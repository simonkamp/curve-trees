#![allow(non_snake_case)]

#[cfg(not(feature = "std"))]
use alloc::{boxed::Box, vec, vec::Vec};

use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::Field;
use ark_std::{One, UniformRand, Zero};
use core::borrow::BorrowMut;
use dock_crypto_utils::ff::powers;
use dock_crypto_utils::transcript::MerlinTranscript;
use rand_core::{CryptoRng, RngCore};
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

use super::constraint_system::{
    ConstraintSystem, RandomizableConstraintSystem, RandomizedConstraintSystem,
};
use super::linear_combination::{LinearCombination, Variable};
use super::proof::R1CSProof;

use crate::errors::R1CSError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof::InnerProductProof;
use crate::r1cs::{committed_t_degrees, degrees, t_poly_degree, Metrics};
use crate::transcript::TranscriptProtocol;

pub const COMMITMENT_LABEL: &[u8; 16] = b"commitment-point";
pub const VEC_COMMITMENT_LABEL: &[u8; 23] = b"vector-commitment-point";

/// A [`ConstraintSystem`] implementation for use by the prover.
///
/// The prover commits high-level variables and their blinding factors `(v, v_blinding)`,
/// allocates low-level variables and creates constraints in terms of these
/// high-level variables and low-level variables.
///
/// When all constraints are added, the proving code calls `prove`
/// which consumes the `Prover` instance, samples random challenges
/// that instantiate the randomized constraints, and creates a complete proof.
pub struct Prover<'g, T: BorrowMut<MerlinTranscript>, C: AffineRepr> {
    transcript: T,
    pc_gens: &'g PedersenGens<C>,
    /// The constraints accumulated so far.
    pub constraints: Vec<LinearCombination<C::ScalarField>>,
    /// Secret data
    pub secrets: Secrets<C::ScalarField>,

    /// This list holds closures that will be called in the second phase of the protocol,
    /// when non-randomized variables are committed.
    deferred_constraints:
        Vec<Box<dyn FnOnce(&mut RandomizingProver<'g, T, C>) -> Result<(), R1CSError>>>,

    /// Index of a pending multiplier that's not fully assigned yet.
    pending_multiplier: Option<usize>,
}

// todo I assume this would be automatically implemented by the compiler if it did not have a a mutable borrow of a transcript
unsafe impl<'g, T: BorrowMut<MerlinTranscript>, C: AffineRepr> Send for Prover<'g, T, C> {} // todo fix after refactor

/// Separate struct to implement Drop trait for (for zeroing),
/// so that compiler does not prohibit us from moving the Transcript out of `prove()`.
#[derive(ZeroizeOnDrop)]
pub struct Secrets<F: Field> {
    /// Stores assignments to the "left" of multiplication gates
    a_L: Vec<F>,
    /// Stores assignments to the "right" of multiplication gates
    a_R: Vec<F>,
    /// Stores assignments to the "output" of multiplication gates
    a_O: Vec<F>,
    /// High-level witness data (blinding, value) openings to V commitments
    v_open: Vec<(F, F)>,
    /// Each item of the vector is pair with first element as the blinding and the next is the vector of elements committed in a Pedersen commitment
    pub vec_open: Vec<(F, Vec<F>)>,
}

/// Prover in the randomizing phase.
///
/// Note: this type is exported because it is used to specify the associated type
/// in the public impl of a trait `ConstraintSystem`, which boils down to allowing compiler to
/// monomorphize the closures for the proving and verifying code.
/// However, this type cannot be instantiated by the user and therefore can only be used within
/// the callback provided to `specify_randomized_constraints`.
pub struct RandomizingProver<'g, T: BorrowMut<MerlinTranscript>, C: AffineRepr> {
    prover: Prover<'g, T, C>,
}

impl<'g, T: BorrowMut<MerlinTranscript>, C: AffineRepr> ConstraintSystem<C::ScalarField>
    for Prover<'g, T, C>
{
    fn transcript(&mut self) -> &mut MerlinTranscript {
        self.transcript.borrow_mut()
    }

    fn multiply(
        &mut self,
        mut left: LinearCombination<C::ScalarField>,
        mut right: LinearCombination<C::ScalarField>,
    ) -> (
        Variable<C::ScalarField>,
        Variable<C::ScalarField>,
        Variable<C::ScalarField>,
    ) {
        // Synthesize the assignments for l,r,o
        let l = self.eval(&left);
        let r = self.eval(&right);
        let o = l * r;

        // Create variables for l,r,o ...
        let l_var = Variable::MultiplierLeft(self.secrets.a_L.len());
        let r_var = Variable::MultiplierRight(self.secrets.a_R.len());
        let o_var = Variable::MultiplierOutput(self.secrets.a_O.len());
        // ... and assign them
        self.secrets.a_L.push(l);
        self.secrets.a_R.push(r);
        self.secrets.a_O.push(o);

        // Constrain l,r,o:
        left.terms.push((l_var, -C::ScalarField::one()));
        right.terms.push((r_var, -C::ScalarField::one()));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate(
        &mut self,
        assignment: Option<C::ScalarField>,
    ) -> Result<Variable<C::ScalarField>, R1CSError> {
        let scalar = assignment.ok_or(R1CSError::MissingAssignment)?;

        match self.pending_multiplier {
            None => {
                let i = self.secrets.a_L.len();
                self.pending_multiplier = Some(i);
                self.secrets.a_L.push(scalar);
                self.secrets.a_R.push(C::ScalarField::zero());
                self.secrets.a_O.push(C::ScalarField::zero());
                Ok(Variable::MultiplierLeft(i))
            }
            Some(i) => {
                self.pending_multiplier = None;
                self.secrets.a_R[i] = scalar;
                self.secrets.a_O[i] = self.secrets.a_L[i] * self.secrets.a_R[i];
                Ok(Variable::MultiplierRight(i))
            }
        }
    }

    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(C::ScalarField, C::ScalarField)>,
    ) -> Result<
        (
            Variable<C::ScalarField>,
            Variable<C::ScalarField>,
            Variable<C::ScalarField>,
        ),
        R1CSError,
    > {
        let (l, r) = input_assignments.ok_or(R1CSError::MissingAssignment)?;
        let o = l * r;

        // Create variables for l,r,o ...
        let l_var = Variable::MultiplierLeft(self.secrets.a_L.len());
        let r_var = Variable::MultiplierRight(self.secrets.a_R.len());
        let o_var = Variable::MultiplierOutput(self.secrets.a_O.len());
        // ... and assign them
        self.secrets.a_L.push(l);
        self.secrets.a_R.push(r);
        self.secrets.a_O.push(o);

        Ok((l_var, r_var, o_var))
    }

    fn metrics(&self) -> Metrics {
        Metrics {
            multipliers: self.secrets.a_L.len(),
            constraints: self.constraints.len() + self.deferred_constraints.len(),
            phase_one_constraints: self.constraints.len(),
            phase_two_constraints: self.deferred_constraints.len(),
        }
    }

    fn constrain(&mut self, lc: LinearCombination<C::ScalarField>) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination evals to 0 for prover, etc).
        self.constraints.push(lc);
    }

    fn evaluate(&self, lc: &LinearCombination<C::ScalarField>) -> Option<C::ScalarField> {
        Some(self.eval(lc))
    }
}

impl<'g, T: BorrowMut<MerlinTranscript>, C: AffineRepr> RandomizableConstraintSystem<C::ScalarField>
    for Prover<'g, T, C>
{
    type RandomizedCS = RandomizingProver<'g, T, C>;

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
    where
        F: 'static + FnOnce(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        self.deferred_constraints.push(Box::new(callback));
        Ok(())
    }
}

impl<'g, T: BorrowMut<MerlinTranscript>, C: AffineRepr> ConstraintSystem<C::ScalarField>
    for RandomizingProver<'g, T, C>
{
    fn transcript(&mut self) -> &mut MerlinTranscript {
        self.prover.transcript.borrow_mut()
    }

    fn multiply(
        &mut self,
        left: LinearCombination<C::ScalarField>,
        right: LinearCombination<C::ScalarField>,
    ) -> (
        Variable<C::ScalarField>,
        Variable<C::ScalarField>,
        Variable<C::ScalarField>,
    ) {
        self.prover.multiply(left, right)
    }

    fn allocate(
        &mut self,
        assignment: Option<C::ScalarField>,
    ) -> Result<Variable<C::ScalarField>, R1CSError> {
        self.prover.allocate(assignment)
    }

    fn allocate_multiplier(
        &mut self,
        input_assignments: Option<(C::ScalarField, C::ScalarField)>,
    ) -> Result<
        (
            Variable<C::ScalarField>,
            Variable<C::ScalarField>,
            Variable<C::ScalarField>,
        ),
        R1CSError,
    > {
        self.prover.allocate_multiplier(input_assignments)
    }

    fn metrics(&self) -> Metrics {
        self.prover.metrics()
    }

    fn constrain(&mut self, lc: LinearCombination<C::ScalarField>) {
        self.prover.constrain(lc)
    }

    fn evaluate(&self, lc: &LinearCombination<C::ScalarField>) -> Option<C::ScalarField> {
        Some(self.prover.eval(lc))
    }
}

impl<'g, T: BorrowMut<MerlinTranscript>, C: AffineRepr> RandomizedConstraintSystem<C::ScalarField>
    for RandomizingProver<'g, T, C>
{
    fn challenge_scalar(&mut self, label: &'static [u8]) -> C::ScalarField {
        let t = self.prover.transcript.borrow_mut();
        TranscriptProtocol::challenge_scalar::<C>(t, label)
    }
}

impl<'g, T: BorrowMut<MerlinTranscript>, C: AffineRepr> Prover<'g, T, C> {
    /// Construct an empty constraint system with specified external
    /// input variables.
    ///
    /// # Inputs
    ///
    /// The `bp_gens` and `pc_gens` are generators for Bulletproofs
    /// and for the Pedersen commitments, respectively.  The
    /// [`BulletproofGens`] should have `gens_capacity` greater than
    /// the number of multiplication constraints that will eventually
    /// be added into the constraint system.
    ///
    /// The `transcript` parameter is a Merlin proof transcript.  The
    /// `ProverCS` holds onto the `&mut MerlinTranscript` until it consumes
    /// itself during [`ProverCS::prove`], releasing its borrow of the
    /// transcript.  This ensures that the transcript cannot be
    /// altered except by the `ProverCS` before proving is complete.
    ///
    /// # Returns
    ///
    /// Returns a new `Prover` instance.
    pub fn new(pc_gens: &'g PedersenGens<C>, mut transcript: T) -> Self {
        transcript.borrow_mut().r1cs_domain_sep();

        Prover {
            pc_gens,
            transcript,
            secrets: Secrets {
                v_open: Vec::new(),
                a_L: Vec::new(),
                a_R: Vec::new(),
                a_O: Vec::new(),
                vec_open: Vec::new(),
            },
            constraints: Vec::new(),
            deferred_constraints: Vec::new(),
            pending_multiplier: None,
        }
    }

    /// Creates commitment to a high-level variable and adds it to the transcript.
    ///
    /// # Inputs
    ///
    /// The `v` and `v_blinding` parameters are openings to the
    /// commitment to the external variable for the constraint
    /// system.  Passing the opening (the value together with the
    /// blinding factor) makes it possible to reference pre-existing
    /// commitments in the constraint system.  All external variables
    /// must be passed up-front, so that challenges produced by
    /// [`ConstraintSystem::challenge_scalar`] are bound to the
    /// external variables.
    ///
    /// # Returns
    ///
    /// Returns a pair of a Pedersen commitment (as a compressed Ristretto point),
    /// and a [`Variable`] corresponding to it, which can be used to form constraints.
    pub fn commit(
        &mut self,
        v: C::ScalarField,
        v_blinding: C::ScalarField,
    ) -> (C, Variable<C::ScalarField>) {
        let i = self.secrets.v_open.len();
        self.secrets.v_open.push((v_blinding, v));

        // Add the commitment to the transcript.
        let V = self.pc_gens.commit(v, v_blinding);
        self.transcript
            .borrow_mut()
            .append_point(COMMITMENT_LABEL, &V);

        (V, Variable::Committed(i))
    }

    /// Commit all values of `v` in a single Pedersen commitment. Returns the commitment and a list of variables, one for each of the values in `v`
    pub fn commit_vec(
        &mut self,
        v: &[C::ScalarField],
        v_blinding: C::ScalarField,
        bp_gens: &BulletproofGens<C>, // same as used during proving, uses the "G" generators to commit like for a_O
    ) -> (C, Vec<Variable<C::ScalarField>>) {
        use core::iter;

        // compute the commitment:
        // comm = <v, G> + v_blinding * B_blinding
        let gens = bp_gens.share(0);

        // [b] * H + [v_1] * G1 + ... + [v_n] * Gn
        let generators: Vec<_> = iter::once(&self.pc_gens.B_blinding)
            .chain(gens.G(v.len() as u32))
            .copied()
            .collect::<Vec<_>>();

        let scalars: Zeroizing<Vec<C::ScalarField>> =
            Zeroizing::new(iter::once(&v_blinding).chain(v.iter()).copied().collect());

        assert_eq!(generators.len(), scalars.len());

        let comm = C::Group::msm_unchecked(generators.as_slice(), scalars.as_slice()).into_affine();

        let vars = self.vars_for_committed_vec(&comm, v, v_blinding);

        (comm, vars)
    }

    /// Returns variables for the values in `v` and blinding `v_blinding` which were committed inside the commitment `comm`  
    pub fn vars_for_committed_vec(
        &mut self,
        comm: &C,
        v: &[C::ScalarField],
        v_blinding: C::ScalarField,
    ) -> Vec<Variable<C::ScalarField>> {
        // create variables for all the addressable coordinates
        let comm_idx = self.secrets.vec_open.len();
        let vars = (0..v.len())
            .map(|i| Variable::VectorCommit(comm_idx, i))
            .collect();

        // add the opening (values || blinding) to the secrets
        self.secrets
            .vec_open
            .push((v_blinding, committed_vec_opening(v)));

        // add the commitment to the transcript.
        self.transcript
            .borrow_mut()
            .append_point(VEC_COMMITMENT_LABEL, comm);
        vars
    }

    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    fn flattened_constraints(
        &mut self,
        z: &C::ScalarField,
    ) -> (
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
        Vec<Vec<C::ScalarField>>,
    ) {
        let n = self.secrets.a_L.len();
        let m = self.secrets.v_open.len();

        let mut wL = vec![C::ScalarField::zero(); n];
        let mut wR = vec![C::ScalarField::zero(); n];
        let mut wO = vec![C::ScalarField::zero(); n];
        let mut wV = vec![C::ScalarField::zero(); m];

        let mut wVCs = Vec::with_capacity(self.secrets.vec_open.len());
        for v in self.secrets.vec_open.iter() {
            wVCs.push(vec![C::ScalarField::zero(); v.1.len()]);
        }

        let mut exp_z = *z;
        for lc in self.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var {
                    Variable::MultiplierLeft(i) => {
                        wL[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierRight(i) => {
                        wR[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierOutput(i) => {
                        wO[*i] += exp_z * coeff;
                    }
                    Variable::Committed(i) => {
                        wV[*i] -= exp_z * coeff;
                    }
                    Variable::VectorCommit(j, i) => {
                        // j : index of commitment
                        // i : coordinate with-in commitment
                        wVCs[*j][*i] += exp_z * coeff;
                    }
                    Variable::One(_) => {
                        // The prover doesn't need to handle constant terms
                    }
                }
            }
            exp_z *= z;
        }

        (wL, wR, wO, wV, wVCs)
    }

    /// Returns the secret value of the linear combination.
    pub fn eval(&self, lc: &LinearCombination<C::ScalarField>) -> C::ScalarField {
        lc.terms
            .iter()
            .map(|(var, coeff)| {
                *coeff
                    * match var {
                        Variable::VectorCommit(j, i) => self.secrets.vec_open[*j].1[*i], // lookup in vector commitment
                        Variable::MultiplierLeft(i) => self.secrets.a_L[*i],
                        Variable::MultiplierRight(i) => self.secrets.a_R[*i],
                        Variable::MultiplierOutput(i) => self.secrets.a_O[*i],
                        Variable::Committed(i) => self.secrets.v_open[*i].1,
                        Variable::One(_) => C::ScalarField::one(),
                    }
            })
            .sum()
    }

    /// Calls all remembered callbacks with an API that
    /// allows generating challenge scalars.
    fn create_randomized_constraints(mut self) -> Result<Self, R1CSError> {
        // Clear the pending multiplier (if any) because it was committed into A_L/A_R/S.
        self.pending_multiplier = None;

        if self.deferred_constraints.is_empty() {
            self.transcript.borrow_mut().r1cs_1phase_domain_sep();
            Ok(self)
        } else {
            self.transcript.borrow_mut().r1cs_2phase_domain_sep();
            // Note: the wrapper could've used &mut instead of ownership,
            // but specifying lifetimes for boxed closures is not going to be nice,
            // so we move the self into wrapper and then move it back out afterwards.
            let mut callbacks = core::mem::take(&mut self.deferred_constraints);
            let mut wrapped_self = RandomizingProver { prover: self };
            for callback in callbacks.drain(..) {
                callback(&mut wrapped_self)?;
            }
            Ok(wrapped_self.prover)
        }
    }

    /// Consume this `ConstraintSystem` to produce a proof.
    #[cfg(feature = "std")]
    pub fn prove(self, bp_gens: &BulletproofGens<C>) -> Result<R1CSProof<C>, R1CSError> {
        let mut rng = rand::thread_rng();
        self.prove_with_rng(bp_gens, &mut rng)
    }

    pub fn prove_with_rng<R: RngCore + CryptoRng>(
        self,
        bp_gens: &BulletproofGens<C>,
        rng: &mut R,
    ) -> Result<R1CSProof<C>, R1CSError> {
        self.prove_and_return_transcript_with_rng(bp_gens, rng)
            .map(|(proof, _transcript)| proof)
    }

    pub fn size(&self) -> u32 {
        let mut n = self.secrets.a_L.len();
        for (_, v) in self.secrets.vec_open.iter() {
            n = core::cmp::max(n, committed_vec_dimension(v));
        }
        n as u32
    }

    /// The number of multiply gates allocated so far
    pub fn num_multipliers(&self) -> usize {
        self.secrets.a_L.len()
    }

    /// Consume this `ConstraintSystem` to produce a proof. Returns the proof and the transcript passed in `Prover::new`.
    #[cfg(feature = "std")]
    pub fn prove_and_return_transcript(
        self,
        bp_gens: &BulletproofGens<C>,
    ) -> Result<(R1CSProof<C>, T), R1CSError> {
        let mut rng = rand::thread_rng();
        self.prove_and_return_transcript_with_rng(bp_gens, &mut rng)
    }

    /// Consume this `ConstraintSystem` to produce a proof. Returns the proof and the transcript passed in `Prover::new`.
    pub fn prove_and_return_transcript_with_rng<R: RngCore + CryptoRng>(
        mut self,
        bp_gens: &BulletproofGens<C>,
        rng: &mut R,
    ) -> Result<(R1CSProof<C>, T), R1CSError> {
        // pad
        let size = self.size();
        while size > self.secrets.a_L.len() as u32 {
            self.allocate_multiplier(Some((C::ScalarField::zero(), C::ScalarField::zero())))?;
        }

        use crate::util;
        use core::iter;

        // number of vector commitments
        let ncomm = self.secrets.vec_open.len();

        let (l_r_degrees, inner_product_degree) = degrees(ncomm);
        let vec_com_degrees = &l_r_degrees[2..];

        #[cfg(debug_assertions)]
        {
            log::debug!("inner_product_degree: {}", inner_product_degree);
            log::debug!("number of commitments: {}", ncomm);
            log::debug!("number of constraints: {}", self.secrets.a_L.len());
            log::debug!("degrees = {:?}", &l_r_degrees[..]);
        }

        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        self.transcript
            .borrow_mut()
            .merlin
            .append_u64(b"m", self.secrets.v_open.len() as u64);
        self.transcript
            .borrow_mut()
            .merlin
            .append_u64(b"c", self.secrets.vec_open.len() as u64);
        for i in 0..self.secrets.vec_open.len() {
            self.transcript.borrow_mut().merlin.append_u64(
                b"c_i",
                committed_vec_dimension(&self.secrets.vec_open[i].1) as u64,
            );
        }

        // // Create a `TranscriptRng` from the high-level witness data
        // //
        // // The prover wants to rekey the RNG with its witness data.
        // //
        // // This consists of the high level witness data (the v's and
        // // v_blinding's), as well as the low-level witness data (a_L,
        // // a_R, a_O).  Since the low-level data should (hopefully) be
        // // determined by the high-level data, it doesn't give any
        // // extra entropy for reseeding the RNG.
        // //
        // // Since the v_blindings should be random scalars (in order to
        // // protect the v's in the commitments), we don't gain much by
        // // committing the v's as well as the v_blinding's.
        // let mut rng = {
        //     let mut builder = self.transcript.borrow_mut().build_rng();

        //     // Commit the blinding factors for the input wires
        //     for (v_b, _) in &self.secrets.v {
        //         builder = builder.rekey_with_witness_bytes(b"v_blinding", &util::field_as_bytes(v_b));
        //     }

        //     use rand::thread_rng;
        //     builder.finalize(&mut thread_rng())
        // };

        // Commit to the first-phase low-level witness variables.
        let n1 = self.size();

        if bp_gens.gens_capacity < n1 {
            return Err(R1CSError::InvalidGeneratorsLength(
                bp_gens.gens_capacity,
                n1,
            ));
        }

        // We are performing a single-party circuit proof, so party index is 0.
        let gens = bp_gens.share(0);

        let mut i_blinding1 = C::ScalarField::rand(rng);
        let mut o_blinding1 = C::ScalarField::rand(rng);
        let mut s_blinding1 = C::ScalarField::rand(rng);

        let s_L1: Zeroizing<Vec<C::ScalarField>> =
            Zeroizing::new((0..n1).map(|_| C::ScalarField::rand(rng)).collect());
        let s_R1: Zeroizing<Vec<C::ScalarField>> =
            Zeroizing::new((0..n1).map(|_| C::ScalarField::rand(rng)).collect());

        #[cfg(feature = "parallel")]
        let (A_I1, A_O1, S1) = {
            // todo clean up when send is safely implemented
            let blinding = self.pc_gens.B_blinding;
            let A_I1_scalars = Zeroizing::new(
                iter::once(&i_blinding1)
                    .chain(self.secrets.a_L.iter())
                    .chain(self.secrets.a_R.iter())
                    .copied()
                    .collect::<Vec<C::ScalarField>>(),
            );
            let A_O1_scalars = Zeroizing::new(
                iter::once(&o_blinding1)
                    .chain(self.secrets.a_O.iter())
                    .copied()
                    .collect::<Vec<C::ScalarField>>(),
            );
            let (mut A_I1, mut A_O1, mut S1) = (None, None, None);
            rayon::scope(|s| {
                // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
                s.spawn(|_| {
                    A_I1 = Some(
                        C::Group::msm_unchecked(
                            iter::once(&blinding)
                                .chain(gens.G(n1))
                                .chain(gens.H(n1))
                                .copied()
                                .collect::<Vec<C>>()
                                .as_slice(),
                            A_I1_scalars.as_slice(),
                        )
                        .into(),
                    )
                });
                // A_O = <a_O, G> + o_blinding * B_blinding
                s.spawn(|_| {
                    A_O1 = Some(
                        C::Group::msm_unchecked(
                            iter::once(&blinding)
                                .chain(gens.G(n1))
                                .copied()
                                .collect::<Vec<C>>()
                                .as_slice(),
                            A_O1_scalars.as_slice(),
                        )
                        .into(),
                    )
                });

                // Vector commitments of the form
                // <Vi, G> + vi_blinding * B:blinding

                // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
                s.spawn(|_| {
                    let S1_scalars = Zeroizing::new(
                        iter::once(&s_blinding1)
                            .chain(s_L1.iter())
                            .chain(s_R1.iter())
                            .copied()
                            .collect::<Vec<C::ScalarField>>(),
                    );
                    S1 = Some(
                        C::Group::msm_unchecked_full_width(
                            iter::once(&blinding)
                                .chain(gens.G(n1))
                                .chain(gens.H(n1))
                                .copied()
                                .collect::<Vec<C>>()
                                .as_slice(),
                            S1_scalars.as_slice(),
                        )
                        .into(),
                    )
                });
            });

            match (A_I1, A_O1, S1) {
                (Some(A_I1), Some(A_O1), Some(S1)) => (A_I1, A_O1, S1),
                _ => {
                    return Err(R1CSError::GadgetError {
                        description: "Failed to compute commitments".into(),
                    })
                }
            }
        };
        #[cfg(not(feature = "parallel"))]
        let (A_I1, A_O1, S1) = {
            // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
            let A_I1_scalars = Zeroizing::new(
                iter::once(&i_blinding1)
                    .chain(self.secrets.a_L.iter())
                    .chain(self.secrets.a_R.iter())
                    .map(|s| (*s).into())
                    .collect::<Vec<C::ScalarField>>(),
            );
            let A_I1 = C::Group::msm_unchecked(
                iter::once(&self.pc_gens.B_blinding)
                    .chain(gens.G(n1))
                    .chain(gens.H(n1))
                    .copied()
                    .collect::<Vec<C>>()
                    .as_slice(),
                A_I1_scalars.as_slice(),
            )
            .into();

            // A_O = <a_O, G> + o_blinding * B_blinding
            let A_O1_scalars = Zeroizing::new(
                iter::once(&o_blinding1)
                    .chain(self.secrets.a_O.iter())
                    .map(|s| (*s).into())
                    .collect::<Vec<C::ScalarField>>(),
            );
            let A_O1 = C::Group::msm_unchecked(
                iter::once(&self.pc_gens.B_blinding)
                    .chain(gens.G(n1))
                    .copied()
                    .collect::<Vec<C>>()
                    .as_slice(),
                A_O1_scalars.as_slice(),
            )
            .into();

            // Vector commitments of the form
            // <Vi, G> + vi_blinding * B:blinding

            // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
            let S1_scalars = Zeroizing::new(
                iter::once(&s_blinding1)
                    .chain(s_L1.iter())
                    .chain(s_R1.iter())
                    .map(|s| (*s).into())
                    .collect::<Vec<C::ScalarField>>(),
            );
            let S1 = C::Group::msm_unchecked_full_width(
                iter::once(&self.pc_gens.B_blinding)
                    .chain(gens.G(n1))
                    .chain(gens.H(n1))
                    .copied()
                    .collect::<Vec<C>>()
                    .as_slice(),
                S1_scalars.as_slice(),
            )
            .into();
            (A_I1, A_O1, S1)
        };

        let transcript = self.transcript.borrow_mut();
        transcript.append_point(b"A_I1", &A_I1);
        transcript.append_point(b"A_O1", &A_O1);
        transcript.append_point(b"S1", &S1);

        // Process the remaining constraints.
        self = self.create_randomized_constraints()?;

        // Pad zeros to the next power of two (or do that implicitly when creating vectors)

        // If the number of multiplications is not 0 or a power of 2, then pad the circuit.
        let n = self.size();
        let n2 = n - n1;
        let padded_n = n.next_power_of_two();
        let pad = padded_n - n;

        if bp_gens.gens_capacity < padded_n {
            return Err(R1CSError::InvalidGeneratorsLength(
                bp_gens.gens_capacity,
                padded_n,
            ));
        }

        // Commit to the second-phase low-level witness variables

        let has_2nd_phase_commitments = n2 > 0;

        let (mut i_blinding2, mut o_blinding2, mut s_blinding2) = if has_2nd_phase_commitments {
            (
                C::ScalarField::rand(rng),
                C::ScalarField::rand(rng),
                C::ScalarField::rand(rng),
            )
        } else {
            (
                C::ScalarField::zero(),
                C::ScalarField::zero(),
                C::ScalarField::zero(),
            )
        };

        let s_L2: Zeroizing<Vec<C::ScalarField>> =
            Zeroizing::new((0..n2).map(|_| C::ScalarField::rand(rng)).collect());
        let s_R2: Zeroizing<Vec<C::ScalarField>> =
            Zeroizing::new((0..n2).map(|_| C::ScalarField::rand(rng)).collect());

        #[cfg(feature = "parallel")]
        let (A_I2, A_O2, S2) = if has_2nd_phase_commitments {
            // todo clean up when send is safely implemented
            let blinding = self.pc_gens.B_blinding;
            let A_I2_scalars = Zeroizing::new(
                iter::once(&i_blinding2)
                    .chain(self.secrets.a_L.iter().skip(n1 as usize))
                    .chain(self.secrets.a_R.iter().skip(n1 as usize))
                    .copied()
                    .collect::<Vec<C::ScalarField>>(),
            );
            let A_O2_scalars = Zeroizing::new(
                iter::once(&o_blinding2)
                    .chain(self.secrets.a_O.iter().skip(n1 as usize))
                    .copied()
                    .collect::<Vec<C::ScalarField>>(),
            );
            let S2_scalars = Zeroizing::new(
                iter::once(&s_blinding2)
                    .chain(s_L2.iter())
                    .chain(s_R2.iter())
                    .copied()
                    .collect::<Vec<C::ScalarField>>(),
            );
            let (mut A_I2, mut A_O2, mut S2) = (None, None, None);
            rayon::scope(|s| {
                // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
                s.spawn(|_| {
                    A_I2 = Some(
                        C::Group::msm_unchecked(
                            iter::once(&blinding)
                                .chain(gens.G(n).skip(n1 as usize))
                                .chain(gens.H(n).skip(n1 as usize))
                                .copied()
                                .collect::<Vec<C>>()
                                .as_slice(),
                            A_I2_scalars.as_slice(),
                        )
                        .into(),
                    )
                });
                // A_O = <a_O, G> + o_blinding * B_blinding
                s.spawn(|_| {
                    A_O2 = Some(
                        C::Group::msm_unchecked(
                            iter::once(&blinding)
                                .chain(gens.G(n).skip(n1 as usize))
                                .copied()
                                .collect::<Vec<C>>()
                                .as_slice(),
                            A_O2_scalars.as_slice(),
                        )
                        .into(),
                    )
                });
                // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
                s.spawn(|_| {
                    S2 = Some(
                        C::Group::msm_unchecked_full_width(
                            iter::once(&blinding)
                                .chain(gens.G(n).skip(n1 as usize))
                                .chain(gens.H(n).skip(n1 as usize))
                                .copied()
                                .collect::<Vec<C>>()
                                .as_slice(),
                            S2_scalars.as_slice(),
                        )
                        .into(),
                    )
                });
            });

            match (A_I2, A_O2, S2) {
                (Some(A_I2), Some(A_O2), Some(S2)) => (A_I2, A_O2, S2),
                _ => {
                    return Err(R1CSError::GadgetError {
                        description: "Failed to compute commitments".into(),
                    })
                }
            }
        } else {
            // Since we are using zero blinding factors and
            // there are no variables to commit,
            // the commitments _must_ be identity points,
            // so we can hardcode them saving 3 mults+compressions.
            (C::zero(), C::zero(), C::zero())
        };
        #[cfg(not(feature = "parallel"))]
        let (A_I2, A_O2, S2) = if has_2nd_phase_commitments {
            let A_I2_scalars = Zeroizing::new(
                iter::once(&i_blinding2)
                    .chain(self.secrets.a_L.iter().skip(n1 as usize))
                    .chain(self.secrets.a_R.iter().skip(n1 as usize))
                    .copied()
                    .collect::<Vec<C::ScalarField>>(),
            );
            let A_O2_scalars = Zeroizing::new(
                iter::once(&o_blinding2)
                    .chain(self.secrets.a_O.iter().skip(n1 as usize))
                    .copied()
                    .collect::<Vec<C::ScalarField>>(),
            );
            let S2_scalars = Zeroizing::new(
                iter::once(&s_blinding2)
                    .chain(s_L2.iter())
                    .chain(s_R2.iter())
                    .copied()
                    .collect::<Vec<C::ScalarField>>(),
            );
            (
                // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
                C::Group::msm_unchecked(
                    iter::once(&self.pc_gens.B_blinding)
                        .chain(gens.G(n).skip(n1 as usize))
                        .chain(gens.H(n).skip(n1 as usize))
                        .copied()
                        .collect::<Vec<C>>()
                        .as_slice(),
                    A_I2_scalars.as_slice(),
                )
                .into(),
                // A_O = <a_O, G> + o_blinding * B_blinding
                C::Group::msm_unchecked(
                    iter::once(&self.pc_gens.B_blinding)
                        .chain(gens.G(n).skip(n1 as usize))
                        .copied()
                        .collect::<Vec<C>>()
                        .as_slice(),
                    A_O2_scalars.as_slice(),
                )
                .into(),
                // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
                C::Group::msm_unchecked_full_width(
                    iter::once(&self.pc_gens.B_blinding)
                        .chain(gens.G(n).skip(n1 as usize))
                        .chain(gens.H(n).skip(n1 as usize))
                        .copied()
                        .collect::<Vec<C>>()
                        .as_slice(),
                    S2_scalars.as_slice(),
                )
                .into(),
            )
        } else {
            // Since we are using zero blinding factors and
            // there are no variables to commit,
            // the commitments _must_ be identity points,
            // so we can hardcode them saving 3 mults+compressions.
            (C::zero(), C::zero(), C::zero())
        };

        let transcript = self.transcript.borrow_mut();
        transcript.append_point(b"A_I2", &A_I2);
        transcript.append_point(b"A_O2", &A_O2);
        transcript.append_point(b"S2", &S2);

        // 4. Compute blinded vector polynomials l(x) and r(x)

        let y = TranscriptProtocol::challenge_scalar::<C>(transcript, b"y");
        let z = TranscriptProtocol::challenge_scalar::<C>(transcript, b"z");

        // log::debug!("P A_I2 {}", &A_I2);
        // log::debug!("P A_O2 {}", &A_O2);
        // log::debug!("P S2 {}", &S2);
        // log::debug!("P z {}", z);

        let (wL, wR, wO, wV, wVCs) = self.flattened_constraints(&z);

        // #[cfg(debug_assertions)]
        // {
        //     log::debug!("Length of constraints vector: {}", self.constraints.len());
        //     log::debug!("prover wVCs = {:?}", &wVCs);
        //     log::debug!("prover wL = {:?}", &wL);
        //     log::debug!("prover wR = {:?}", &wR);
        //     log::debug!("prover wO = {:?}", &wO);
        // }

        let mut l_poly =
            util::VecPoly::<C::ScalarField>::zero(n as usize, inner_product_degree + 1);
        let mut r_poly =
            util::VecPoly::<C::ScalarField>::zero(n as usize, inner_product_degree + 1);

        let y_inv = y.inverse().ok_or_else(|| R1CSError::GadgetError {
            description: "y must be non-zero".into(),
        })?;

        let exp_y_inv = powers(&y_inv, padded_n);
        let exp_y = powers(&y, padded_n);

        //
        let sLsR = s_L1
            .iter()
            .chain(s_L2.iter())
            .zip(s_R1.iter().chain(s_R2.iter()));

        debug_assert_eq!(inner_product_degree % 2, 0, "op_degree must be even");

        let mid_degree = inner_product_degree / 2;
        debug_assert_eq!(1 + ncomm, mid_degree);
        debug_assert_eq!(l_r_degrees[0].0, mid_degree);
        debug_assert_eq!(l_r_degrees[0].1, mid_degree);
        debug_assert_eq!(l_r_degrees[1].0, inner_product_degree);
        debug_assert_eq!(l_r_degrees[1].1, 0);

        // The fixed generalized Bulletproofs uses op_degree = 2 * ncomm + 2.
        // The prefix of op_splits(op_degree) that we actually use is then:
        //   (mid, mid), (op_degree, 0), (op_degree - 1, 1), (op_degree - 2, 2), ...
        // so veccom_ops[j] places vector commitment j at (op_degree - (j + 1), j + 1).
        // This leaves all left coefficients below mid equal to zero, matching Table 2.
        //
        // 0 commitments => op_degree = 2, mid = 1
        //
        // Left:
        // 0 : -
        // 1 : aL + y^-n o wR
        // 2 : aO
        // 3 : sL
        //
        // Right:
        // 0 : wO - y^n
        // 1 : y^n o aR + wL
        // 2 : -
        // 3 : y^n o sR
        //
        // 1 commitment => op_degree = 4, mid = 2
        //
        // Left:
        // 0 : -
        // 1 : -
        // 2 : aL + y^-n o wR
        // 3 : com1
        // 4 : aO
        // 5 : sL
        //
        // Right:
        // 0 : wO - y^n
        // 1 : Wc1
        // 2 : y^n o aR + wL
        // 3 : -
        // 4 : -
        // 5 : y^n o sR
        //
        // 2 commitments => op_degree = 6, mid = 3
        //
        // Left:
        // 0 : -
        // 1 : -
        // 2 : -
        // 3 : aL + y^-n o wR
        // 4 : com2
        // 5 : com1
        // 6 : aO
        // 7 : sL
        //
        // Right:
        // 0 : wO - y^n
        // 1 : Wc1
        // 2 : Wc2
        // 3 : y^n o aR + wL
        // 4 : -
        // 5 : -
        // 6 : -
        // 7 : y^n o sR
        //
        // 3 commitments => op_degree = 8, mid = 4
        //
        // Left:
        // 0 : -
        // 1 : -
        // 2 : -
        // 3 : -
        // 4 : aL + y^-n o wR
        // 5 : com3
        // 6 : com2
        // 7 : com1
        // 8 : aO
        // 9 : sL
        //
        // Right:
        // 0 : wO - y^n
        // 1 : Wc1
        // 2 : Wc2
        // 3 : Wc3
        // 4 : y^n o aR + wL
        // 5 : -
        // 6 : -
        // 7 : -
        // 8 : -
        // 9 : y^n o sR
        //
        // In the fixed bulletproofs draft, the high right slots paired with committed vectors would also
        // contain `y o c_{k,R}`. But we don't have `c_{k,R}` like Monero so leave those slots as zero.

        for (i, (sl, sr)) in sLsR.enumerate() {
            debug_assert!(i < self.secrets.a_L.len());

            // a_L and a_R constraints:
            // Set both to mid_degree so that the product of these end up at inner_product_degree
            // l_poly.mid_degree = a_L + y^-n * (z * z^Q * W_R)
            // r_poly.mid_degree = y^n * a_R + (z * z^Q * W_L)
            l_poly.coeff_mut(mid_degree)[i] = self.secrets.a_L[i] + exp_y_inv[i] * wR[i];
            r_poly.coeff_mut(mid_degree)[i] = exp_y[i] * self.secrets.a_R[i] + wL[i];

            // a_O constraints:
            // Set these to inner_product_degree and 0 so that the product of these end up at inner_product_degree
            // l_poly.inner_product_degree = a_O
            // r_poly.0 = (z * z^Q * W_O) - y^n
            l_poly.coeff_mut(inner_product_degree)[i] = self.secrets.a_O[i];
            r_poly.coeff_mut(0)[i] = wO[i] - exp_y[i];

            // masks:
            // Set both to inner_product_degree + 1 so that the product of these end up beyond inner_product_degree
            // l_poly.(inner_product_degree+1) = s_L (mask)
            l_poly.coeff_mut(inner_product_degree + 1)[i] = *sl;
            r_poly.coeff_mut(inner_product_degree + 1)[i] = exp_y[i] * sr;
        }

        // veccom constraints
        for (j, w) in self.secrets.vec_open.iter().enumerate() {
            //
            let (l_deg, r_deg) = vec_com_degrees[j];

            // copy values to l_poly r_poly
            for i in 0..w.1.len() {
                debug_assert_eq!(l_poly.coeff(l_deg)[i], C::ScalarField::zero());
                debug_assert_eq!(r_poly.coeff(r_deg)[i], C::ScalarField::zero());
                l_poly.coeff_mut(l_deg)[i] = w.1[i];
                r_poly.coeff_mut(r_deg)[i] = wVCs[j][i];
            }
        }

        let mut t_poly = util::VecPoly::special_product(&l_poly, &r_poly, mid_degree);
        debug_assert_eq!(t_poly.deg(), t_poly_degree(inner_product_degree));

        // As per fixed bulletproofs draft, every omitted low-degree coefficient of t(X) is zero because
        // l_poly has no support below mid_degree. The omitted coefficient at op_degree is not
        // zero, it is the synthetic target coefficient reconstructed from the public commitments.
        #[cfg(debug_assertions)]
        for d in 0..mid_degree {
            debug_assert_eq!(
                t_poly.coeff()[d],
                C::ScalarField::zero(),
                "t_poly coefficient below mid should be zero"
            );
        }

        // commit to coefficients of t-poly

        // create blinding poly for t-poly
        let mut t_blinding_poly = util::Poly::zero(t_poly.deg());
        let comm_t_deg = committed_t_degrees(inner_product_degree);
        let mut T = Vec::with_capacity(comm_t_deg.len());

        // Since the terms we care about are coefficient of degree `op_degree` in `t_poly`
        // and we already have commitments to it, no need of committing here.
        t_blinding_poly.coeff_mut()[inner_product_degree] = wV
            .iter()
            .zip(self.secrets.v_open.iter())
            .map(|(c, (v_blinding, _))| *c * v_blinding)
            .sum();

        let transcript = self.transcript.borrow_mut();
        for d in comm_t_deg {
            let b = C::ScalarField::rand(rng);
            let T_d = self.pc_gens.commit(t_poly.coeff_mut()[d], b);
            t_blinding_poly.coeff_mut()[d] = b;
            transcript.append_index(b"t_poly degree", d as u64);
            transcript.append_point(b"t_poly", &T_d);
            T.push(T_d);
        }

        let u = TranscriptProtocol::challenge_scalar::<C>(transcript, b"u");
        let x = TranscriptProtocol::challenge_scalar::<C>(transcript, b"x");

        // #[cfg(debug_assertions)]
        // println!("prover: x = {}", x);

        // Optimz: If large number of veccoms, precomputing powers of x once can help a bit

        let t_x = t_poly.eval(x);
        let t_x_blinding = t_blinding_poly.eval(x);

        // The constant term of l is zero, hence l_vec is zero beyond n. Reserve `pad` trailing
        // slots up front so the `append` does not reallocate.
        let mut l_vec = l_poly.eval(x, pad as usize);
        l_vec.append(&mut vec![C::ScalarField::zero(); pad as usize]);

        // XXX this should refer to the notes to explain why this is correct
        // This is the constant term of r(x) beyond w_O since it is zero after n.
        let mut r_vec = r_poly.eval(x, pad as usize);
        r_vec.append(&mut vec![C::ScalarField::zero(); pad as usize]);
        for i in n..padded_n {
            r_vec[i as usize] = -exp_y[i as usize];
        }

        // sanity check
        #[cfg(debug_assertions)]
        {
            let y_inv = y.inverse().ok_or_else(|| R1CSError::GadgetError {
                description: "y must be non-zero".into(),
            })?;
            let y_inv_vec = powers(&y_inv, padded_n);

            let yneg_wR = wR
                .iter()
                .zip(y_inv_vec.iter())
                .map(|(wRi, exp_y_inv)| (*wRi) * exp_y_inv)
                .chain(iter::repeat(C::ScalarField::zero()).take((padded_n - n) as usize))
                .collect::<Vec<C::ScalarField>>();

            let delta = C::ScalarField::inner_product(&yneg_wR[0..n as usize], &wL);

            let yn: Vec<_> = powers(&y, n);
            let mut aRyn = vec![C::ScalarField::zero(); n as usize];
            for i in 0..n {
                aRyn[i as usize] = self.secrets.a_R[i as usize] * yn[i as usize];
            }

            let mut t2 = C::ScalarField::zero();

            // linear term
            t2 += C::ScalarField::inner_product(&wL, &self.secrets.a_L);
            t2 += C::ScalarField::inner_product(&wR, &self.secrets.a_R);
            t2 += C::ScalarField::inner_product(&wO, &self.secrets.a_O);

            for i in 0..self.secrets.vec_open.len() {
                t2 += C::ScalarField::inner_product(&wVCs[i], &self.secrets.vec_open[i].1);
            }

            // product
            t2 += C::ScalarField::inner_product(&self.secrets.a_L, &aRyn);
            t2 -= C::ScalarField::inner_product(&self.secrets.a_O, &yn);

            // publicly computable correction
            t2 += delta;

            assert_eq!(
                t_poly.coeff_mut()[inner_product_degree],
                t2,
                "t_poly term check failed"
            );
            log::debug!("sanity check passed");
        }

        let mut i_blinding = i_blinding1 + u * i_blinding2;
        let mut o_blinding = o_blinding1 + u * o_blinding2;
        let mut s_blinding = s_blinding1 + u * s_blinding2;

        i_blinding1.zeroize();
        o_blinding1.zeroize();
        s_blinding1.zeroize();
        i_blinding2.zeroize();
        o_blinding2.zeroize();
        s_blinding2.zeroize();

        //
        let mut e_terms: Vec<Option<C::ScalarField>> = vec![None; l_poly.deg() + 1];

        // special
        e_terms[l_r_degrees[0].0] = Some(i_blinding); // aL || aR
        e_terms[l_r_degrees[1].0] = Some(o_blinding); // aO

        // veccom
        for j in 0..ncomm {
            debug_assert!(e_terms[vec_com_degrees[j].0].is_none());
            e_terms[vec_com_degrees[j].0] = Some(self.secrets.vec_open[j].0);
        }

        // blinding
        e_terms[inner_product_degree + 1] = Some(s_blinding); // sL || sR

        // #[cfg(debug_assertions)]
        // {
        //     for (i, e) in e_terms.iter().enumerate() {
        //         log::debug!("e_terms, x^{} = {:?}", i, e);
        //     }
        // }

        // evaluate blinding, e_blinding = <e_terms, [1, x, x^2, ...]>
        let mut e_blinding = C::ScalarField::zero();
        {
            let mut xn = C::ScalarField::one();
            for bnd in e_terms.iter() {
                if let Some(val) = bnd {
                    e_blinding += xn * *val;
                }
                xn *= x;
            }
        }
        e_terms.zeroize();
        i_blinding.zeroize();
        o_blinding.zeroize();
        s_blinding.zeroize();

        transcript.append_scalar::<C>(b"t_x", &t_x);
        transcript.append_scalar::<C>(b"t_x_blinding", &t_x_blinding);
        transcript.append_scalar::<C>(b"e_blinding", &e_blinding);

        // Get a challenge value to combine statements for the IPP
        let w = TranscriptProtocol::challenge_scalar::<C>(transcript, b"w");
        let Q = self.pc_gens.B.mul(w).into();

        let G_factors = iter::repeat(C::ScalarField::one())
            .take(n1 as usize)
            .chain(iter::repeat(u).take((n2 + pad) as usize))
            .collect::<Vec<_>>();

        let H_factors = exp_y_inv
            .into_iter()
            .zip(G_factors.iter())
            .map(|(y_inv, u_or_1)| y_inv * u_or_1)
            .collect::<Vec<_>>();

        let ipp_proof = InnerProductProof::create(
            transcript,
            &Q,
            &G_factors,
            &H_factors,
            gens.G(padded_n).copied().collect(),
            gens.H(padded_n).copied().collect(),
            l_vec,
            r_vec,
        )?;

        let second_phase = if A_I2.is_zero() && A_O2.is_zero() && S2.is_zero() {
            None
        } else {
            Some((A_I2, A_O2, S2))
        };

        let proof = R1CSProof {
            A_I1,
            A_O1,
            S1,
            second_phase,
            T,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        };
        Ok((proof, self.transcript))
    }
}

/// Returns the opening the prover stores for a vector commitment to `v`. Created for mocking.
#[cfg_attr(feature = "nightly_mocking_tests", mocktopus::macros::mockable)]
pub fn committed_vec_opening<F: Clone>(v: &[F]) -> Vec<F> {
    v.to_vec()
}

/// Returns the dimension the prover declares for a vector commitment with opening `opening`.
/// Created for mocking.
#[cfg_attr(feature = "nightly_mocking_tests", mocktopus::macros::mockable)]
pub fn committed_vec_dimension<F>(opening: &[F]) -> usize {
    opening.len()
}
