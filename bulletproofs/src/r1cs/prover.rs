#![allow(non_snake_case)]

use ark_ec::{AffineRepr, VariableBaseMSM};
use ark_ff::Field;
use ark_std::{One, UniformRand, Zero};
use core::borrow::BorrowMut;
use core::mem;
use merlin::Transcript;
use zeroize::{ZeroizeOnDrop, Zeroizing};

use super::constraint_system::{
    ConstraintSystem, RandomizableConstraintSystem, RandomizedConstraintSystem,
};
use super::linear_combination::{LinearCombination, Variable};
use super::proof::R1CSProof;

use crate::errors::R1CSError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::inner_product_proof::InnerProductProof;
use crate::r1cs::Metrics;
use crate::transcript::TranscriptProtocol;

use super::op_splits;

/// A [`ConstraintSystem`] implementation for use by the prover.
///
/// The prover commits high-level variables and their blinding factors `(v, v_blinding)`,
/// allocates low-level variables and creates constraints in terms of these
/// high-level variables and low-level variables.
///
/// When all constraints are added, the proving code calls `prove`
/// which consumes the `Prover` instance, samples random challenges
/// that instantiate the randomized constraints, and creates a complete proof.
pub struct Prover<'g, T: BorrowMut<Transcript>, C: AffineRepr> {
    transcript: T,
    pc_gens: &'g PedersenGens<C>,
    /// The constraints accumulated so far.
    constraints: Vec<LinearCombination<C::ScalarField>>,
    /// Secret data
    secrets: Secrets<C::ScalarField>,

    /// This list holds closures that will be called in the second phase of the protocol,
    /// when non-randomized variables are committed.
    deferred_constraints:
        Vec<Box<dyn FnOnce(&mut RandomizingProver<'g, T, C>) -> Result<(), R1CSError>>>,

    /// Index of a pending multiplier that's not fully assigned yet.
    pending_multiplier: Option<usize>,
}

// todo I assume this would be automatically implemented by the compiler if it did not have a a mutable borrow of a transcript
unsafe impl<'g, T: BorrowMut<Transcript>, C: AffineRepr> Send for Prover<'g, T, C> {} // todo fix after refactor

/// Separate struct to implement Drop trait for (for zeroing),
/// so that compiler does not prohibit us from moving the Transcript out of `prove()`.
#[derive(ZeroizeOnDrop)]
struct Secrets<F: Field> {
    /// Stores assignments to the "left" of multiplication gates
    a_L: Vec<F>,
    /// Stores assignments to the "right" of multiplication gates
    a_R: Vec<F>,
    /// Stores assignments to the "output" of multiplication gates
    a_O: Vec<F>,
    /// High-level witness data (value openings to V commitments)
    v: Vec<F>,
    /// High-level witness data (blinding openings to V commitments)
    v_blinding: Vec<F>,
    ///
    vec_open: Vec<(F, Vec<F>)>,
}

/// Prover in the randomizing phase.
///
/// Note: this type is exported because it is used to specify the associated type
/// in the public impl of a trait `ConstraintSystem`, which boils down to allowing compiler to
/// monomorphize the closures for the proving and verifying code.
/// However, this type cannot be instantiated by the user and therefore can only be used within
/// the callback provided to `specify_randomized_constraints`.
pub struct RandomizingProver<'g, T: BorrowMut<Transcript>, C: AffineRepr> {
    prover: Prover<'g, T, C>,
}

impl<'g, T: BorrowMut<Transcript>, C: AffineRepr> ConstraintSystem<C::ScalarField>
    for Prover<'g, T, C>
{
    fn transcript(&mut self) -> &mut Transcript {
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
}

impl<'g, T: BorrowMut<Transcript>, C: AffineRepr> RandomizableConstraintSystem<C::ScalarField>
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

impl<'g, T: BorrowMut<Transcript>, C: AffineRepr> ConstraintSystem<C::ScalarField>
    for RandomizingProver<'g, T, C>
{
    fn transcript(&mut self) -> &mut Transcript {
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
}

impl<'g, T: BorrowMut<Transcript>, C: AffineRepr> RandomizedConstraintSystem<C::ScalarField>
    for RandomizingProver<'g, T, C>
{
    fn challenge_scalar(&mut self, label: &'static [u8]) -> C::ScalarField {
        self.prover
            .transcript
            .borrow_mut()
            .challenge_scalar::<C>(label)
    }
}

impl<'g, T: BorrowMut<Transcript>, C: AffineRepr> Prover<'g, T, C> {
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
    /// `ProverCS` holds onto the `&mut Transcript` until it consumes
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
                v: Vec::new(),
                v_blinding: Vec::new(),
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
        let i = self.secrets.v.len();
        self.secrets.v.push(v);
        self.secrets.v_blinding.push(v_blinding);

        // Add the commitment to the transcript.
        let V = self.pc_gens.commit(v, v_blinding);
        self.transcript.borrow_mut().append_point(b"V", &V);

        (V, Variable::Committed(i))
    }

    pub fn commit_vec(
        &mut self,
        v: &[C::ScalarField],
        v_blinding: C::ScalarField,
        bp_gens: &BulletproofGens<C>, // same as used during proving, uses the "G" generators to commit like for a_O
    ) -> (C, Vec<Variable<C::ScalarField>>) {
        use std::iter;

        // compute the commitment:
        // comm = <v, G> + <v_blinding> B_blinding
        let gens = bp_gens.share(0);

        // [b] * H + [v_1] * G1 + ... + [v_n] * Gn
        let generators: Vec<_> = iter::once(&self.pc_gens.B_blinding)
            .chain(gens.G(v.len()))
            .copied()
            .collect::<Vec<_>>();

        let scalars: Vec<C::ScalarField> =
            iter::once(&v_blinding).chain(v.iter()).copied().collect();

        assert_eq!(generators.len(), scalars.len());

        let comm = C::Group::msm_unchecked(generators.as_slice(), scalars.as_slice());

        // create variables for all the addressable coordinates
        let comm_idx = self.secrets.vec_open.len();
        let vars = (0..v.len())
            .map(|i| Variable::VectorCommit(comm_idx, i))
            .collect();

        // add the opening (values || blinding) to the secrets
        self.secrets.vec_open.push((v_blinding, v.to_owned()));

        // add the commitment to the transcript.
        let comm = comm.into();
        self.transcript.borrow_mut().append_point(b"V", &comm);

        (comm, vars)
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
        let m = self.secrets.v.len();

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
                        Variable::Committed(i) => self.secrets.v[*i],
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
            let mut callbacks = mem::replace(&mut self.deferred_constraints, Vec::new());
            let mut wrapped_self = RandomizingProver { prover: self };
            for callback in callbacks.drain(..) {
                callback(&mut wrapped_self)?;
            }
            Ok(wrapped_self.prover)
        }
    }

    /// Consume this `ConstraintSystem` to produce a proof.
    pub fn prove(self, bp_gens: &BulletproofGens<C>) -> Result<R1CSProof<C>, R1CSError> {
        self.prove_and_return_transcript(bp_gens)
            .map(|(proof, _transcript)| proof)
    }

    pub fn size(&self) -> usize {
        let mut n = self.secrets.a_L.len();
        for (_, v) in self.secrets.vec_open.iter() {
            n = std::cmp::max(n, v.len());
        }
        n
    }

    pub fn number_of_constraints(&self) -> usize {
        self.secrets.a_L.len()
    }

    /// Consume this `ConstraintSystem` to produce a proof. Returns the proof and the transcript passed in `Prover::new`.
    pub fn prove_and_return_transcript(
        mut self,
        bp_gens: &BulletproofGens<C>,
    ) -> Result<(R1CSProof<C>, T), R1CSError> {
        // pad
        while self.size() > self.secrets.a_L.len() {
            self.allocate_multiplier(Some((C::ScalarField::zero(), C::ScalarField::zero())))?;
        }

        use crate::util;
        use std::iter;

        // number of commitments
        let ncomm = self.secrets.vec_open.len();

        // op_degree = 2 + 2 * floor(#comm / 2)
        let op_degree = 2 + 2 * (ncomm / 2);

        let ops = op_splits(op_degree);
        let veccom_ops = &ops[2..];

        #[cfg(debug_assertions)]
        {
            println!("op_degree: {}", op_degree);
            println!("number of commitments: {}", ncomm);
            println!("number of constraints: {}", self.secrets.a_L.len());
            println!("ops = {:?}", &ops[..]);
        }

        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        self.transcript
            .borrow_mut()
            .append_u64(b"m", self.secrets.v.len() as u64);

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
        //     for v_b in &self.secrets.v_blinding {
        //         builder = builder.rekey_with_witness_bytes(b"v_blinding", &util::field_as_bytes(v_b));
        //     }

        //     use rand::thread_rng;
        //     builder.finalize(&mut thread_rng())
        // };

        // Commit to the first-phase low-level witness variables.
        let n1 = self.size();

        if bp_gens.gens_capacity < n1 {
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        // We are performing a single-party circuit proof, so party index is 0.
        let gens = bp_gens.share(0);

        let mut rng = rand::thread_rng();
        let i_blinding1 = C::ScalarField::rand(&mut rng);
        let o_blinding1 = C::ScalarField::rand(&mut rng);
        let s_blinding1 = C::ScalarField::rand(&mut rng);

        let s_L1: Zeroizing<Vec<C::ScalarField>> =
            Zeroizing::new((0..n1).map(|_| C::ScalarField::rand(&mut rng)).collect());
        let s_R1: Zeroizing<Vec<C::ScalarField>> =
            Zeroizing::new((0..n1).map(|_| C::ScalarField::rand(&mut rng)).collect());

        #[cfg(feature = "parallel")]
        let (A_I1, A_O1, S1) = {
            // todo clean up when send is safely implemented
            let blinding = self.pc_gens.B_blinding;
            let A_I1_scalars = iter::once(&i_blinding1)
                .chain(self.secrets.a_L.iter())
                .chain(self.secrets.a_R.iter())
                .copied()
                .collect::<Vec<C::ScalarField>>();
            let A_O1_scalars = iter::once(&o_blinding1)
                .chain(self.secrets.a_O.iter())
                .copied()
                .collect::<Vec<C::ScalarField>>();
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
                    S1 = Some(
                        C::Group::msm_unchecked(
                            iter::once(&blinding)
                                .chain(gens.G(n1))
                                .chain(gens.H(n1))
                                .copied()
                                .collect::<Vec<C>>()
                                .as_slice(),
                            iter::once(&s_blinding1)
                                .chain(s_L1.iter())
                                .chain(s_R1.iter())
                                .copied()
                                .collect::<Vec<C::ScalarField>>()
                                .as_slice(),
                        )
                        .into(),
                    )
                });
            });

            (A_I1.unwrap(), A_O1.unwrap(), S1.unwrap())
        };
        #[cfg(not(feature = "parallel"))]
        let (A_I1, A_O1, S1) = {
            // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
            let A_I1 = C::Group::msm_unchecked(
                iter::once(&self.pc_gens.B_blinding)
                    .chain(gens.G(n1))
                    .chain(gens.H(n1))
                    .copied()
                    .collect::<Vec<C>>()
                    .as_slice(),
                iter::once(&i_blinding1)
                    .chain(self.secrets.a_L.iter())
                    .chain(self.secrets.a_R.iter())
                    .map(|s| (*s).into())
                    .collect::<Vec<C::ScalarField>>()
                    .as_slice(),
            )
            .into();

            // A_O = <a_O, G> + o_blinding * B_blinding
            let A_O1 = C::Group::msm_unchecked(
                iter::once(&self.pc_gens.B_blinding)
                    .chain(gens.G(n1))
                    .copied()
                    .collect::<Vec<C>>()
                    .as_slice(),
                iter::once(&o_blinding1)
                    .chain(self.secrets.a_O.iter())
                    .map(|s| (*s).into())
                    .collect::<Vec<C::ScalarField>>()
                    .as_slice(),
            )
            .into();

            // Vector commitments of the form
            // <Vi, G> + vi_blinding * B:blinding

            // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
            let S1 = C::Group::msm_unchecked(
                iter::once(&self.pc_gens.B_blinding)
                    .chain(gens.G(n1))
                    .chain(gens.H(n1))
                    .copied()
                    .collect::<Vec<C>>()
                    .as_slice(),
                iter::once(&s_blinding1)
                    .chain(s_L1.iter())
                    .chain(s_R1.iter())
                    .map(|s| (*s).into())
                    .collect::<Vec<C::ScalarField>>()
                    .as_slice(),
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
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        // Commit to the second-phase low-level witness variables

        let has_2nd_phase_commitments = n2 > 0;

        let (i_blinding2, o_blinding2, s_blinding2) = if has_2nd_phase_commitments {
            (
                C::ScalarField::rand(&mut rng),
                C::ScalarField::rand(&mut rng),
                C::ScalarField::rand(&mut rng),
            )
        } else {
            (
                C::ScalarField::zero(),
                C::ScalarField::zero(),
                C::ScalarField::zero(),
            )
        };

        let s_L2: Zeroizing<Vec<C::ScalarField>> =
            Zeroizing::new((0..n2).map(|_| C::ScalarField::rand(&mut rng)).collect());
        let s_R2: Zeroizing<Vec<C::ScalarField>> =
            Zeroizing::new((0..n2).map(|_| C::ScalarField::rand(&mut rng)).collect());

        // both not supported atm.
        assert!(!has_2nd_phase_commitments || self.secrets.vec_open.is_empty());

        let (A_I2, A_O2, S2) = if has_2nd_phase_commitments {
            (
                // A_I = <a_L, G> + <a_R, H> + i_blinding * B_blinding
                C::Group::msm_unchecked(
                    iter::once(&self.pc_gens.B_blinding)
                        .chain(gens.G(n).skip(n1))
                        .chain(gens.H(n).skip(n1))
                        .copied()
                        .collect::<Vec<C>>()
                        .as_slice(),
                    iter::once(&i_blinding2)
                        .chain(self.secrets.a_L.iter().skip(n1))
                        .chain(self.secrets.a_R.iter().skip(n1))
                        .copied()
                        .collect::<Vec<C::ScalarField>>()
                        .as_slice(),
                )
                .into(),
                // A_O = <a_O, G> + o_blinding * B_blinding
                C::Group::msm_unchecked(
                    iter::once(&self.pc_gens.B_blinding)
                        .chain(gens.G(n).skip(n1))
                        .copied()
                        .collect::<Vec<C>>()
                        .as_slice(),
                    iter::once(&o_blinding2)
                        .chain(self.secrets.a_O.iter().skip(n1))
                        .copied()
                        .collect::<Vec<C::ScalarField>>()
                        .as_slice(),
                )
                .into(),
                // S = <s_L, G> + <s_R, H> + s_blinding * B_blinding
                C::Group::msm_unchecked(
                    iter::once(&self.pc_gens.B_blinding)
                        .chain(gens.G(n).skip(n1))
                        .chain(gens.H(n).skip(n1))
                        .copied()
                        .collect::<Vec<C>>()
                        .as_slice(),
                    iter::once(&s_blinding2)
                        .chain(s_L2.iter())
                        .chain(s_R2.iter())
                        .copied()
                        .collect::<Vec<C::ScalarField>>()
                        .as_slice(),
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

        let y = transcript.challenge_scalar::<C>(b"y");
        let z = transcript.challenge_scalar::<C>(b"z");

        // println!("P A_I2 {}", &A_I2);
        // println!("P A_O2 {}", &A_O2);
        // println!("P S2 {}", &S2);
        // println!("P z {}", z);

        let (wL, wR, wO, wV, wVCs) = self.flattened_constraints(&z);

        #[cfg(debug_assertions)]
        {
            println!("Length of constraints vector: {}", self.constraints.len());
            println!("prover wVCs = {:?}", &wVCs);
            println!("prover wL = {:?}", &wL);
            println!("prover wR = {:?}", &wR);
            println!("prover wO = {:?}", &wO);
        }

        let mut l_poly = util::VecPoly::<C::ScalarField>::zero(n, op_degree + 1);
        let mut r_poly = util::VecPoly::<C::ScalarField>::zero(n, op_degree + 1);

        let y_inv = y.inverse().unwrap();

        let exp_y_inv = util::exp_iter(y_inv).take(padded_n).collect::<Vec<_>>();
        let exp_y = util::exp_iter(y).take(padded_n).collect::<Vec<_>>();

        //
        let sLsR = s_L1
            .iter()
            .chain(s_L2.iter())
            .zip(s_R1.iter().chain(s_R2.iter()));

        debug_assert_eq!(op_degree % 2, 0, "op_degree must be even");

        let mid_degree = op_degree / 2;

        // 1 comm => op_degree = 2
        // 2 comm => op_degree = 4
        // 3 comm => op_degree = 4
        // 4 comm => op_degree = 6
        // 5 comm => op_degree = 6
        // etc.
        // op_degree = 2 + 2 * floor(#comm / 2)

        for (i, (sl, sr)) in sLsR.enumerate() {
            debug_assert!(i < self.secrets.a_L.len());

            // The first (original) op_degree is 2, which permits a single vector commitment:
            //
            // Left:
            // 0 : com1
            // 1 : aL + wR
            // 2 : aO
            // 3 : sL
            //
            // Right:
            // 0 : Wo
            // 1 : aR + wL
            // 2 : Wc1
            // 3 : sR
            //
            // Since a_L and a_R must be at the same power, only even op_degrees are possible :(
            // Hence the next valid op_degree is 4, which permits up to 3 vector commitments:
            //
            // Left:
            // 0 : com1
            // 1 : com2
            // 2 : aL
            // 3 : aO
            // 4 : com3
            // 5 : sL
            //
            // Right:
            // 0 : Wc3
            // 1 : Wo
            // 2 : aR
            // 3 : Wc2
            // 4 : Wc1
            // 5 : sR
            //
            // The next valid op_degree is 6, this permits up to 5 vector commitments:
            //
            // Left:
            // 0 : com1
            // 1 : com2
            // 2 : com3
            // 3 : aL
            // 4 : aO
            // 5 : com4
            // 6 : com5
            // 7 : sL
            //
            // Right:
            // 0 : Wc5
            // 1 : Wc4
            // 2 : Wo
            // 3 : aR
            // 4 : Wc3
            // 5 : Wc2
            // 6 : Wc1
            // 7 : sR
            //
            // Note that the x^0, x^1 term is zero.
            // For every additional commitment r_poly degree increases by 2,
            // but the number of zero terms increase by 1
            //
            // The op_degree is 6, the total degree is 11.
            //
            // Left:
            // 1 : com1
            // 2 : com2
            // 3 : com3
            // 4 : aL
            // 5 : aO
            // 6 : -
            // 7 : -
            // 8 : -
            // 9 : sL
            //
            // Right:
            // 3 : Wo
            // 4 : aR
            // 5 : Wc3
            // 6 : Wc2
            // 7 : Wc1
            // 8 : -
            // 9 : sR
            //
            // op_degree is 8

            // l_poly.0 = 0

            // a_L and a_R constraints:
            //
            // l_poly.1 = a_L + y^-n * (z * z^Q * W_R)
            // r_poly.1 = y^n * a_R + (z * z^Q * W_L)
            debug_assert_eq!(l_poly.coeff_mut(mid_degree)[i], C::ScalarField::zero());
            debug_assert_eq!(r_poly.coeff_mut(mid_degree)[i], C::ScalarField::zero());
            l_poly.coeff_mut(ops[0].0)[i] = self.secrets.a_L[i] + exp_y_inv[i] * wR[i];
            r_poly.coeff_mut(ops[0].1)[i] = exp_y[i] * self.secrets.a_R[i] + wL[i];

            // a_O constraints:
            //
            // l_poly.2 = a_O
            // r_poly.0 = (z * z^Q * W_O) - y^n
            debug_assert_eq!(l_poly.coeff_mut(op_degree)[i], C::ScalarField::zero());
            debug_assert_eq!(r_poly.coeff_mut(0)[i], C::ScalarField::zero());
            l_poly.coeff_mut(ops[1].0)[i] = self.secrets.a_O[i];
            r_poly.coeff_mut(ops[1].1)[i] = wO[i] - exp_y[i];

            // masks:
            // l_poly.3 = s_L (mask)
            debug_assert_eq!(l_poly.coeff_mut(op_degree + 1)[i], C::ScalarField::zero());
            debug_assert_eq!(r_poly.coeff_mut(op_degree + 1)[i], C::ScalarField::zero());
            l_poly.coeff_mut(op_degree + 1)[i] = *sl;
            r_poly.coeff_mut(op_degree + 1)[i] = exp_y[i] * sr;
        }

        // veccom constraints
        for (j, w) in self.secrets.vec_open.iter().enumerate() {
            //
            let (l_deg, r_deg) = veccom_ops[j];

            // copy values to l_poly r_poly
            for i in 0..w.1.len() {
                debug_assert_eq!(l_poly.coeff_mut(l_deg)[i], C::ScalarField::zero());
                debug_assert_eq!(r_poly.coeff_mut(r_deg)[i], C::ScalarField::zero());
                l_poly.coeff_mut(l_deg)[i] = w.1[i];
                r_poly.coeff_mut(r_deg)[i] = wVCs[j][i];
            }
        }

        let mut t_poly = util::VecPoly::inner_product(&l_poly, &r_poly);
        assert_eq!(t_poly.deg(), 2 * (op_degree + 1));

        // commit to t-poly
        let mut t_blinding_poly = util::Poly::zero(t_poly.deg());
        for d in 0..t_poly.deg() + 1 {
            if d == op_degree {
                continue;
            }
            t_blinding_poly.coeff()[d] = C::ScalarField::rand(&mut rng);
            // println!("T_{}", d);
        }

        // commit to t-poly
        let mut T = vec![C::zero(); t_poly.deg() + 1];
        for d in 0..t_poly.deg() + 1 {
            if d == op_degree {
                continue;
            }
            T[d] = self
                .pc_gens
                .commit(t_poly.coeff()[d], t_blinding_poly.coeff()[d]);
        }

        // commit to T
        let transcript = self.transcript.borrow_mut();
        for d in 0..t_poly.deg() + 1 {
            if d == op_degree {
                continue;
            }
            transcript.append_point(util::T_LABELS[d], &T[d]);
        }

        let u = transcript.challenge_scalar::<C>(b"u");
        let x = transcript.challenge_scalar::<C>(b"x");

        // calculate x^op_degree
        let mut op_x = C::ScalarField::one();
        for _ in 0..op_degree {
            op_x *= x;
        }

        #[cfg(debug_assertions)]
        println!("prover: x = {}", x);

        t_blinding_poly.coeff()[op_degree] = wV
            .iter()
            .zip(self.secrets.v_blinding.iter())
            .map(|(c, v_blinding)| *c * v_blinding)
            .sum();

        let t_x = t_poly.eval(x);
        let t_x_blinding = t_blinding_poly.eval(x);

        // The constant term of l is zero, hence l_vec is zero beyond n
        let mut l_vec = l_poly.eval(x);
        l_vec.append(&mut vec![C::ScalarField::zero(); pad]);

        // XXX this should refer to the notes to explain why this is correct
        // This is the constant term of r(x) beyond w_O since it is zero after n.
        let mut r_vec = r_poly.eval(x);
        r_vec.append(&mut vec![C::ScalarField::zero(); pad]);
        for i in n..padded_n {
            r_vec[i] = -exp_y[i];
        }

        // sanity check
        #[cfg(debug_assertions)]
        {
            use crate::inner_product_proof::inner_product;

            let y_inv = y.inverse().unwrap();
            let y_inv_vec = util::exp_iter(y_inv)
                .take(padded_n)
                .collect::<Vec<C::ScalarField>>();

            let yneg_wR = wR
                .iter()
                .zip(y_inv_vec.iter())
                .map(|(wRi, exp_y_inv)| (*wRi) * exp_y_inv)
                .chain(iter::repeat(C::ScalarField::zero()).take(padded_n - n))
                .collect::<Vec<C::ScalarField>>();

            let delta = inner_product(&yneg_wR[0..n], &wL);

            let yn: Vec<_> = util::exp_iter(y).take(n).collect();
            let mut aRyn = vec![C::ScalarField::zero(); n];
            for i in 0..n {
                aRyn[i] = self.secrets.a_R[i] * yn[i];
            }

            let mut t2 = C::ScalarField::zero();

            // linear term
            t2 += inner_product(&wL, &self.secrets.a_L);
            t2 += inner_product(&wR, &self.secrets.a_R);
            t2 += inner_product(&wO, &self.secrets.a_O);

            for i in 0..self.secrets.vec_open.len() {
                t2 += inner_product(&wVCs[i], &self.secrets.vec_open[i].1);
            }

            // product
            t2 += inner_product(&self.secrets.a_L, &aRyn);
            t2 -= inner_product(&self.secrets.a_O, &yn);

            // publicly computable correction
            t2 += delta;

            assert_eq!(t_poly.coeff()[op_degree], t2, "t_poly term check failed");
            println!("sanity check passed");
        }

        let i_blinding = i_blinding1 + u * i_blinding2;
        let o_blinding = o_blinding1 + u * o_blinding2;
        let s_blinding = s_blinding1 + u * s_blinding2;

        //
        let mut e_terms: Vec<Option<C::ScalarField>> = vec![None; l_poly.deg() + 1];

        // special
        debug_assert_eq!(ops[0].0, ops[0].1);
        e_terms[ops[0].0] = Some(i_blinding); // aL || aR
        e_terms[ops[1].0] = Some(o_blinding); // aO

        // veccom
        for j in 0..ncomm {
            debug_assert!(e_terms[veccom_ops[j].0].is_none());
            e_terms[veccom_ops[j].0] = Some(self.secrets.vec_open[j].0);
        }

        // blinding
        e_terms[op_degree + 1] = Some(s_blinding); // sL || sR

        #[cfg(debug_assertions)]
        {
            for (i, e) in e_terms.iter().enumerate() {
                println!("e_terms, x^{} = {:?}", i, e);
            }
        }

        // evaluate blinding
        let mut e_blinding = C::ScalarField::zero();
        {
            let mut xn = C::ScalarField::one();
            for bnd in e_terms.into_iter() {
                if let Some(val) = bnd {
                    e_blinding += xn * val;
                }
                xn *= x;
            }
        }

        transcript.append_scalar::<C>(b"t_x", &t_x);
        transcript.append_scalar::<C>(b"t_x_blinding", &t_x_blinding);
        transcript.append_scalar::<C>(b"e_blinding", &e_blinding);

        // Get a challenge value to combine statements for the IPP
        let w = transcript.challenge_scalar::<C>(b"w");
        let Q = self.pc_gens.B.mul(w).into();

        let G_factors = iter::repeat(C::ScalarField::one())
            .take(n1)
            .chain(iter::repeat(u).take(n2 + pad))
            .collect::<Vec<_>>();

        let H_factors = exp_y_inv
            .into_iter()
            .zip(G_factors.iter())
            .map(|(y_inv, u_or_1)| y_inv * u_or_1)
            .collect::<Vec<_>>();

        // TODO: check if missing \circ y^{-1} on the vec. comm part:
        // everything in H_generators (r_vec) is mult. by y!

        let ipp_proof = InnerProductProof::create(
            transcript,
            &Q,
            &G_factors,
            &H_factors,
            gens.G(padded_n).copied().collect(),
            gens.H(padded_n).copied().collect(),
            l_vec,
            r_vec,
        );

        let proof = R1CSProof {
            A_I1,
            A_O1,
            S1,
            A_I2,
            A_O2,
            S2,
            T,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
        };
        Ok((proof, self.transcript))
    }
}
