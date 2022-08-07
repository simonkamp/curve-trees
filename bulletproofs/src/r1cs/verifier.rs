#![allow(non_snake_case)]

use ark_ec::{msm::VariableBaseMSM, AffineCurve};
use ark_ff::{Field, PrimeField};
use ark_std::{One, UniformRand, Zero};
use core::borrow::BorrowMut;
use core::mem;
use merlin::Transcript;

use super::constraint_system::{
    ConstraintSystem, RandomizableConstraintSystem, RandomizedConstraintSystem,
};
use super::linear_combination::{LinearCombination, Variable};
use super::proof::R1CSProof;

use crate::errors::R1CSError;
use crate::generators::{BulletproofGens, PedersenGens};
use crate::r1cs::Metrics;
use crate::transcript::TranscriptProtocol;

/// A [`ConstraintSystem`] implementation for use by the verifier.
///
/// The verifier adds high-level variable commitments to the transcript,
/// allocates low-level variables and creates constraints in terms of these
/// high-level variables and low-level variables.
///
/// When all constraints are added, the verifying code calls `verify`
/// which consumes the `Verifier` instance, samples random challenges
/// that instantiate the randomized constraints, and verifies the proof.
pub struct Verifier<T: BorrowMut<Transcript>, C: AffineCurve> {
    transcript: T,
    constraints: Vec<LinearCombination<C::ScalarField>>,

    vec_comms: Vec<(C, usize)>,

    /// Records the number of low-level variables allocated in the
    /// constraint system.
    ///
    /// Because the `VerifierCS` only keeps the constraints
    /// themselves, it doesn't record the assignments (they're all
    /// `Missing`), so the `num_vars` isn't kept implicitly in the
    /// variable assignments.
    num_vars: usize,
    V: Vec<C>,

    /// This list holds closures that will be called in the second phase of the protocol,
    /// when non-randomized variables are committed.
    /// After that, the option will flip to None and additional calls to `randomize_constraints`
    /// will invoke closures immediately.
    deferred_constraints:
        Vec<Box<dyn FnOnce(&mut RandomizingVerifier<T, C>) -> Result<(), R1CSError>>>,

    /// Index of a pending multiplier that's not fully assigned yet.
    pending_multiplier: Option<usize>,
}

/// Verifier in the randomizing phase.
///
/// Note: this type is exported because it is used to specify the associated type
/// in the public impl of a trait `ConstraintSystem`, which boils down to allowing compiler to
/// monomorphize the closures for the proving and verifying code.
/// However, this type cannot be instantiated by the user and therefore can only be used within
/// the callback provided to `specify_randomized_constraints`.
pub struct RandomizingVerifier<T: BorrowMut<Transcript>, C: AffineCurve> {
    verifier: Verifier<T, C>,
}

impl<T: BorrowMut<Transcript>, C: AffineCurve> ConstraintSystem<C> for Verifier<T, C> {
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
        let var = self.num_vars;
        self.num_vars += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        // Constrain l,r,o:
        left.terms.push((l_var, -C::ScalarField::one()));
        right.terms.push((r_var, -C::ScalarField::one()));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate(
        &mut self,
        _: Option<C::ScalarField>,
    ) -> Result<Variable<C::ScalarField>, R1CSError> {
        match self.pending_multiplier {
            None => {
                let i = self.num_vars;
                self.num_vars += 1;
                self.pending_multiplier = Some(i);
                Ok(Variable::MultiplierLeft(i))
            }
            Some(i) => {
                self.pending_multiplier = None;
                Ok(Variable::MultiplierRight(i))
            }
        }
    }

    fn allocate_multiplier(
        &mut self,
        _: Option<(C::ScalarField, C::ScalarField)>,
    ) -> Result<
        (
            Variable<C::ScalarField>,
            Variable<C::ScalarField>,
            Variable<C::ScalarField>,
        ),
        R1CSError,
    > {
        let var = self.num_vars;
        self.num_vars += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        Ok((l_var, r_var, o_var))
    }

    fn metrics(&self) -> Metrics {
        Metrics {
            multipliers: self.num_vars,
            constraints: self.constraints.len() + self.deferred_constraints.len(),
            phase_one_constraints: self.constraints.len(),
            phase_two_constraints: self.deferred_constraints.len(),
        }
    }

    fn constrain(&mut self, lc: LinearCombination<C::ScalarField>) {
        // TODO: check that the linear combinations are valid
        // (e.g. that variables are valid, that the linear combination
        // evals to 0 for prover, etc).
        self.constraints.push(lc);
    }
}

impl<T: BorrowMut<Transcript>, C: AffineCurve> RandomizableConstraintSystem<C> for Verifier<T, C> {
    type RandomizedCS = RandomizingVerifier<T, C>;

    fn specify_randomized_constraints<F>(&mut self, callback: F) -> Result<(), R1CSError>
    where
        F: 'static + FnOnce(&mut Self::RandomizedCS) -> Result<(), R1CSError>,
    {
        self.deferred_constraints.push(Box::new(callback));
        Ok(())
    }
}

impl<T: BorrowMut<Transcript>, C: AffineCurve> ConstraintSystem<C> for RandomizingVerifier<T, C> {
    fn transcript(&mut self) -> &mut Transcript {
        self.verifier.transcript.borrow_mut()
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
        self.verifier.multiply(left, right)
    }

    fn allocate(
        &mut self,
        assignment: Option<C::ScalarField>,
    ) -> Result<Variable<C::ScalarField>, R1CSError> {
        self.verifier.allocate(assignment)
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
        self.verifier.allocate_multiplier(input_assignments)
    }

    fn metrics(&self) -> Metrics {
        self.verifier.metrics()
    }

    fn constrain(&mut self, lc: LinearCombination<C::ScalarField>) {
        self.verifier.constrain(lc)
    }
}

impl<T: BorrowMut<Transcript>, C: AffineCurve> RandomizedConstraintSystem<C>
    for RandomizingVerifier<T, C>
{
    fn challenge_scalar(&mut self, label: &'static [u8]) -> C::ScalarField {
        self.verifier
            .transcript
            .borrow_mut()
            .challenge_scalar::<C>(label)
    }
}

impl<T: BorrowMut<Transcript>, C: AffineCurve> Verifier<T, C> {
    /// Construct an empty constraint system with specified external
    /// input variables.
    ///
    /// # Inputs
    ///
    /// The `transcript` parameter is a Merlin proof transcript.  The
    /// `VerifierCS` holds onto the `&mut Transcript` until it consumes
    /// itself during [`VerifierCS::verify`], releasing its borrow of the
    /// transcript.  This ensures that the transcript cannot be
    /// altered except by the `VerifierCS` before proving is complete.
    ///
    /// The `commitments` parameter is a list of Pedersen commitments
    /// to the external variables for the constraint system.  All
    /// external variables must be passed up-front, so that challenges
    /// produced by [`ConstraintSystem::challenge_scalar`] are bound
    /// to the external variables.
    ///
    /// # Returns
    ///
    /// Returns a tuple `(cs, vars)`.
    ///
    /// The first element is the newly constructed constraint system.
    ///
    /// The second element is a list of [`Variable`]s corresponding to
    /// the external inputs, which can be used to form constraints.
    pub fn new(mut transcript: T) -> Self {
        transcript.borrow_mut().r1cs_domain_sep();

        Verifier {
            vec_comms: Vec::new(),
            transcript,
            num_vars: 0,
            V: Vec::new(),
            constraints: Vec::new(),
            deferred_constraints: Vec::new(),
            pending_multiplier: None,
        }
    }

    /// Creates commitment to a high-level variable and adds it to the transcript.
    ///
    /// # Inputs
    ///
    /// The `commitment` parameter is a Pedersen commitment
    /// to the external variable for the constraint system.  All
    /// external variables must be passed up-front, so that challenges
    /// produced by [`ConstraintSystem::challenge_scalar`] are bound
    /// to the external variables.
    ///
    /// # Returns
    ///
    /// Returns a pair of a Pedersen commitment (as a compressed Ristretto point),
    /// and a [`Variable`] corresponding to it, which can be used to form constraints.
    pub fn commit(&mut self, commitment: C) -> Variable<C::ScalarField> {
        let i = self.V.len();
        self.V.push(commitment);

        // Add the commitment to the transcript.
        self.transcript.borrow_mut().append_point(b"V", &commitment);

        Variable::Committed(i)
    }

    pub fn commit_vec(&mut self, dimension: usize, comm: C) -> Vec<Variable<C::ScalarField>> {
        // allocate next index for vector commitment
        let comm_idx = self.vec_comms.len();

        // add the commitment to the transcript.
        self.transcript.borrow_mut().append_point(b"V", &comm);

        // add to list of commitments
        self.vec_comms.push((comm, dimension));

        // create variables for all the addressable coordinates
        (0..dimension)
            .map(|i| Variable::VectorCommit(comm_idx, i))
            .collect()
    }

    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV, wc)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    ///
    /// This has the same logic as `ProverCS::flattened_constraints()`
    /// but also computes the constant terms (which the prover skips
    /// because they're not needed to construct the proof).
    fn flattened_constraints(
        &mut self,
        z: &C::ScalarField,
    ) -> (
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
        Vec<C::ScalarField>,
        Vec<Vec<C::ScalarField>>,
        C::ScalarField,
    ) {
        let n = self.num_vars;
        let m = self.V.len();

        let mut wL = vec![C::ScalarField::zero(); n];
        let mut wR = vec![C::ScalarField::zero(); n];
        let mut wO = vec![C::ScalarField::zero(); n];
        let mut wV = vec![C::ScalarField::zero(); m];
        let mut wc = C::ScalarField::zero();

        // TODO: compute dynamically
        let comm_dim = 32;
        let comm_num = 1;

        let mut wVCs = vec![vec![C::ScalarField::zero(); comm_dim]; comm_num];

        let mut exp_z = *z;
        for lc in self.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var {
                    Variable::VectorCommit(j, i) => {
                        // j : index of commitment
                        // i : coordinate with-in commitment
                        wVCs[*j][*i] += exp_z * coeff;
                    }
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
                    Variable::One(_) => {
                        wc -= exp_z * coeff;
                    }
                }
            }
            exp_z *= z;
        }

        (wL, wR, wO, wV, wVCs, wc)
    }

    /// Calls all remembered callbacks with an API that
    /// allows generating challenge scalars.
    fn create_randomized_constraints(mut self) -> Result<Self, R1CSError> {
        // Clear the pending multiplier (if any) because it was committed into A_L/A_R/S.
        self.pending_multiplier = None;

        if self.deferred_constraints.len() == 0 {
            self.transcript.borrow_mut().r1cs_1phase_domain_sep();
            Ok(self)
        } else {
            self.transcript.borrow_mut().r1cs_2phase_domain_sep();
            // Note: the wrapper could've used &mut instead of ownership,
            // but specifying lifetimes for boxed closures is not going to be nice,
            // so we move the self into wrapper and then move it back out afterwards.
            let mut callbacks = mem::replace(&mut self.deferred_constraints, Vec::new());
            let mut wrapped_self = RandomizingVerifier { verifier: self };
            for callback in callbacks.drain(..) {
                callback(&mut wrapped_self)?;
            }
            Ok(wrapped_self.verifier)
        }
    }

    /// Consume this `VerifierCS` and attempt to verify the supplied `proof`.
    /// The `pc_gens` and `bp_gens` are generators for Pedersen commitments and
    /// Bulletproofs vector commitments, respectively.  The
    /// [`BulletproofGens`] should have `gens_capacity` greater than
    /// the number of multiplication constraints that will eventually
    /// be added into the constraint system.
    pub fn verify(
        self,
        proof: &R1CSProof<C>,
        pc_gens: &PedersenGens<C>,
        bp_gens: &BulletproofGens<C>,
    ) -> Result<(), R1CSError> {
        let (proof_points, proof_scalars, fixed_point_scalars, padded_n) =
            match self.verification_scalars_and_points(proof) {
                Err(e) => return Err(e),
                Ok(t) => t,
            };

        // We are performing a single-party circuit proof, so party index is 0.
        let gens = bp_gens.share(0);

        if bp_gens.gens_capacity < padded_n {
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        use std::iter;
        let fixed_points = iter::once(pc_gens.B[0])
            .chain(iter::once(pc_gens.B_blinding))
            .chain(gens.G(padded_n).map(|&G_i| (G_i)))
            .chain(gens.H(padded_n).map(|&H_i| (H_i)));

        let mega_check: C::Projective = VariableBaseMSM::multi_scalar_mul(
            proof_points
                .into_iter()
                .chain(fixed_points)
                .collect::<Vec<_>>()
                .as_slice(),
            proof_scalars
                .into_iter()
                .chain(fixed_point_scalars.into_iter())
                .map(|s| s.into())
                .collect::<Vec<_>>()
                .as_slice(),
        );

        if !mega_check.is_zero() {
            return Err(R1CSError::VerificationError);
        }

        Ok(())
    }

    pub fn verification_scalars_and_points(
        mut self,
        proof: &R1CSProof<C>,
    ) -> Result<(Vec<C>, Vec<C::ScalarField>, Vec<C::ScalarField>, usize), R1CSError> {
        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        let transcript = self.transcript.borrow_mut();
        transcript.append_u64(b"m", self.V.len() as u64);

        let op_degree = 2 + self.vec_comms.len();
        let t_poly_deg = 6 + 2 * self.vec_comms.len();

        println!("{}", t_poly_deg);

        assert_eq!(t_poly_deg + 1, proof.T.len());

        let n1 = self.num_vars;
        transcript.validate_and_append_point(b"A_I1", &proof.A_I1)?;
        transcript.validate_and_append_point(b"A_O1", &proof.A_O1)?;
        transcript.validate_and_append_point(b"S1", &proof.S1)?;

        // Process the remaining constraints.
        self = self.create_randomized_constraints()?;

        let transcript = self.transcript.borrow_mut();

        // If the number of multiplications is not 0 or a power of 2, then pad the circuit.
        let n = self.num_vars;
        let n2 = n - n1;
        let padded_n = self.num_vars.next_power_of_two();
        let pad = padded_n - n;

        use crate::inner_product_proof::inner_product;
        use crate::util;
        use std::iter;

        // These points are the identity in the 1-phase unrandomized case.
        transcript.append_point(b"A_I2", &proof.A_I2);
        transcript.append_point(b"A_O2", &proof.A_O2);
        transcript.append_point(b"S2", &proof.S2);

        let y = transcript.challenge_scalar::<C>(b"y");
        let z = transcript.challenge_scalar::<C>(b"z");

        println!("V A_I2 {}", &proof.A_I2);
        println!("V A_O2 {}", &proof.A_O2);
        println!("V S2 {}", &proof.S2);
        println!("V z {}", z);

        // commit to T
        
        let transcript = self.transcript.borrow_mut();
        for d in 1..t_poly_deg + 1 {
            if d == op_degree {
                continue;
            }
            println!("{}", &proof.T[d]);
            transcript.validate_and_append_point(util::T_LABELS[d], &proof.T[d])?;
        }

        let u = transcript.challenge_scalar::<C>(b"u");
        let x = transcript.challenge_scalar::<C>(b"x");

        println!("V x: {}", x);

        transcript.append_scalar::<C>(b"t_x", &proof.t_x);
        transcript.append_scalar::<C>(b"t_x_blinding", &proof.t_x_blinding);
        transcript.append_scalar::<C>(b"e_blinding", &proof.e_blinding);

        let w = transcript.challenge_scalar::<C>(b"w");

        let (wL, wR, wO, wV, wVCs, wc) = self.flattened_constraints(&z);

        // Get IPP variables
        let (u_sq, u_inv_sq, s) = proof
            .ipp_proof
            .verification_scalars(padded_n, self.transcript.borrow_mut())
            .map_err(|_| R1CSError::VerificationError)?;

        let a = proof.ipp_proof.a;
        let b = proof.ipp_proof.b;

        let y_inv = y.inverse().unwrap();
        let y_inv_vec = util::exp_iter(y_inv)
            .take(padded_n)
            .collect::<Vec<C::ScalarField>>();
        let yneg_wR = wR
            .into_iter()
            .zip(y_inv_vec.iter())
            .map(|(wRi, exp_y_inv)| wRi * exp_y_inv)
            .chain(iter::repeat(C::ScalarField::zero()).take(pad))
            .collect::<Vec<C::ScalarField>>();

        let delta = inner_product(&yneg_wR[0..n], &wL);

        let mut u_for_g = iter::repeat(C::ScalarField::one())
            .take(n1)
            .chain(iter::repeat(u).take(n2 + pad));
        let mut u_for_h = u_for_g.clone();

        // define parameters for P check
        /*
        let mut g_scalars = Vec::with_capacity(padded_n);
        
        {
            let mut yneg_wR = yneg_wR.into_iter();
            let mut s = s.iter().rev().take(padded_n);

            for _ in 0..padded_n {
                let yneg_wRi = yneg_wR.next().unwrap();
                let u_or_1 = u_for_g.next().unwrap();
                let si = s.next().unwrap();

                let res = u_or_1 * (x * yneg_wRi - a * si);

                g_scalars.push(res);
            }
        }
        */

        let g_scalars = yneg_wR
            .iter()
            .zip(u_for_g.clone())
            .zip(s.iter().take(padded_n))
            .map(|((yneg_wRi, u_or_1), s_i)| u_or_1 * (x * yneg_wRi - a * s_i));

        // 
        let mut h_scalars = Vec::with_capacity(padded_n);
        {
            let mut wL = wL.into_iter();
            let mut wO = wO.into_iter();
            let mut s = s.iter().rev().take(padded_n);
            let mut y_inv_vec = y_inv_vec.into_iter();

            for i in 0..padded_n {
                let y_inv = y_inv_vec.next().unwrap();
                let u_or_1 = u_for_h.next().unwrap();

                let wLi = wL.next().unwrap_or_default();
                let wOi = wO.next().unwrap_or_default();

                let si = s.next().unwrap();

                let mut comb = x * wLi + wOi;

                // add terms for vector commitments
                for j in 0..self.vec_comms.len() {
                    comb *= x;
                    comb += wVCs[j][i];
                }

                // y^{-n} o (w_L * x^2 + w_O * x + w_Vi)
                let res = u_or_1 * (y_inv * (comb - b * si) - C::ScalarField::one());
                
                h_scalars.push(res);
            }
        }

        let mut rng = rand::thread_rng();
        let r = C::ScalarField::rand(&mut rng);
        let xx = x * x;
        let rxx = r * xx;
        let xxx = x * xx;

        // group the T_scalars and T_points together
        let mut T_points = vec![];
        let mut T_scalars = vec![]; // [r * x, rxx * x, rxx * xx, rxx * xxx, rxx * xx * xx];
        let mut rxn = r;
        for d in 1..t_poly_deg + 1 {
            rxn *= x;
            if d == op_degree {
                continue;
            }
            T_points.push(proof.T[d].clone());
            T_scalars.push(rxn);
        }

        let mut xoff = C::ScalarField::one();

        let mut comm_V: Vec<_> = Vec::with_capacity(self.vec_comms.len());
        let mut scalar_V: Vec<_> = Vec::with_capacity(self.vec_comms.len());
        for (comm, _dim) in self.vec_comms.iter() {
            xoff *= x;
            comm_V.push(comm.clone());
            scalar_V.push(xoff);
        }

        println!("xoff = {}, comm_V.len() = {}", xoff, comm_V.len());

        let proof_points = 
            comm_V.into_iter()
            .chain(iter::once(proof.A_I1))
            .chain(iter::once(proof.A_O1))
            .chain(iter::once(proof.S1))
            .chain(iter::once(proof.A_I2))
            .chain(iter::once(proof.A_O2))
            .chain(iter::once(proof.S2))
            .chain(self.V.iter().cloned())
            .chain(T_points.iter().cloned())
            .chain(proof.ipp_proof.L_vec.iter().cloned())
            .chain(proof.ipp_proof.R_vec.iter().cloned())
            .collect();

        let proof_scalars: Vec<C::ScalarField> = 
            scalar_V.into_iter()
            .chain(iter::once(xoff * x)) // A_I1
            .chain(iter::once(xoff * xx)) // A_O1
            .chain(iter::once(xoff * xxx)) // S1
            .chain(iter::once(u * x)) // A_I2
            .chain(iter::once(u * xx)) // A_O2
            .chain(iter::once(u * xxx)) // S2
            .chain(wV.iter().map(|wVi| *wVi * rxx)) // V
            .chain(T_scalars.iter().cloned()) // T_points
            .chain(u_sq.into_iter()) // ipp_proof.L_vec
            .chain(u_inv_sq.into_iter()) // ipp_proof.R_vec
            .collect::<Vec<_>>();

        let fixed_point_scalars: Vec<C::ScalarField> =
            iter::once(w * (proof.t_x - a * b) + r * (xx * (wc + delta) - proof.t_x)) // B
                .chain(iter::once(-proof.e_blinding - r * proof.t_x_blinding)) // B_blinding
                .chain(g_scalars) // G
                .chain(h_scalars) // H
                .collect::<Vec<_>>();

        Ok((proof_points, proof_scalars, fixed_point_scalars, padded_n))
    }
}

pub fn batch_verify<C: AffineCurve>(
    verification_tuples: Vec<(Vec<C>, Vec<C::ScalarField>, Vec<C::ScalarField>, usize)>,
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
) -> Result<(), R1CSError> {
    let mut rng = rand::thread_rng();
    let mut ver_iter = verification_tuples.into_iter();
    let (mut proof_points, mut proof_point_scalars, mut linear_combination, padded_n) =
        ver_iter.nth(0).unwrap();

    for (mut pp, ps, fps, _) in ver_iter {
        proof_points.append(&mut pp);

        // Sample random scalar
        let random_scalar = C::ScalarField::rand(&mut rng);

        // Multiply all scalars
        let ps = ps.into_iter().map(|s| s * random_scalar);
        let fps = fps.into_iter().map(|s| s * random_scalar);

        proof_point_scalars.append(&mut ps.collect());
        linear_combination = linear_combination
            .iter()
            .zip(fps)
            .map(|(a, b)| *a + b)
            .collect()
    }

    // We are performing a single-party circuit proof, so party index is 0.
    let gens = bp_gens.share(0);

    if bp_gens.gens_capacity < padded_n {
        return Err(R1CSError::InvalidGeneratorsLength);
    }

    use std::iter;
    let fixed_points = iter::once(pc_gens.B[0])
        .chain(iter::once(pc_gens.B_blinding))
        .chain(gens.G(padded_n).map(|&G_i| (G_i)))
        .chain(gens.H(padded_n).map(|&H_i| (H_i)));

    let mega_check: C::Projective = VariableBaseMSM::multi_scalar_mul(
        proof_points
            .into_iter()
            .chain(fixed_points)
            .collect::<Vec<_>>()
            .as_slice(),
        proof_point_scalars
            .into_iter()
            .chain(linear_combination)
            .map(|s| s.into())
            .collect::<Vec<_>>()
            .as_slice(),
    );

    if !mega_check.is_zero() {
        return Err(R1CSError::VerificationError);
    }

    Ok(())
}
