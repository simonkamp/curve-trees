use crate::curve_tree::{SelectAndRerandomizePath, SelectAndRerandomizePathWithDivisorComms};
use crate::curve_tree_prover::{
    CurveTreeWitnessPath, RootChildren, WitnessNode, WitnessPathsWithSameRoot,
};
use crate::error::{Error, Result};
use crate::parameters::SelRerandProofParametersRef;
use crate::select::{multi_select_public_set_ext_challenge, select, select_public_set};
use crate::utils::get_2_rngs_from_one;
use ark_dlog_gadget::dlog::{
    commit_witness_chunks_prover, create_divisor_and_decomposition,
    discrete_log_blinding_given_challenge, discrete_log_challenge, ChallengedGenerator,
    DiscreteLogChallenge, DiscreteLogParameters, DivisorComms, PointWithDlog,
};
use ark_dlog_gadget::utils::CurveSpec;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ec_divisors::util::GeneratorTable;
use ark_ec_divisors::DivisorCurve;
use ark_ff::{Field, PrimeField};
use ark_std::vec;
use ark_std::{boxed::Box, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Prover, Variable};
use bulletproofs::BulletproofGens;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_chacha::ChaChaRng;
use rand_core::CryptoRngCore;
use zeroize::Zeroize;

pub const VC_LEN: u16 = 256;

#[derive(Clone)]
pub enum RootDivisorComms<P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> {
    Even(DivisorComms<Affine<P0>>),
    Odd(DivisorComms<Affine<P1>>),
}

impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: DivisorCurve<BaseField = F1, ScalarField = F0> + Copy,
        P1: DivisorCurve<BaseField = F0, ScalarField = F1> + Copy,
    > CurveTreeWitnessPath<L, P0, P1>
{
    pub fn select_and_rerandomize_prover_gadget_new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &(impl SelRerandProofParametersRef<P0, P1, Parameters0, Parameters1> + Sync),
        rng: &mut R,
    ) -> Result<(SelectAndRerandomizePathWithDivisorComms<L, P0, P1>, F0)> {
        let even_parameters = parameters.even_parameters();
        let odd_parameters = parameters.odd_parameters();

        let (
            even_rerandomized_nodes,
            odd_rerandomized_nodes,
            mut even_rerandomization_scalars,
            mut odd_rerandomization_scalars,
            re_randomization_of_leaf,
        ) = self.randomize_nodes((even_parameters.pc_gens(), odd_parameters.pc_gens()), rng);

        let mut even_node_comms = vec![];
        let mut even_node_divisors = vec![];
        let mut odd_node_divisors = vec![];
        let mut odd_node_comms = vec![];
        let root_is_even = self.root_is_even();

        if root_is_even {
            let (x_var, y_var, x_rerand, y_rerand, divisor_comms, p) =
                Self::create_and_commit_divisor_for_root::<_, Parameters0>(
                    rng,
                    even_prover,
                    &self.even_internal_nodes[0],
                    &odd_rerandomized_nodes[0],
                    odd_rerandomization_scalars[0],
                    &odd_parameters.table_b_blinding,
                    &odd_parameters.sl_params.delta,
                    &even_parameters.sl_params.bp_gens,
                )?;
            even_node_divisors.push((x_var.into(), y_var.into(), x_rerand, y_rerand, p));
            even_node_comms.push(divisor_comms);
        } else {
            let (x_var, y_var, x_rerand, y_rerand, divisor_comms, p) =
                CurveTreeWitnessPath::<L, P1, P0>::create_and_commit_divisor_for_root::<
                    _,
                    Parameters1,
                >(
                    rng,
                    odd_prover,
                    &self.odd_internal_nodes[0],
                    &even_rerandomized_nodes[0],
                    even_rerandomization_scalars[0],
                    &even_parameters.table_b_blinding,
                    &even_parameters.sl_params.delta,
                    &odd_parameters.sl_params.bp_gens,
                )?;
            odd_node_divisors.push((x_var.into(), y_var.into(), x_rerand, y_rerand, p));
            odd_node_comms.push(divisor_comms);
        }

        let even_length = self.even_internal_nodes.len();
        let odd_length = self.odd_internal_nodes.len();

        let mut commit_even = |rng: &mut ChaChaRng| -> Result<()> {
            for i in 0..even_length {
                // Because root is already processed in the function called before this
                let index = if root_is_even { i + 1 } else { i };
                if self.even_internal_nodes.len() == index {
                    continue;
                }
                let (x_var, y_var, x_rerand, y_rerand, divisor_comms, p) =
                    Self::create_and_commit_divisor_for_non_root::<_, Parameters0>(
                        rng,
                        even_prover,
                        &self.even_internal_nodes[index],
                        &even_rerandomized_nodes[i],
                        even_rerandomization_scalars[i],
                        &odd_rerandomized_nodes[index],
                        odd_rerandomization_scalars[index],
                        &odd_parameters.table_b_blinding,
                        &odd_parameters.sl_params.delta,
                        &even_parameters.sl_params.bp_gens,
                    )?;
                even_node_comms.push(divisor_comms);
                even_node_divisors.push((x_var.into(), y_var.into(), x_rerand, y_rerand, p));
            }
            Ok(())
        };

        let mut commit_odd = |rng: &mut ChaChaRng| -> Result<()> {
            for i in 0..odd_length {
                // Because root is already processed in the function called before this
                let index = if !root_is_even { i + 1 } else { i };
                if self.odd_internal_nodes.len() == index {
                    continue;
                }
                let (x_var, y_var, x_rerand, y_rerand, divisor_comms, p) =
                    CurveTreeWitnessPath::<L, P1, P0>::create_and_commit_divisor_for_non_root::<
                        _,
                        Parameters1,
                    >(
                        rng,
                        odd_prover,
                        &self.odd_internal_nodes[index],
                        &odd_rerandomized_nodes[i],
                        odd_rerandomization_scalars[i],
                        &even_rerandomized_nodes[index],
                        even_rerandomization_scalars[index],
                        &even_parameters.table_b_blinding,
                        &even_parameters.sl_params.delta,
                        &odd_parameters.sl_params.bp_gens,
                    )?;
                odd_node_comms.push(divisor_comms);
                odd_node_divisors.push((x_var.into(), y_var.into(), x_rerand, y_rerand, p));
            }
            Ok(())
        };

        let (mut rng_even, mut rng_odd) = get_2_rngs_from_one(rng);

        #[cfg(not(feature = "parallel"))]
        {
            commit_even(&mut rng_even)?;
            commit_odd(&mut rng_odd)?;
        }

        #[cfg(feature = "parallel")]
        {
            let (even_result, odd_result) =
                rayon::join(|| commit_even(&mut rng_even), || commit_odd(&mut rng_odd));
            even_result?;
            odd_result?;
        }

        constraints_for_dlogs::<_, _, _, _, P0, P1, Parameters0, Parameters1>(
            even_prover,
            odd_prover,
            &even_parameters.table_b_blinding,
            &odd_parameters.table_b_blinding,
            even_node_divisors,
            odd_node_divisors,
        )?;

        Zeroize::zeroize(&mut odd_rerandomization_scalars);
        Zeroize::zeroize(&mut even_rerandomization_scalars);

        Ok((
            SelectAndRerandomizePathWithDivisorComms {
                path: SelectAndRerandomizePath {
                    odd_commitments: odd_rerandomized_nodes,
                    even_commitments: even_rerandomized_nodes,
                },
                even_divisor_comms: even_node_comms,
                odd_divisor_comms: odd_node_comms,
            },
            re_randomization_of_leaf,
        ))
    }

    fn create_and_commit_divisor_for_root<R: CryptoRngCore, Parameters: DiscreteLogParameters>(
        rng: &mut R,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        witness_node: &WitnessNode<L, P0, P1>,
        rerandomized_child: &Affine<P1>,
        randomization: F1,
        blinding_base_table: &GeneratorTable<F0, Parameters>,
        delta: &Affine<P1>,
        bp_gens: &BulletproofGens<Affine<P0>>,
    ) -> Result<(
        Variable<F0>,
        Variable<F0>,
        F0,
        F0,
        DivisorComms<Affine<P0>>,
        Box<PointWithDlog<F0, Parameters>>,
    )> {
        let child_node = witness_node.child_node_to_randomize;
        let all_x_coords = &witness_node.x_coord_children;
        let (x, y, x_rerand, yx_rerand) = select_root(
            prover,
            delta,
            rerandomized_child,
            all_x_coords,
            Some(child_node),
        )?;
        let (divisor_comms, p) = create_and_commit_divisor::<R, F0, F1, P0, P1, Parameters>(
            rng,
            prover,
            randomization,
            blinding_base_table,
            bp_gens,
        )?;
        Ok((x, y, x_rerand, yx_rerand, divisor_comms, p))
    }

    fn create_and_commit_divisor_for_non_root<
        R: CryptoRngCore,
        Parameters: DiscreteLogParameters,
    >(
        rng: &mut R,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        witness_node: &WitnessNode<L, P0, P1>,
        rerandomized_self: &Affine<P0>,
        self_randomization: F0,
        rerandomized_child: &Affine<P1>,
        child_randomization: F1,
        blinding_base_table: &GeneratorTable<F0, Parameters>,
        delta: &Affine<P1>,
        bp_gens: &BulletproofGens<Affine<P0>>,
    ) -> Result<(
        Variable<F0>,
        Variable<F0>,
        F0,
        F0,
        DivisorComms<Affine<P0>>,
        Box<PointWithDlog<F0, Parameters>>,
    )> {
        let (x_var, y_var, x, y) = witness_node.single_level_select(
            prover,
            delta,
            rerandomized_self,
            self_randomization,
            rerandomized_child,
        )?;
        let (divisor_comms, p) = create_and_commit_divisor::<_, F0, F1, P0, P1, Parameters>(
            rng,
            prover,
            child_randomization,
            blinding_base_table,
            bp_gens,
        )?;
        Ok((x_var, y_var, x, y, divisor_comms, p))
    }
}

impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > WitnessNode<L, P0, P1>
{
    pub fn single_level_select(
        &self,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        delta: &Affine<P1>,
        self_node_rerandomized: &Affine<P0>,
        self_rerandomization_scalar: P0::ScalarField,
        rerandomized_child: &Affine<P1>,
    ) -> Result<(Variable<F0>, Variable<F0>, F0, F0)> {
        // In this case this (`self`) is a non-root inner node and the children (and the scalar used for rerandomizing) are part of the witness.
        // Allocate variables for x-coordinates (which are committed in `self_node_rerandomized`) of child nodes with `self_rerandomization_scalar` as the blinding
        let children = prover
            .vars_for_committed_vec(
                self_node_rerandomized,
                &self.x_coord_children,
                self_rerandomization_scalar,
            )
            .iter()
            .map(|var| LinearCombination::<P0::ScalarField>::from(*var))
            .collect();

        select_non_root(
            prover,
            delta,
            rerandomized_child,
            children,
            Some(self.child_node_to_randomize),
        )
    }
}

impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: DivisorCurve<BaseField = F1, ScalarField = F0> + Copy,
        P1: DivisorCurve<BaseField = F0, ScalarField = F1> + Copy,
    > WitnessPathsWithSameRoot<L, P0, P1>
{
    pub fn select_and_rerandomize_prover_gadget_new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        even_prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<P1>>,
        parameters: &(impl SelRerandProofParametersRef<P0, P1, Parameters0, Parameters1> + Sync),
        rng: &mut R,
    ) -> Result<(
        Vec<SelectAndRerandomizePathWithDivisorComms<L, P0, P1>>,
        Vec<F0>,
    )> {
        let even_parameters = parameters.even_parameters();
        let odd_parameters = parameters.odd_parameters();

        let num_paths = self.num_paths();
        let individual_paths = self.to_individual_paths();

        // Determine if root is even based on the RootChildren variant
        let root_is_even = matches!(&self.root_children, RootChildren::Even { .. });

        // Collect all randomized nodes and scalars for each path
        let mut all_even_rerandomized_nodes = Vec::with_capacity(num_paths);
        let mut all_odd_rerandomized_nodes = Vec::with_capacity(num_paths);
        let mut all_even_rerandomization_scalars = Vec::with_capacity(num_paths);
        let mut all_odd_rerandomization_scalars = Vec::with_capacity(num_paths);
        let mut all_leaf_rerandomizations = Vec::with_capacity(num_paths);

        for path in &individual_paths {
            let (
                even_rerandomized_nodes,
                odd_rerandomized_nodes,
                even_rerandomization_scalars,
                odd_rerandomization_scalars,
                re_randomization_of_leaf,
            ) = path.randomize_nodes((even_parameters.pc_gens(), odd_parameters.pc_gens()), rng);

            all_even_rerandomized_nodes.push(even_rerandomized_nodes);
            all_odd_rerandomized_nodes.push(odd_rerandomized_nodes);
            all_even_rerandomization_scalars.push(even_rerandomization_scalars);
            all_odd_rerandomization_scalars.push(odd_rerandomization_scalars);
            all_leaf_rerandomizations.push(re_randomization_of_leaf);
        }

        // Process root level - x-coords are allocated once, but each path has its own divisor proof

        let mut even_node_comms = Vec::with_capacity(num_paths);
        let mut even_node_divisors = Vec::with_capacity(num_paths);
        let mut odd_node_divisors = Vec::with_capacity(num_paths);
        let mut odd_node_comms = Vec::with_capacity(num_paths);

        match &self.root_children {
            RootChildren::Even {
                x_coords,
                child_nodes_to_randomize,
            } => {
                let delta = odd_parameters.sl_params.delta;
                let bp_gens = &even_parameters.sl_params.bp_gens;

                Self::create_and_commit_divisor_for_root::<_, Parameters0>(
                    rng,
                    even_prover,
                    x_coords,
                    child_nodes_to_randomize,
                    &all_odd_rerandomized_nodes,
                    &all_odd_rerandomization_scalars,
                    &mut even_node_comms,
                    &mut even_node_divisors,
                    delta,
                    bp_gens,
                    &odd_parameters.table_b_blinding,
                )?;
            }
            RootChildren::Odd {
                x_coords,
                child_nodes_to_randomize,
            } => {
                let delta = even_parameters.sl_params.delta;
                let bp_gens = &odd_parameters.sl_params.bp_gens;

                WitnessPathsWithSameRoot::<L, P1, P0>::create_and_commit_divisor_for_root::<
                    _,
                    Parameters1,
                >(
                    rng,
                    odd_prover,
                    x_coords,
                    child_nodes_to_randomize,
                    &all_even_rerandomized_nodes,
                    &all_even_rerandomization_scalars,
                    &mut odd_node_comms,
                    &mut odd_node_divisors,
                    delta,
                    bp_gens,
                    &even_parameters.table_b_blinding,
                )?;
            }
        }

        // Process non-root nodes for each path

        for path_idx in 0..num_paths {
            let path = &individual_paths[path_idx];
            let even_length = path.even_internal_nodes.len();
            let odd_length = path.odd_internal_nodes.len();
            let even_rerandomized_nodes = &all_even_rerandomized_nodes[path_idx];
            let odd_rerandomized_nodes = &all_odd_rerandomized_nodes[path_idx];
            let even_rerandomization_scalars = &all_even_rerandomization_scalars[path_idx];
            let odd_rerandomization_scalars = &all_odd_rerandomization_scalars[path_idx];

            if even_node_comms.len() <= path_idx {
                even_node_comms.push(Vec::new());
                even_node_divisors.push(Vec::new());
            }
            if odd_node_comms.len() <= path_idx {
                odd_node_comms.push(Vec::new());
                odd_node_divisors.push(Vec::new());
            }

            // Process even non-root nodes
            for i in 0..even_length {
                let index = if root_is_even { i + 1 } else { i };
                if path.even_internal_nodes.len() == index {
                    continue;
                }
                let (x_var, y_var, x, y, divisor_comms, p) =
                    CurveTreeWitnessPath::<L, P0, P1>::create_and_commit_divisor_for_non_root::<
                        _,
                        Parameters0,
                    >(
                        rng,
                        even_prover,
                        &path.even_internal_nodes[index],
                        &even_rerandomized_nodes[i],
                        even_rerandomization_scalars[i],
                        &odd_rerandomized_nodes[index],
                        odd_rerandomization_scalars[index],
                        &odd_parameters.table_b_blinding,
                        &odd_parameters.sl_params.delta,
                        &even_parameters.sl_params.bp_gens,
                    )?;
                even_node_comms[path_idx].push(divisor_comms);
                even_node_divisors[path_idx].push((x_var.into(), y_var.into(), x, y, p));
            }

            // Process odd non-root nodes
            for i in 0..odd_length {
                let index = if !root_is_even { i + 1 } else { i };
                if path.odd_internal_nodes.len() == index {
                    continue;
                }
                let (x_var, y_var, x, y, divisor_comms, p) =
                    CurveTreeWitnessPath::<L, P1, P0>::create_and_commit_divisor_for_non_root::<
                        _,
                        Parameters1,
                    >(
                        rng,
                        odd_prover,
                        &path.odd_internal_nodes[index],
                        &odd_rerandomized_nodes[i],
                        odd_rerandomization_scalars[i],
                        &even_rerandomized_nodes[index],
                        even_rerandomization_scalars[index],
                        &even_parameters.table_b_blinding,
                        &even_parameters.sl_params.delta,
                        &odd_parameters.sl_params.bp_gens,
                    )?;
                odd_node_comms[path_idx].push(divisor_comms);
                odd_node_divisors[path_idx].push((x_var.into(), y_var.into(), x, y, p));
            }
        }

        constraints_for_dlogs::<_, _, _, _, P0, P1, Parameters0, Parameters1>(
            even_prover,
            odd_prover,
            &even_parameters.table_b_blinding,
            &odd_parameters.table_b_blinding,
            even_node_divisors.into_iter().flatten(),
            odd_node_divisors.into_iter().flatten(),
        )?;

        let mut result_paths = Vec::with_capacity(num_paths);
        for (odd, even) in all_odd_rerandomized_nodes
            .into_iter()
            .zip(all_even_rerandomized_nodes)
        {
            result_paths.push(SelectAndRerandomizePathWithDivisorComms {
                path: SelectAndRerandomizePath {
                    odd_commitments: odd,
                    even_commitments: even,
                },
                even_divisor_comms: even_node_comms.remove(0),
                odd_divisor_comms: odd_node_comms.remove(0),
            });
        }

        Ok((result_paths, all_leaf_rerandomizations))
    }

    fn create_and_commit_divisor_for_root<R: CryptoRngCore, Parameters: DiscreteLogParameters>(
        rng: &mut R,
        prover: &mut Prover<MerlinTranscript, Affine<P0>>,
        x_coords: &[F0],
        child_nodes_to_randomize: &[Affine<P1>],
        all_rerandomized_nodes: &[Vec<Affine<P1>>],
        all_rerandomization_scalars: &[Vec<F1>],
        node_comms: &mut Vec<Vec<DivisorComms<Affine<P0>>>>,
        node_divisors: &mut Vec<
            Vec<(
                LinearCombination<F0>,
                LinearCombination<F0>,
                F0,
                F0,
                Box<PointWithDlog<F0, Parameters>>,
            )>,
        >,
        delta: Affine<P1>,
        bp_gens: &BulletproofGens<Affine<P0>>,
        table: &GeneratorTable<F0, Parameters>,
    ) -> Result<()> {
        // Each path's selected child + delta
        let children_plus_delta: Vec<Affine<P1>> = child_nodes_to_randomize
            .iter()
            .map(|c| (*c + delta).into_affine())
            .collect();

        // Allocate x-coordinates for all selected children and enforce set membership
        let x_vars: Vec<LinearCombination<F0>> = children_plus_delta
            .iter()
            .map(|c| prover.allocate(Some(c.x)).unwrap().into())
            .collect();

        // Get challenge and enforce multi-select on public set
        let challenge = prover
            .transcript()
            .challenge_scalar(b"challenge-for-multi_select");
        multi_select_public_set_ext_challenge(prover, x_vars.clone(), x_coords, challenge)?;

        // For each path, create divisor proof for its selected child of root
        for (path_idx, (x_var, child)) in x_vars
            .into_iter()
            .zip(children_plus_delta.into_iter())
            .enumerate()
        {
            let rerandomized_child = &all_rerandomized_nodes[path_idx][0];
            let randomization = all_rerandomization_scalars[path_idx][0];

            // Add rerandomized child to transcript
            prover
                .transcript()
                .append(b"rerandomized_child", rerandomized_child);

            let y_var: LinearCombination<F0> = prover.allocate(Some(child.y))?.into();
            let (x, y) = (*rerandomized_child + delta)
                .into_affine()
                .xy()
                .ok_or_else(|| Error::PointCantBeZero)?;

            // Create divisor and commit
            let (divisor_comms, p) = create_and_commit_divisor::<_, F0, F1, P0, P1, Parameters>(
                rng,
                prover,
                randomization,
                table,
                bp_gens,
            )?;

            node_comms.push(vec![divisor_comms]);
            node_divisors.push(vec![(x_var, y_var, x, y, p)]);
        }
        Ok(())
    }
}

pub fn select_root<
    Fb: PrimeField,
    Fs: Field,
    C2: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Cs: ConstraintSystem<Fs>,
>(
    cs: &mut Cs, // Prover or verifier
    delta: &Affine<C2>,
    rerandomized_child: &Affine<C2>, // The public rerandomization of the selected child without Delta
    all_children_plus_delta: &[Fs],  // Public set of x-coordinates of all children plus delta
    child: Option<Affine<C2>>,       // Witness of the selected child
) -> Result<(Variable<Fs>, Variable<Fs>, Fs, Fs)> {
    // Add the re-randomised child to the transcript
    cs.transcript()
        .append(b"rerandomized_child", &rerandomized_child);

    let delta = delta.into_group();
    // Show that child is part of `all_children` by showing that the child's x-coordinate is present in x-coordinates of the all children
    let child_plus_delta = child.map(|c| (c + delta).into_affine());
    let x = cs.allocate(child_plus_delta.map(|xy| xy.x))?;
    let y = cs.allocate(child_plus_delta.map(|xy| xy.y))?;
    let x_lc: LinearCombination<_> = x.into();
    select_public_set(cs, x_lc.clone(), all_children_plus_delta)?;
    let (x_rerand, y_rerand) = (*rerandomized_child + delta)
        .into_affine()
        .xy()
        .ok_or_else(|| Error::PointCantBeZero)?;
    Ok((x, y, x_rerand, y_rerand))
}

pub fn select_non_root<
    Fb: PrimeField,
    Fs: Field,
    C2: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Cs: ConstraintSystem<Fs>,
>(
    cs: &mut Cs, // Prover or verifier
    delta: &Affine<C2>,
    rerandomized_child: &Affine<C2>, // The public rerandomization of the selected child without Delta
    all_children_plus_delta: Vec<LinearCombination<Fs>>, // Public set of x-coordinates of all children plus delta
    child: Option<Affine<C2>>,                           // Witness of the selected child
) -> Result<(Variable<Fs>, Variable<Fs>, Fs, Fs)> {
    // Add the re-randomised child to the transcript
    cs.transcript()
        .append(b"rerandomized_child", &rerandomized_child);

    let delta = delta.into_group();
    // Show that child is part of `all_children` by showing that the child's x-coordinate is present in x-coordinates of the all children
    let child_plus_delta = child.map(|c| (c + delta).into_affine());
    let x = cs.allocate(child_plus_delta.map(|xy| xy.x))?;
    let y = cs.allocate(child_plus_delta.map(|xy| xy.y))?;
    let x_lc: LinearCombination<_> = x.into();
    select(cs, x_lc.clone(), all_children_plus_delta.iter().cloned())?;
    let (x_rerand, y_rerand) = (*rerandomized_child + delta)
        .into_affine()
        .xy()
        .ok_or_else(|| Error::PointCantBeZero)?;
    Ok((x, y, x_rerand, y_rerand))
}

pub type DlogItem<F, Params> = (
    LinearCombination<F>,
    LinearCombination<F>,
    F,
    F,
    Box<PointWithDlog<F, Params>>,
);

/// Enum for single root item case (single-path prover/verifier, batched prover/verifier)
pub enum RootDlogItem<
    F0: PrimeField,
    F1: PrimeField,
    Params0: DiscreteLogParameters,
    Params1: DiscreteLogParameters,
> {
    Even(DlogItem<F0, Params0>),
    Odd(DlogItem<F1, Params1>),
}

/// Enum for multiple root items case (multi-path with same root)
pub enum RootDlogItems<
    'a,
    F0: PrimeField,
    F1: PrimeField,
    Params0: DiscreteLogParameters,
    Params1: DiscreteLogParameters,
> {
    Even(&'a [DlogItem<F0, Params0>]),
    Odd(&'a [DlogItem<F1, Params1>]),
}

/// Generates challenges and applies discrete log blinding for a single root item case.
/// Used by single-path and batched prover/verifier gadgets.
pub fn constraints_for_dlogs<
    F0: PrimeField,
    F1: PrimeField,
    Cs0: ConstraintSystem<F0>,
    Cs1: ConstraintSystem<F1>,
    P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
    P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    Params0: DiscreteLogParameters,
    Params1: DiscreteLogParameters,
>(
    cs_even: &mut Cs0,
    cs_odd: &mut Cs1,
    table_even: &GeneratorTable<F1, Params1>,
    table_odd: &GeneratorTable<F0, Params0>,
    even_node_items: impl IntoIterator<Item = DlogItem<F0, Params0>>,
    odd_node_items: impl IntoIterator<Item = DlogItem<F1, Params1>>,
) -> Result<()> {
    let curve_spec_even = CurveSpec::<F0> {
        a: P1::COEFF_A,
        b: P1::COEFF_B,
    };
    let curve_spec_odd = CurveSpec::<F1> {
        a: P0::COEFF_A,
        b: P0::COEFF_B,
    };
    let (challenge_even, challenge_gen_even) = challenge(cs_even, &curve_spec_even, table_odd)?;
    let (challenge_odd, challenge_gen_odd) = challenge(cs_odd, &curve_spec_odd, table_even)?;

    // Apply blinding to even node and leaf items
    for (x_var, y_var, x, y, p) in even_node_items {
        discrete_log_blinding_given_challenge(
            cs_even,
            (x_var, y_var),
            *p,
            (x, y),
            &curve_spec_even,
            &challenge_even,
            &challenge_gen_even,
        );
    }

    // Apply blinding to odd node and leaf items
    for (x_var, y_var, x, y, p) in odd_node_items {
        discrete_log_blinding_given_challenge(
            cs_odd,
            (x_var, y_var),
            *p,
            (x, y),
            &curve_spec_odd,
            &challenge_odd,
            &challenge_gen_odd,
        );
    }
    Ok(())
}

pub fn challenge<F: PrimeField, Cs: ConstraintSystem<F>, Params: DiscreteLogParameters>(
    cs: &mut Cs,
    curve: &CurveSpec<F>,
    table: &GeneratorTable<F, Params>,
) -> Result<(
    DiscreteLogChallenge<F, Params>,
    ChallengedGenerator<F, Params>,
)> {
    let (challenge, challenged_generators) = discrete_log_challenge(cs, curve, &[table])?;
    let mut challenged_generators = challenged_generators.into_iter();
    let challeng_gen = challenged_generators.next().unwrap();
    Ok((challenge, challeng_gen))
}

pub fn create_and_commit_divisor<
    R: CryptoRngCore,
    F0: PrimeField,
    F1: PrimeField,
    C0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
    C1: DivisorCurve<BaseField = F0, ScalarField = F1> + Copy,
    Params: DiscreteLogParameters,
>(
    rng: &mut R,
    prover: &mut Prover<MerlinTranscript, Affine<C0>>,
    randomization: F1,
    blinding_base_table: &GeneratorTable<F0, Params>,
    bp_gens: &BulletproofGens<Affine<C0>>,
) -> Result<(DivisorComms<Affine<C0>>, Box<PointWithDlog<F0, Params>>)> {
    let (divisor_commitments, o_blind_claim) = {
        // Optimz: All divisors could be computed in parallel. And creating multiple divisors at once is faster
        let witness = create_divisor_and_decomposition::<F0, C1, Params>(
            blinding_base_table,
            -randomization,
        )?;
        let (divisor_commitments, _, vars_divisor) =
            commit_witness_chunks_prover(rng, prover, &witness, VC_LEN as usize, bp_gens)?;

        (divisor_commitments, vars_divisor)
    };
    Ok((divisor_commitments, o_blind_claim))
}
