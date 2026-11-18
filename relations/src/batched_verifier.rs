use crate::batched_prover::{
    accumulate_selected_children, batched_select_and_accumulate_non_root,
    batched_select_and_accumulate_root,
};
use crate::curve_tree::{Root, SelectAndRerandomizeMultiPathWithDivisorComms};
use crate::error::{Error, Result};
use crate::parameters::SelRerandProofParametersRef;
use crate::prover::{constraints_for_dlogs, constraints_for_dlogs_presummed, DlogItem};
use crate::select::{multi_select_public_set, select, select_public_set};
use crate::verifier::commit_dlog_and_divisor;
use ark_dlog_gadget::dlog::{DiscreteLogParameters, DivisorComms};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_std::{format, string::ToString, vec, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Variable, Verifier};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};

impl<
        const L: usize,
        const M: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy + Send,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy + Send,
    > SelectAndRerandomizeMultiPathWithDivisorComms<L, M, P0, P1>
{
    /// Divisor-based batched select and rerandomize verifier gadget.
    pub fn batched_select_and_rerandomize_verifier_gadget<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        root: &Root<L, M, P0, P1>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<P1>>,
        parameters: &(impl SelRerandProofParametersRef<P0, P1, Parameters0, Parameters1> + Sync),
    ) -> Result<()> {
        self.check_lengths_for_root_and_width_of_path(root)?;

        let even_parameters = parameters.even_parameters();
        let odd_parameters = parameters.odd_parameters();

        let num_indices_usize = self.path.selected_commitments.len();
        let num_indices = num_indices_usize as u32;

        let mut even_node_divisors = Vec::new();
        let mut odd_node_divisors = Vec::new();
        // Leaf items kept separate from the summed items for the height > 1 path (see constraints_for_dlogs_presummed).
        let mut odd_leaf_divisors = Vec::new();

        // In a tree of height 1, the root is itself the parent of the leaves, so select each leaf
        // directly from the public root x-coords.
        if root.height() == 1 {
            let root_node = match root {
                Root::Odd(root_node) => root_node,
                Root::Even(_) => {
                    return Err(Error::MalformedProofInput(
                        "an even root cannot be the parent of leaves".to_string(),
                    ))
                }
            };
            for i in 0..num_indices_usize {
                let x_coords = root_node.x_coord_children.get(i).ok_or_else(|| {
                    Error::MalformedProofInput(format!(
                        "root x_coord_children shorter than selected indices (index {i}, len {})",
                        root_node.x_coord_children.len()
                    ))
                })?;
                let selected_commitment =
                    self.path.selected_commitments.get(i).ok_or_else(|| {
                        Error::MalformedProofInput(format!(
                            "selected_commitments shorter than selected indices (index {i}, len {})",
                            self.path.selected_commitments.len()
                        ))
                    })?;
                let leaf_divisor = self.odd_divisor_comms.get(i).ok_or_else(|| {
                    Error::MalformedProofInput(format!(
                        "missing leaf divisor commitment for selected index {i} (len {})",
                        self.odd_divisor_comms.len()
                    ))
                })?;
                let item = Self::verify_leaf::<Parameters1>(
                    odd_verifier,
                    LeafParent::Root(x_coords.as_slice()),
                    selected_commitment,
                    &even_parameters.sl_params.delta,
                    leaf_divisor,
                )?;
                odd_node_divisors.push(item);
            }

            return constraints_for_dlogs::<_, _, _, _, P0, P1, Parameters0, Parameters1>(
                even_verifier,
                odd_verifier,
                &even_parameters.table_b_blinding,
                &odd_parameters.table_b_blinding,
                even_node_divisors,
                odd_node_divisors,
            );
        }

        // For height > 1
        let root_is_even = match root {
            Root::Even(root_node) => {
                let item = Self::verify_batched_root_on_curve::<Parameters0>(
                    even_verifier,
                    num_indices,
                    &root_node.x_coord_children,
                    &self.path.odd_commitments,
                    &self.even_divisor_comms,
                    &odd_parameters.sl_params.delta,
                )?;
                even_node_divisors.push(item);
                true
            }
            Root::Odd(root_node) => {
                let item = SelectAndRerandomizeMultiPathWithDivisorComms::<L, M, P1, P0>::verify_batched_root_on_curve::<
                    Parameters1,
                >(
                    odd_verifier,
                    num_indices,
                    &root_node.x_coord_children,
                    &self.path.even_commitments,
                    &self.odd_divisor_comms,
                    &even_parameters.sl_params.delta,
                )?;
                odd_node_divisors.push(item);
                false
            }
        };

        // Process the non-root levels.
        let even_items = Self::verify_batched_non_root_on_curve::<Parameters0>(
            even_verifier,
            root_is_even,
            self.path.even_commitments.len(),
            num_indices,
            &self.path.even_commitments,
            &self.path.odd_commitments,
            &self.even_divisor_comms,
            &odd_parameters.sl_params.delta,
        )?;
        even_node_divisors.extend(even_items);

        let odd_non_root_len = self.path.odd_commitments.len().saturating_sub(1);
        let odd_items = SelectAndRerandomizeMultiPathWithDivisorComms::<L, M, P1, P0>::verify_batched_non_root_on_curve::<
            Parameters1,
        >(
            odd_verifier,
            !root_is_even,
            odd_non_root_len,
            num_indices,
            &self.path.odd_commitments,
            &self.path.even_commitments,
            &self.odd_divisor_comms,
            &even_parameters.sl_params.delta,
        )?;
        odd_node_divisors.extend(odd_items);

        // Process leaf level - individual verification for each leaf
        {
            let odd_length = self.path.odd_commitments.len();
            let parent_index = odd_length.checked_sub(1).ok_or_else(|| {
                Error::MalformedProofInput(
                    "odd_commitments must contain at least one element for leaf verification"
                        .to_string(),
                )
            })?;

            // Commit to parent to get variables

            let parent_commitment =
                self.path.odd_commitments.get(parent_index).ok_or_else(|| {
                    Error::MalformedProofInput(format!(
                        "odd_commitments shorter than required for leaf verification (index {parent_index}, len {})",
                        self.path.odd_commitments.len()
                    ))
                })?;
            let children_vars: Vec<Variable<F1>> =
                odd_verifier.commit_vec(L * num_indices as usize, *parent_commitment);
            if children_vars.len() % num_indices_usize != 0 {
                return Err(Error::MalformedProofInput(
                    "leaf parent commitment does not split evenly across selected indices"
                        .to_string(),
                ));
            }
            let chunk_size = children_vars.len() / num_indices_usize;
            if chunk_size == 0 {
                return Err(Error::MalformedProofInput(
                    "leaf parent commitment produced empty chunks".to_string(),
                ));
            }
            let chunks: Vec<_> = children_vars.chunks_exact(chunk_size).collect();

            let leaf_divisor_start = self
                .odd_divisor_comms
                .len()
                .checked_sub(num_indices_usize)
                .ok_or_else(|| {
                    Error::MalformedProofInput(format!(
                        "odd_divisor_comms shorter than selected indices for leaf verification (len {}, num_indices {num_indices_usize})",
                        self.odd_divisor_comms.len()
                    ))
                })?;

            for (i, chunk) in chunks.iter().enumerate() {
                let selected_commitment =
                    self.path.selected_commitments.get(i).ok_or_else(|| {
                        Error::MalformedProofInput(format!(
                            "selected_commitments shorter than inferred leaf chunks (index {i}, len {})",
                            self.path.selected_commitments.len()
                        ))
                    })?;
                let leaf_divisor = self
                    .odd_divisor_comms
                    .get(leaf_divisor_start + i)
                    .ok_or_else(|| {
                        Error::MalformedProofInput(format!(
                            "missing leaf divisor commitment for selected index {} (len {})",
                            leaf_divisor_start + i,
                            self.odd_divisor_comms.len()
                        ))
                    })?;
                let item = Self::verify_leaf::<Parameters1>(
                    odd_verifier,
                    LeafParent::NonRoot(chunk.iter().map(|v| (*v).into()).collect()),
                    selected_commitment,
                    &even_parameters.sl_params.delta,
                    leaf_divisor,
                )?;
                odd_leaf_divisors.push(item);
            }
        }

        constraints_for_dlogs_presummed::<_, _, _, _, P0, P1, Parameters0, Parameters1>(
            even_verifier,
            odd_verifier,
            &even_parameters.table_b_blinding,
            &odd_parameters.table_b_blinding,
            even_node_divisors,
            odd_node_divisors,
            odd_leaf_divisors,
        )?;

        Ok(())
    }

    /// Enforce membership checks for each selected child and sum the children and create divisor
    fn verify_batched_root_on_curve<Parameters: DiscreteLogParameters>(
        verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        num_indices: u32,
        root_x_coords: &[[F0; L]],
        child_commitments: &[Affine<P1>],
        divisor_comms: &[DivisorComms<Affine<P0>>],
        child_delta: &Affine<P1>,
    ) -> Result<DlogItem<F0, Parameters>> {
        // x-coordinates of all children of all the roots
        let mut all_x_coords: Vec<F0> = Vec::with_capacity(L * num_indices as usize);
        for i in 0..num_indices as usize {
            let x_coords = root_x_coords.get(i).ok_or_else(|| {
                Error::MalformedProofInput(format!(
                    "root x_coord_children shorter than selected indices (index {i}, len {})",
                    root_x_coords.len()
                ))
            })?;
            all_x_coords.extend_from_slice(x_coords.as_slice());
        }

        // Do membership check on root's children's x-coords and get the sum of selected children
        let (sum_x_var, sum_y_var) = batched_select_and_accumulate_root::<F0, P1, _>(
            verifier,
            num_indices,
            &all_x_coords,
            None,
        )?;

        let root_child = child_commitments.first().ok_or_else(|| {
            Error::MalformedProofInput("missing root child commitment".to_string())
        })?;
        let shifted_rerandomized =
            (*root_child + (*child_delta * P1::ScalarField::from(num_indices))).into_affine();
        let (x, y) = shifted_rerandomized.xy().ok_or(Error::PointCantBeZero)?;

        let divisor = divisor_comms.first().ok_or_else(|| {
            Error::MalformedProofInput("missing root divisor commitment".to_string())
        })?;
        let p = commit_dlog_and_divisor::<_, _, Parameters>(verifier, divisor)?;
        Ok((sum_x_var, sum_y_var, x, y, p))
    }

    /// Enforce for each of the first `num_parent_levels` `parent_commitments`, corresponding
    /// `child_commitments` is a child of the parent and the divisor check on the sum of the children
    /// holds. `skip_root` is true when the root lives on this parity
    fn verify_batched_non_root_on_curve<Parameters: DiscreteLogParameters>(
        verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        skip_root: bool,
        num_parent_levels: usize,
        num_indices: u32,
        parent_commitments: &[Affine<P0>],
        child_commitments: &[Affine<P1>],
        divisor_comms: &[DivisorComms<Affine<P0>>],
        child_delta: &Affine<P1>,
    ) -> Result<Vec<DlogItem<F0, Parameters>>> {
        let mut items = Vec::with_capacity(num_parent_levels);
        let child_delta_scaled = *child_delta * P1::ScalarField::from(num_indices);
        for parent_index in 0..num_parent_levels {
            let child_index = if skip_root {
                parent_index + 1
            } else {
                parent_index
            };

            let parent_commitment = parent_commitments.get(parent_index).ok_or_else(|| {
                Error::MalformedProofInput(format!(
                    "parent commitments shorter than required for traversal (index {parent_index}, len {})",
                    parent_commitments.len()
                ))
            })?;
            let child_commitment = child_commitments.get(child_index).ok_or_else(|| {
                Error::MalformedProofInput(format!(
                    "child commitments shorter than required for traversal (index {child_index}, len {})",
                    child_commitments.len()
                ))
            })?;
            let divisor = divisor_comms.get(child_index).ok_or_else(|| {
                Error::MalformedProofInput(format!(
                    "divisor commitments shorter than required for traversal (index {child_index}, len {})",
                    divisor_comms.len()
                ))
            })?;

            // Do membership check on node's children's x-coords and get the sum of selected children
            let children_vars: Vec<LinearCombination<F0>> = verifier
                .commit_vec(L * num_indices as usize, *parent_commitment)
                .into_iter()
                .map(|v| v.into())
                .collect();
            let (sum_x_var, sum_y_var) = batched_select_and_accumulate_non_root::<F0, P1, _>(
                verifier,
                num_indices,
                children_vars,
                None,
            )?;

            let shifted_rerandomized = (*child_commitment + child_delta_scaled).into_affine();
            let (x, y) = shifted_rerandomized.xy().ok_or(Error::PointCantBeZero)?;

            let p = commit_dlog_and_divisor::<_, _, Parameters>(verifier, divisor)?;
            items.push((sum_x_var, sum_y_var, x, y, p));
        }
        Ok(items)
    }

    /// Enforce membership of leaf's x-coord and create and commit its divisor vars
    fn verify_leaf<Parameters1: DiscreteLogParameters>(
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<P1>>,
        children: LeafParent<F1>,
        selected_commitment: &Affine<P0>,
        leaf_delta: &Affine<P0>,
        leaf_divisor: &DivisorComms<Affine<P1>>,
    ) -> Result<DlogItem<F1, Parameters1>> {
        let x_var: LinearCombination<F1> = odd_verifier.allocate(None)?.into();
        let y_var: LinearCombination<F1> = odd_verifier.allocate(None)?.into();
        match children {
            LeafParent::Root(xs) => select_public_set(odd_verifier, x_var.clone(), xs)?,
            LeafParent::NonRoot(lcs) => select(odd_verifier, x_var.clone(), lcs.into_iter())?,
        }
        odd_verifier
            .transcript()
            .append(b"rerandomized_child", selected_commitment);
        let rerandomized_plus_delta = (*selected_commitment + *leaf_delta).into_affine();
        let (x, y) = rerandomized_plus_delta.xy().ok_or(Error::PointCantBeZero)?;
        let p = commit_dlog_and_divisor::<_, _, Parameters1>(odd_verifier, leaf_divisor)?;
        Ok((x_var, y_var, x, y, p))
    }

    /// Verify the shared root of several batched multi-paths at once - one check per root.
    /// And then enforce one divisor check per multi-path on the sum of the children
    fn verify_shared_root_for_multi_paths<Parameters: DiscreteLogParameters>(
        verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        root_x_coords: &[[F0; L]],
        num_leaves_per_mp: &[usize],
        rerandomized_sums: &[Affine<P1>],
        root_divisors: &[&DivisorComms<Affine<P0>>],
        child_delta: &Affine<P1>,
    ) -> Result<Vec<DlogItem<F0, Parameters>>> {
        let num_multi_paths = num_leaves_per_mp.len();
        let max_leaves_mp = num_leaves_per_mp.iter().copied().max().unwrap_or(0);

        // Membership check per root. Collect the child x-vars per root and then do its membership
        // check. This means there are at most M (multi-set) checks regardless of the total number
        // of children
        let mut x_vars_per_mp: Vec<Vec<LinearCombination<F0>>> = vec![Vec::new(); num_multi_paths];
        for root_idx in 0..max_leaves_mp {
            let mut xs = Vec::new();
            for (mp_idx, &num_indices) in num_leaves_per_mp.iter().enumerate() {
                if root_idx < num_indices {
                    let x_lc: LinearCombination<F0> = verifier.allocate(None).unwrap().into();
                    xs.push(x_lc.clone());
                    x_vars_per_mp[mp_idx].push(x_lc);
                }
            }
            let x_coords = root_x_coords.get(root_idx).ok_or_else(|| {
                Error::MalformedProofInput(format!(
                    "root x_coord_children shorter than selected indices (index {root_idx}, len {})",
                    root_x_coords.len()
                ))
            })?;
            multi_select_public_set(verifier, xs.clone(), x_coords.as_slice())?;
        }

        // Per multi-path - sum its selected children and allocate a divisor for the rerandomized sum.
        let mut items = Vec::with_capacity(num_multi_paths);
        for i in 0..num_multi_paths {
            let (sum_x, sum_y) =
                accumulate_selected_children::<F0, P1, _>(verifier, &x_vars_per_mp[i], None)?;
            let shifted = (rerandomized_sums[i]
                + (*child_delta * P1::ScalarField::from(num_leaves_per_mp[i] as u64)))
            .into_affine();
            let (x, y) = shifted.xy().ok_or(Error::PointCantBeZero)?;
            let p = commit_dlog_and_divisor::<_, _, Parameters>(verifier, root_divisors[i])?;
            items.push((sum_x, sum_y, x, y, p));
        }
        Ok(items)
    }

    /// Divisor-based batched select and rerandomize verifier gadget for several batched multi-paths
    /// sharing a common root.
    pub fn batched_select_and_rerandomize_verifier_gadget_multi<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        paths: &[Self],
        root: &Root<L, M, P0, P1>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<P1>>,
        parameters: &(impl SelRerandProofParametersRef<P0, P1, Parameters0, Parameters1> + Sync),
    ) -> Result<()> {
        let even_parameters = parameters.even_parameters();
        let odd_parameters = parameters.odd_parameters();

        let num_multi_paths = paths.len();
        if num_multi_paths == 0 {
            return Err(Error::NeedNonZeroNumberOfPaths);
        }
        for path in paths {
            path.check_lengths_for_root_and_width_of_path(root)?;
        }

        let num_indices_per_mp = paths
            .iter()
            .map(|p| p.path.selected_commitments.len())
            .collect::<Vec<_>>();
        // maximum number of leaves in any multi-path
        let max_leaves_mp = num_indices_per_mp.iter().copied().max().unwrap();

        let mut even_node_divisors: Vec<Vec<DlogItem<F0, Parameters0>>> =
            vec![Vec::new(); num_multi_paths];
        let mut odd_node_divisors: Vec<Vec<DlogItem<F1, Parameters1>>> =
            vec![Vec::new(); num_multi_paths];
        // Leaf items per multi-path, kept separate from summed items (see constraints_for_dlogs_presummed).
        let mut odd_leaf_divisors: Vec<Vec<DlogItem<F1, Parameters1>>> =
            vec![Vec::new(); num_multi_paths];

        if root.height() == 1 {
            let root_node = match root {
                Root::Odd(root_node) => root_node,
                Root::Even(_) => {
                    return Err(Error::MalformedProofInput(
                        "height-1 tree must have an odd root".to_string(),
                    ))
                }
            };
            let even_delta = even_parameters.sl_params.delta;

            // Membership check per root. Collect the leaf x-vars per root and then do its membership
            // check. This means there are at most M (multi-set) checks regardless of the total number
            // of leaves
            let mut x_vars_per_mp: Vec<Vec<LinearCombination<F1>>> =
                vec![Vec::new(); num_multi_paths];
            for root_idx in 0..max_leaves_mp {
                let mut xs = Vec::new();
                for (mp_idx, &num_indices) in num_indices_per_mp.iter().enumerate() {
                    if root_idx < num_indices {
                        let x_lc: LinearCombination<F1> =
                            odd_verifier.allocate(None).unwrap().into();
                        xs.push(x_lc.clone());
                        x_vars_per_mp[mp_idx].push(x_lc);
                    }
                }
                let x_coords = root_node.x_coord_children.get(root_idx).ok_or_else(|| {
                    Error::MalformedProofInput(format!(
                        "root x_coord_children shorter than selected indices (index {root_idx}, len {})",
                        root_node.x_coord_children.len()
                    ))
                })?;
                multi_select_public_set(odd_verifier, xs.clone(), x_coords.as_slice())?;
            }

            // Per leaf - allocate y coordinate, commit its divisor.
            for mp_idx in 0..num_multi_paths {
                for root_idx in 0..num_indices_per_mp[mp_idx] {
                    let y_var: LinearCombination<F1> = odd_verifier.allocate(None)?.into();
                    let selected_commitment = paths[mp_idx]
                        .path
                        .selected_commitments
                        .get(root_idx)
                        .ok_or_else(|| {
                            Error::MalformedProofInput(format!(
                                "selected_commitments shorter than selected indices (multi-path {mp_idx}, index {root_idx}, len {})",
                                paths[mp_idx].path.selected_commitments.len()
                            ))
                        })?;
                    odd_verifier
                        .transcript()
                        .append(b"rerandomized_child", selected_commitment);
                    let rerandomized_plus_delta = (*selected_commitment + even_delta).into_affine();
                    let (x, y) = rerandomized_plus_delta.xy().ok_or(Error::PointCantBeZero)?;
                    let leaf_divisor =
                        paths[mp_idx]
                            .odd_divisor_comms
                            .get(root_idx)
                            .ok_or_else(|| {
                                Error::MalformedProofInput(format!(
                                    "missing leaf divisor commitment for selected index (multi-path {mp_idx}, index {root_idx}, len {})",
                                    paths[mp_idx].odd_divisor_comms.len()
                                ))
                            })?;
                    let p =
                        commit_dlog_and_divisor::<_, _, Parameters1>(odd_verifier, leaf_divisor)?;
                    odd_leaf_divisors[mp_idx].push((
                        x_vars_per_mp[mp_idx][root_idx].clone(),
                        y_var,
                        x,
                        y,
                        p,
                    ));
                }
            }
        } else {
            let root_is_even = root.is_even();

            // Process the shared root once
            if root_is_even {
                let root_node = match root {
                    Root::Even(root_node) => root_node,
                    Root::Odd(_) => unreachable!(),
                };
                let mut rerandomized_sums = Vec::with_capacity(num_multi_paths);
                let mut root_divisors = Vec::with_capacity(num_multi_paths);
                for path in paths {
                    rerandomized_sums.push(*path.path.odd_commitments.get(0).ok_or_else(|| {
                        Error::MalformedProofInput("missing root child commitment".to_string())
                    })?);
                    root_divisors.push(path.even_divisor_comms.get(0).ok_or_else(|| {
                        Error::MalformedProofInput("missing root divisor commitment".to_string())
                    })?);
                }
                let items = Self::verify_shared_root_for_multi_paths::<Parameters0>(
                    even_verifier,
                    &root_node.x_coord_children,
                    &num_indices_per_mp,
                    &rerandomized_sums,
                    &root_divisors,
                    &odd_parameters.sl_params.delta,
                )?;
                for (mp, item) in items.into_iter().enumerate() {
                    even_node_divisors[mp].push(item);
                }
            } else {
                let root_node = match root {
                    Root::Odd(root_node) => root_node,
                    Root::Even(_) => unreachable!(),
                };
                let mut rerandomized_sums = Vec::with_capacity(num_multi_paths);
                let mut root_divisors = Vec::with_capacity(num_multi_paths);
                for path in paths {
                    rerandomized_sums.push(*path.path.even_commitments.get(0).ok_or_else(
                        || Error::MalformedProofInput("missing root child commitment".to_string()),
                    )?);
                    root_divisors.push(path.odd_divisor_comms.get(0).ok_or_else(|| {
                        Error::MalformedProofInput("missing root divisor commitment".to_string())
                    })?);
                }
                let items = SelectAndRerandomizeMultiPathWithDivisorComms::<L, M, P1, P0>::verify_shared_root_for_multi_paths::<
                    Parameters1,
                >(
                    odd_verifier,
                    &root_node.x_coord_children,
                    &num_indices_per_mp,
                    &rerandomized_sums,
                    &root_divisors,
                    &even_parameters.sl_params.delta,
                )?;
                for (mp, item) in items.into_iter().enumerate() {
                    odd_node_divisors[mp].push(item);
                }
            }

            // Per multi-path: non-root levels then the leaf level.
            for mp_idx in 0..num_multi_paths {
                let path = &paths[mp_idx];
                let num_indices = num_indices_per_mp[mp_idx];

                // Process all even levels
                let even_items = Self::verify_batched_non_root_on_curve::<Parameters0>(
                    even_verifier,
                    root_is_even,
                    path.path.even_commitments.len(),
                    num_indices as u32,
                    &path.path.even_commitments,
                    &path.path.odd_commitments,
                    &path.even_divisor_comms,
                    &odd_parameters.sl_params.delta,
                )?;
                even_node_divisors[mp_idx].extend(even_items);

                // Process all odd levels except for leaf's parent
                let odd_non_root_len =
                    path.path.odd_commitments.len().checked_sub(1).ok_or_else(|| {
                        Error::MalformedProofInput(
                            "odd_commitments must contain at least one element for leaf verification"
                                .to_string(),
                        )
                    })?;
                let odd_items = SelectAndRerandomizeMultiPathWithDivisorComms::<L, M, P1, P0>::verify_batched_non_root_on_curve::<
                    Parameters1,
                >(
                    odd_verifier,
                    !root_is_even,
                    odd_non_root_len,
                    num_indices as u32,
                    &path.path.odd_commitments,
                    &path.path.even_commitments,
                    &path.odd_divisor_comms,
                    &even_parameters.sl_params.delta,
                )?;
                odd_node_divisors[mp_idx].extend(odd_items);

                // leaf level
                let parent_index =
                    path.path.odd_commitments.len().checked_sub(1).ok_or_else(|| {
                        Error::MalformedProofInput(
                            "odd_commitments must contain at least one element for leaf verification"
                                .to_string(),
                        )
                    })?;
                let parent_commitment =
                    *path.path.odd_commitments.get(parent_index).ok_or_else(|| {
                        Error::MalformedProofInput(format!(
                            "odd_commitments shorter than required for leaf verification (multi-path {mp_idx}, index {parent_index}, len {})",
                            path.path.odd_commitments.len()
                        ))
                    })?;
                let children_vars: Vec<Variable<F1>> =
                    odd_verifier.commit_vec(L * num_indices, parent_commitment);
                if children_vars.len() % num_indices != 0 {
                    return Err(Error::MalformedProofInput(
                        "leaf parent commitment does not split evenly across selected indices"
                            .to_string(),
                    ));
                }
                let chunk_size = children_vars.len() / num_indices;
                let chunks: Vec<_> = children_vars.chunks_exact(chunk_size).collect();
                let leaf_divisor_start = path
                    .odd_divisor_comms
                    .len()
                    .checked_sub(num_indices)
                    .ok_or_else(|| {
                        Error::MalformedProofInput(format!(
                            "odd_divisor_comms shorter than selected indices for leaf verification (multi-path {mp_idx}, len {}, num_indices {num_indices})",
                            path.odd_divisor_comms.len()
                        ))
                    })?;
                for (i, chunk) in chunks.iter().enumerate() {
                    let selected_commitment =
                        path.path.selected_commitments.get(i).ok_or_else(|| {
                            Error::MalformedProofInput(format!(
                                "selected_commitments shorter than inferred leaf chunks (multi-path {mp_idx}, index {i}, len {})",
                                path.path.selected_commitments.len()
                            ))
                        })?;
                    let leaf_divisor = path
                        .odd_divisor_comms
                        .get(leaf_divisor_start + i)
                        .ok_or_else(|| {
                            Error::MalformedProofInput(format!(
                                "missing leaf divisor commitment for selected index {} (multi-path {mp_idx}, len {})",
                                leaf_divisor_start + i,
                                path.odd_divisor_comms.len()
                            ))
                        })?;
                    let item = Self::verify_leaf::<Parameters1>(
                        odd_verifier,
                        LeafParent::NonRoot(chunk.iter().map(|v| (*v).into()).collect()),
                        selected_commitment,
                        &even_parameters.sl_params.delta,
                        leaf_divisor,
                    )?;
                    odd_leaf_divisors[mp_idx].push(item);
                }
            }
        }

        constraints_for_dlogs_presummed::<_, _, _, _, P0, P1, Parameters0, Parameters1>(
            even_verifier,
            odd_verifier,
            &even_parameters.table_b_blinding,
            &odd_parameters.table_b_blinding,
            even_node_divisors.into_iter().flatten(),
            odd_node_divisors.into_iter().flatten(),
            odd_leaf_divisors.into_iter().flatten(),
        )?;

        Ok(())
    }
}

enum LeafParent<'a, F: PrimeField> {
    Root(&'a [F]), // Leaf's parent is root and these are x-coords of children of root
    NonRoot(Vec<LinearCombination<F>>), // Leaf's parent is non-root and these are variables for the children
}
