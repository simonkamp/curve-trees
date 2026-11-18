use crate::curve_tree::Root;
use crate::curve_tree_prover::{CurveTreeWitnessPath, WitnessNode};
use crate::error::Error;
use crate::lean_curve_tree::{DefaultNode, LeanCurveTree, Node};
use crate::parameters::{SelRerandParametersRef, SingleLayerParameters};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::collections::{BTreeMap, BTreeSet};
use ark_std::{vec, vec::Vec};

type InnerNodeIndex = u64;

// TODO: Faster math when L is power of 2

// TODO: Add persistence

/// Append only curve tree which allows tracking certain leaves and providing their most recent path
#[derive(Clone, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct PartialCurveTree<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    pub height: u8,
    /// Index of the next leaf to be added. Starts from 0
    pub next_leaf_index: u64,
    pub even_levels: Vec<BTreeMap<InnerNodeIndex, Node<P1, P0>>>,
    pub odd_levels: Vec<BTreeMap<InnerNodeIndex, Node<P0, P1>>>,
    /// Leaves that are tracked. Path for these can be retrieved to be used in proofs
    pub leaves: BTreeMap<u64, Affine<P0>>,
    pub even_level_default_nodes: Vec<DefaultNode<P1, P0>>,
    pub odd_level_default_nodes: Vec<DefaultNode<P0, P1>>,
}

impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > PartialCurveTree<L, P0, P1>
{
    pub fn new(
        height: u8,
        parameters: &impl SelRerandParametersRef<P0, P1>,
    ) -> Result<Self, Error> {
        if height == 0 {
            return Err(Error::HeightCantBe0);
        }
        let (odd_level_default_nodes, even_level_default_nodes) =
            LeanCurveTree::<L, P0, P1>::get_default_nodes(height, parameters);
        let mut even_levels = Vec::<BTreeMap<InnerNodeIndex, Node<P1, P0>>>::with_capacity(
            even_level_default_nodes.len(),
        );
        let mut odd_levels = Vec::<BTreeMap<InnerNodeIndex, Node<P0, P1>>>::with_capacity(
            odd_level_default_nodes.len(),
        );
        for _ in 0..odd_level_default_nodes.len() {
            odd_levels.push(BTreeMap::new());
        }
        for _ in 0..even_level_default_nodes.len() {
            even_levels.push(BTreeMap::new());
        }
        Ok(Self {
            height,
            next_leaf_index: 0,
            even_level_default_nodes,
            odd_level_default_nodes,
            even_levels,
            odd_levels,
            leaves: BTreeMap::new(),
        })
    }

    /// Insert a leaf that is tracked and for which path can be retrieved
    pub fn insert_leaf(
        &mut self,
        leaf_index: u64,
        leaf_value: Affine<P0>,
        odd_level_path_nodes: Vec<Node<P0, P1>>,
        even_level_path_nodes: Vec<Node<P1, P0>>,
    ) -> Result<(), Error> {
        if self.next_leaf_index == (L as u64).pow(self.height as u32) {
            return Err(Error::TreeWontSupportRequiredInsertions(
                self.next_leaf_index,
                self.next_leaf_index + 1,
            ));
        }

        if self.leaves.contains_key(&leaf_index) {
            return Err(Error::LeafAlreadyExistAtIndex(leaf_index));
        }

        // If the tree isn't empty then leaves should be inserted in order
        if !self.leaves.is_empty() {
            if leaf_index != self.next_leaf_index {
                return Err(Error::LeafIndexNotAsExpected(
                    leaf_index,
                    self.next_leaf_index,
                ));
            }
        }

        let mut curr_idx = leaf_index;
        for i in 0..self.height as usize {
            let parent_pos = curr_idx / (L as u64);
            if i % 2 == 0 {
                let level_to_update = &mut self.odd_levels[i / 2];
                level_to_update.insert(
                    parent_pos as InnerNodeIndex,
                    odd_level_path_nodes[i / 2].clone(),
                );
            } else {
                let level_to_update = &mut self.even_levels[i / 2];
                level_to_update.insert(
                    parent_pos as InnerNodeIndex,
                    even_level_path_nodes[i / 2].clone(),
                );
            }
            curr_idx /= L as u64;
        }

        self.leaves.insert(leaf_index, leaf_value);
        self.next_leaf_index = leaf_index + 1;
        Ok(())
    }

    /// Update the inner nodes of the tree for given leaves. But these leaves are not tracked.
    // TODO: This function could take another arg `indices_to_keep` which adds leaves at those indices to `self.leaves`
    pub fn update_on_leaves(
        &mut self,
        leaves: Vec<Affine<P0>>,
        parameters: &impl SelRerandParametersRef<P0, P1>,
    ) -> Result<(), Error> {
        if (self.next_leaf_index + leaves.len() as u64) > (L as u64).pow(self.height as u32) {
            return Err(Error::TreeWontSupportRequiredInsertions(
                self.next_leaf_index,
                self.next_leaf_index + leaves.len() as u64,
            ));
        }
        // TODO: Batch the updates together
        let offset = self.next_leaf_index;
        for (j, leaf_value) in leaves.into_iter().enumerate() {
            let leaf_index = offset + j as u64;
            let mut curr_idx = leaf_index;
            for i in 0..self.height as usize {
                let pos = (curr_idx % (L as u64)) as u16;
                // TODO: Rename
                let parent_pos = (curr_idx / (L as u64)) as InnerNodeIndex;
                let child_pos = curr_idx as InnerNodeIndex;
                if i % 2 == 0 {
                    let child_node = if i == 0 {
                        leaf_value
                    } else {
                        let child_level = &self.even_levels[(i / 2) - 1];
                        child_level.get(&child_pos).unwrap().commitment
                    };
                    PartialCurveTree::<L, _, _>::_update(
                        pos,
                        parent_pos,
                        &mut self.odd_levels[i / 2],
                        child_node,
                        self.odd_level_default_nodes[i / 2].clone(),
                        parameters.odd_parameters(),
                        parameters.even_parameters(),
                    )
                } else {
                    let child_level = &self.odd_levels[i / 2];
                    let child_node = child_level.get(&child_pos).unwrap().commitment;
                    PartialCurveTree::<L, _, _>::_update(
                        pos,
                        parent_pos,
                        &mut self.even_levels[i / 2],
                        child_node,
                        self.even_level_default_nodes[i / 2].clone(),
                        parameters.even_parameters(),
                        parameters.odd_parameters(),
                    )
                }
                curr_idx /= L as u64;
            }
            self.next_leaf_index += 1;
        }
        Ok(())
    }

    pub fn get_path_to_leaf(
        &self,
        leaf_index: u64,
    ) -> Result<CurveTreeWitnessPath<L, P0, P1>, Error> {
        log::debug!("Querying leaf {}", leaf_index);
        if !self.leaves.contains_key(&leaf_index) {
            return Err(Error::LeafDoesntExistAtIndex(leaf_index));
        }
        let leaf_value = self.leaves.get(&leaf_index).unwrap().clone();
        let mut even_witness_nodes = Vec::<WitnessNode<L, P0, P1>>::new();
        let mut odd_witness_nodes = Vec::<WitnessNode<L, P1, P0>>::new();
        let mut curr_idx = leaf_index;
        // TODO: Remove unwraps
        for i in 0..self.height as usize {
            let parent_pos = (curr_idx / (L as u64)) as InnerNodeIndex;
            let child_pos = curr_idx as InnerNodeIndex;
            if i % 2 == 0 {
                let child_node = if i == 0 {
                    leaf_value
                } else {
                    let child_level = &self.even_levels[(i / 2) - 1];
                    child_level.get(&child_pos).unwrap().commitment
                };
                odd_witness_nodes.push(PartialCurveTree::<L, _, _>::_witness_node(
                    parent_pos,
                    &self.odd_levels[i / 2],
                    child_node,
                    self.odd_level_default_nodes[i / 2].clone(),
                ));
            } else {
                let child_level = &self.odd_levels[i / 2];
                let child_node = child_level.get(&child_pos).unwrap().commitment;
                even_witness_nodes.push(PartialCurveTree::<L, _, _>::_witness_node(
                    parent_pos,
                    &self.even_levels[i / 2],
                    child_node,
                    self.even_level_default_nodes[i / 2].clone(),
                ));
            }
            curr_idx = curr_idx / L as u64;
        }
        odd_witness_nodes.reverse();
        even_witness_nodes.reverse();
        Ok(CurveTreeWitnessPath::<L, P0, P1> {
            even_internal_nodes: even_witness_nodes,
            odd_internal_nodes: odd_witness_nodes,
        })
    }

    pub fn root_node(&self) -> Root<L, 1, P0, P1> {
        let is_root_at_odd_level = (self.height % 2) == 1;
        // Unwraps are fine as tree height is ensured to be > 0
        if is_root_at_odd_level {
            let node = self.odd_levels.last().unwrap().get(&0).unwrap();
            let default_node = self.odd_level_default_nodes.last().unwrap();
            Root::Odd(LeanCurveTree::inner_root_node(
                node,
                default_node,
                self.height,
            ))
        } else {
            let node = self.even_levels.last().unwrap().get(&0).unwrap();
            let default_node = self.even_level_default_nodes.last().unwrap();
            Root::Even(LeanCurveTree::inner_root_node(
                node,
                default_node,
                self.height,
            ))
        }
    }

    /// Remove the full nodes that don't lie on the path to any leaf that is being tracked.
    pub fn clear_full_nodes(&mut self) -> u64 {
        let mut removed_nodes = 0;
        for i in 0..self.height as usize {
            let children_count = (L as u64).pow((i + 1) as u32);
            let parent_node_indices_of_leaves = self
                .leaves
                .keys()
                .map(|j| *j / children_count)
                .collect::<BTreeSet<InnerNodeIndex>>();
            if i % 2 == 0 {
                let parent_level = &mut self.odd_levels[i / 2];
                let all_parent_node_indices = parent_level
                    .keys()
                    .map(|j| *j)
                    .collect::<Vec<InnerNodeIndex>>();
                for j in all_parent_node_indices {
                    if !parent_node_indices_of_leaves.contains(&j) {
                        parent_level.remove(&j);
                        removed_nodes += 1;
                    }
                }
            } else {
                let parent_level = &mut self.even_levels[i / 2];
                let all_parent_node_indices = parent_level
                    .keys()
                    .map(|j| *j)
                    .collect::<Vec<InnerNodeIndex>>();
                for j in all_parent_node_indices {
                    if !parent_node_indices_of_leaves.contains(&j) {
                        parent_level.remove(&j);
                        removed_nodes += 1;
                    }
                }
            }
        }
        removed_nodes
    }

    fn _update(
        pos: u16,
        parent_pos: InnerNodeIndex,
        level_to_update: &mut BTreeMap<InnerNodeIndex, Node<P0, P1>>,
        child_node: Affine<P0>,
        default_node: DefaultNode<P0, P1>,
        node_level_params: &SingleLayerParameters<P1>,
        child_level_params: &SingleLayerParameters<P0>,
    ) {
        let node_to_update = level_to_update.get_mut(&parent_pos);
        if let Some(node) = node_to_update {
            let default_x_coord = default_node.x_coord;

            LeanCurveTree::<L, P0, P1>::update_node(
                pos as usize,
                node,
                child_node,
                default_x_coord,
                node_level_params,
                child_level_params,
            )
        } else {
            let default_comm = default_node.commitment;
            let default_x_coord = default_node.x_coord;
            let mut node = Node {
                x_coords: vec![default_x_coord],
                commitment: default_comm,
            };
            LeanCurveTree::<L, P0, P1>::update_node(
                pos as usize,
                &mut node,
                child_node,
                default_x_coord,
                node_level_params,
                child_level_params,
            );
            level_to_update.insert(parent_pos, node);
        }
    }

    fn _witness_node(
        parent_pos: InnerNodeIndex,
        parent_level: &BTreeMap<InnerNodeIndex, Node<P0, P1>>,
        child_node: Affine<P0>,
        default_node: DefaultNode<P0, P1>,
    ) -> WitnessNode<L, P1, P0> {
        // TODO: Remove unwrap
        let parent_node = parent_level.get(&parent_pos).unwrap();
        let default_x_coord = default_node.x_coord;
        LeanCurveTree::get_witness_node(parent_node, child_node, default_x_coord)
    }
}
