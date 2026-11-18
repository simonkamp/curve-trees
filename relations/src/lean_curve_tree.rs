use crate::curve_tree::{Root, RootNode};
use crate::curve_tree_prover::{CurveTreeWitnessPath, WitnessNode};
use crate::parameters::{SelRerandParametersRef, SingleLayerParameters};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::collections::BTreeMap;
use ark_std::{vec, vec::Vec};

#[derive(Clone, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct DefaultNode<P0: SWCurveConfig, P1: SWCurveConfig> {
    /// Only 1 coordinate since all `L` x-coordinates are same for a default node
    pub x_coord: P0::BaseField,
    pub commitment: Affine<P1>,
}

#[derive(Clone, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct Node<P0: SWCurveConfig, P1: SWCurveConfig> {
    pub x_coords: Vec<P0::BaseField>,
    pub commitment: Affine<P1>,
}

/// Append only curve tree with minimal nodes to keep that reflect the most recent tree state
#[derive(Clone, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct LeanCurveTree<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    pub height: u8,
    /// Index of the next leaf to be added. Starts from 0
    pub next_leaf_index: u64,
    pub even_level_path_nodes: Vec<Node<P1, P0>>,
    pub odd_level_path_nodes: Vec<Node<P0, P1>>,
    // The following fields are readonly once the tree is initialized so could be moved to "static" storage
    pub even_level_default_nodes: Vec<DefaultNode<P1, P0>>,
    pub odd_level_default_nodes: Vec<DefaultNode<P0, P1>>,
    /// The total number of children and grandchildren at each level
    pub children_count: BTreeMap<u8, u64>,
}

impl<
        const L: usize,
        F0: PrimeField,
        F1: PrimeField,
        P0: SWCurveConfig<BaseField = F1, ScalarField = F0> + Copy,
        P1: SWCurveConfig<BaseField = F0, ScalarField = F1> + Copy,
    > LeanCurveTree<L, P0, P1>
{
    pub fn new(height: u8, parameters: &impl SelRerandParametersRef<P0, P1>) -> Self {
        assert!(height > 0);
        let (odd_level_default_nodes, even_level_default_nodes) =
            Self::get_default_nodes(height, parameters);
        let mut even_level_path_nodes =
            Vec::<Node<P1, P0>>::with_capacity(even_level_default_nodes.len());
        let mut odd_level_path_nodes =
            Vec::<Node<P0, P1>>::with_capacity(odd_level_default_nodes.len());
        let mut children_count = BTreeMap::new();
        for i in 0..(height - 1) {
            // TODO: Optimize when L power of 2.
            let count = (L as u64).pow((i + 1) as u32);
            children_count.insert(i, count);
        }

        for i in 0..odd_level_default_nodes.len() {
            odd_level_path_nodes.push(Node {
                x_coords: vec![],
                commitment: odd_level_default_nodes[i].commitment,
            });
        }
        for i in 0..even_level_default_nodes.len() {
            even_level_path_nodes.push(Node {
                x_coords: vec![],
                commitment: even_level_default_nodes[i].commitment,
            });
        }
        Self {
            height,
            next_leaf_index: 0,
            even_level_default_nodes,
            odd_level_default_nodes,
            children_count,
            even_level_path_nodes,
            odd_level_path_nodes,
        }
    }

    pub fn insert(
        &mut self,
        leaf_value: Affine<P0>,
        parameters: &impl SelRerandParametersRef<P0, P1>,
    ) {
        self.set_full_subtrees_to_default();

        let mut curr_idx = self.next_leaf_index;

        for i in 0..self.height as usize {
            let pos = (curr_idx % (L as u64)) as usize;
            if i % 2 == 0 {
                let node_to_update = &mut self.odd_level_path_nodes[i / 2];

                let child_node = if i == 0 {
                    leaf_value
                } else {
                    self.even_level_path_nodes[(i / 2) - 1].commitment
                };

                let default_x_coord = self.odd_level_default_nodes[i / 2].x_coord;

                LeanCurveTree::<L, P0, P1>::update_node(
                    pos,
                    node_to_update,
                    child_node,
                    default_x_coord,
                    parameters.odd_parameters(),
                    parameters.even_parameters(),
                )
            } else {
                let node_to_update = &mut self.even_level_path_nodes[i / 2];

                let child_node = self.odd_level_path_nodes[i / 2].commitment;

                let default_x_coord = self.even_level_default_nodes[i / 2].x_coord;

                LeanCurveTree::<L, P1, P0>::update_node(
                    pos,
                    node_to_update,
                    child_node,
                    default_x_coord,
                    parameters.even_parameters(),
                    parameters.odd_parameters(),
                )
            }
            curr_idx /= L as u64;
        }

        self.next_leaf_index += 1;
    }

    // Note: Witness doesn't necessarily need to be returned as it can be constructed from the leaf value
    // and the current state of the tree. This fact is useful when implementing this function on a blockchain
    pub fn insert_and_return_path(
        &mut self,
        leaf_value: Affine<P0>,
        parameters: &impl SelRerandParametersRef<P0, P1>,
    ) -> CurveTreeWitnessPath<L, P0, P1> {
        // TODO: Most of this contains duplication from above function which can likely be removed by passing a closure that calls node update function
        let mut even_witness_nodes = Vec::<WitnessNode<L, P0, P1>>::new();
        let mut odd_witness_nodes = Vec::<WitnessNode<L, P1, P0>>::new();

        self.set_full_subtrees_to_default();

        let mut curr_idx = self.next_leaf_index;

        for i in 0..self.height as usize {
            let pos = (curr_idx % (L as u64)) as usize;
            if i % 2 == 0 {
                let node_to_update = &mut self.odd_level_path_nodes[i / 2];

                let child_node = if i == 0 {
                    leaf_value
                } else {
                    self.even_level_path_nodes[(i / 2) - 1].commitment
                };

                let default_x_coord = self.odd_level_default_nodes[i / 2].x_coord;

                odd_witness_nodes.push(LeanCurveTree::_insert_and_return_path(
                    pos,
                    node_to_update,
                    child_node,
                    default_x_coord,
                    parameters.odd_parameters(),
                    parameters.even_parameters(),
                ));
            } else {
                let node_to_update = &mut self.even_level_path_nodes[i / 2];

                let child_node = self.odd_level_path_nodes[i / 2].commitment;

                let default_x_coord = self.even_level_default_nodes[i / 2].x_coord;

                even_witness_nodes.push(LeanCurveTree::_insert_and_return_path(
                    pos,
                    node_to_update,
                    child_node,
                    default_x_coord,
                    parameters.even_parameters(),
                    parameters.odd_parameters(),
                ));
            }
            curr_idx /= L as u64;
        }

        self.next_leaf_index += 1;

        odd_witness_nodes.reverse();
        even_witness_nodes.reverse();
        CurveTreeWitnessPath::<L, P0, P1> {
            even_internal_nodes: even_witness_nodes,
            odd_internal_nodes: odd_witness_nodes,
        }
    }

    pub fn root_node(&self) -> Root<L, 1, P0, P1> {
        let is_root_at_odd_level = (self.height % 2) == 1;
        if is_root_at_odd_level {
            let node = self.odd_level_path_nodes.last().unwrap();
            let default_node = self.odd_level_default_nodes.last().unwrap();
            Root::Odd(LeanCurveTree::inner_root_node(
                node,
                default_node,
                self.height,
            ))
        } else {
            let node = self.even_level_path_nodes.last().unwrap();
            let default_node = self.even_level_default_nodes.last().unwrap();
            Root::Even(LeanCurveTree::inner_root_node(
                node,
                default_node,
                self.height,
            ))
        }
    }

    pub fn default_leaf() -> Affine<P0> {
        Affine::<P0>::zero()
    }

    pub fn get_default_nodes(
        height: u8,
        parameters: &impl SelRerandParametersRef<P0, P1>,
    ) -> (Vec<DefaultNode<P0, P1>>, Vec<DefaultNode<P1, P0>>) {
        let mut even_level_default_nodes = Vec::<DefaultNode<P1, P0>>::new();
        let mut odd_level_default_nodes = Vec::<DefaultNode<P0, P1>>::new();
        // Store value of default node at each level
        for i in 0..height {
            if i % 2 == 0 {
                let node = LeanCurveTree::<L, P0, P1>::combine_default(
                    if i == 0 {
                        Self::default_leaf()
                    } else {
                        even_level_default_nodes.last().unwrap().commitment.clone()
                    },
                    parameters.even_parameters().delta,
                    parameters.odd_parameters(),
                );
                odd_level_default_nodes.push(node);
            } else {
                let node = LeanCurveTree::<L, P1, P0>::combine_default(
                    odd_level_default_nodes.last().unwrap().commitment.clone(),
                    parameters.odd_parameters().delta,
                    parameters.even_parameters(),
                );
                even_level_default_nodes.push(node);
            }
        }
        (odd_level_default_nodes, even_level_default_nodes)
    }

    pub fn path_for_last_added_leaf(
        &self,
        leaf_value: Affine<P0>,
    ) -> CurveTreeWitnessPath<L, P0, P1> {
        let mut even_witness_nodes = Vec::<WitnessNode<L, P0, P1>>::new();
        let mut odd_witness_nodes = Vec::<WitnessNode<L, P1, P0>>::new();
        for i in 0..self.height as usize {
            if i % 2 == 0 {
                let parent_node = &self.odd_level_path_nodes[i / 2];
                let child_node = if i == 0 {
                    leaf_value
                } else {
                    self.even_level_path_nodes[(i / 2) - 1].commitment
                };
                let default_x_coord = self.odd_level_default_nodes[i / 2].x_coord;
                odd_witness_nodes.push(LeanCurveTree::get_witness_node(
                    parent_node,
                    child_node,
                    default_x_coord,
                ));
            } else {
                let parent_node = &self.even_level_path_nodes[i / 2];
                let child_node = self.odd_level_path_nodes[i / 2].commitment;
                let default_x_coord = self.even_level_default_nodes[i / 2].x_coord;
                even_witness_nodes.push(LeanCurveTree::get_witness_node(
                    parent_node,
                    child_node,
                    default_x_coord,
                ));
            }
        }
        odd_witness_nodes.reverse();
        even_witness_nodes.reverse();
        CurveTreeWitnessPath::<L, P0, P1> {
            even_internal_nodes: even_witness_nodes,
            odd_internal_nodes: odd_witness_nodes,
        }
    }

    pub(crate) fn inner_root_node(
        node: &Node<P0, P1>,
        default_node: &DefaultNode<P0, P1>,
        height: u8,
    ) -> RootNode<L, 1, P1, P0> {
        let mut x_coord = [default_node.x_coord; L];
        for i in 0..L {
            if i < node.x_coords.len() {
                x_coord[i] = node.x_coords[i];
            }
        }
        RootNode {
            commitments: [node.commitment],
            x_coord_children: vec![x_coord],
            height,
        }
    }

    fn set_full_subtrees_to_default(&mut self) {
        // For full subtrees, set those subtree roots to default
        for i in 0..(self.height - 1) as usize {
            let children_count = self.children_count[&(i as u8)];
            if (self.next_leaf_index >= children_count)
                && (self.next_leaf_index % children_count) == 0
            {
                if i % 2 == 0 {
                    let node_to_update = &mut self.odd_level_path_nodes[i / 2];
                    node_to_update.x_coords = vec![];
                    node_to_update.commitment = self.odd_level_default_nodes[i / 2].commitment;
                } else {
                    let node_to_update = &mut self.even_level_path_nodes[i / 2];
                    node_to_update.x_coords = vec![];
                    node_to_update.commitment = self.even_level_default_nodes[i / 2].commitment;
                }
            }
        }
    }

    fn _insert_and_return_path(
        pos: usize,
        node_to_update: &mut Node<P0, P1>,
        child_node: Affine<P0>,
        default_x_coord: F1,
        node_level_params: &SingleLayerParameters<P1>,
        child_level_params: &SingleLayerParameters<P0>,
    ) -> WitnessNode<L, P1, P0> {
        Self::update_node(
            pos,
            node_to_update,
            child_node,
            default_x_coord,
            node_level_params,
            child_level_params,
        );
        Self::get_witness_node(node_to_update, child_node, default_x_coord)
    }

    pub(crate) fn get_witness_node(
        parent_node: &Node<P0, P1>,
        child_node: Affine<P0>,
        default_x_coord: F1,
    ) -> WitnessNode<L, P1, P0> {
        let mut x_coord_children = [default_x_coord; L];
        for j in 0..L {
            if j < parent_node.x_coords.len() {
                x_coord_children[j] = parent_node.x_coords[j];
            }
        }
        WitnessNode {
            child_node_to_randomize: child_node,
            x_coord_children,
        }
    }

    pub(crate) fn update_node(
        pos: usize,
        node_to_update: &mut Node<P0, P1>,
        child_node: Affine<P0>,
        default_x_coord: F1,
        node_level_params: &SingleLayerParameters<P1>,
        child_level_params: &SingleLayerParameters<P0>,
    ) {
        let child_node_delta_x_coord = (child_node + child_level_params.delta).into_affine().x;
        let gen_iter = node_level_params.bp_gens.share(0).G(L as u32).skip(pos);
        let gen = gen_iter.copied().next().unwrap();

        let diff = if pos < node_to_update.x_coords.len() {
            let old_x = node_to_update.x_coords[pos];
            node_to_update.x_coords[pos] = child_node_delta_x_coord;
            gen * (child_node_delta_x_coord - old_x)
        } else {
            node_to_update.x_coords.push(child_node_delta_x_coord);
            gen * (child_node_delta_x_coord - default_x_coord)
        };
        node_to_update.commitment = (node_to_update.commitment + diff).into_affine();
    }

    fn combine_default(
        child_node: Affine<P0>,
        delta: Affine<P0>,
        parameters: &SingleLayerParameters<P1>,
    ) -> DefaultNode<P0, P1> {
        let child_delta_x = (child_node + delta).into_affine().x;
        let commitment = parameters.commit_for_default_node(child_delta_x, L as u32, 0);
        DefaultNode {
            x_coord: child_delta_x,
            commitment,
        }
    }
}
