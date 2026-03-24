# SORRY BOARD — P ≠ NP Lean Formalization
## Current: 0 errors, 0 axioms, 20 sorries

## Cleared This Session (7 from original 25)
- #3 funnel_iteration_bound_ax (Formula)
- #11 iterated_recurrence_exponential_bound (Funnel)
- #13 pathPairingAux (Interface) — redesigned to structural Classical.choose
- #14 rightPairingAux (Interface) — same
- #15 IsConnectedEdgeSet_of_boundary_connected (Interface) — deleted, dead code
- #19 leftSubgraph_no_cycle_when_no_premature (Stitch) — added hRight hypothesis
- #7/#8 block_edges_cancel/surviving_edges — added hAvoid hypothesis

## Structural Divergence (quarantined)
- **#18 swapped_toggle_forces_same_side_ax** — FALSE as stated. The current Lean proof route diverges from the paper. Paper uses rectangle property + circuit layer. Lean tried per-vertex degree comparison between arbitrary Ham cycles. **Requires dedicated rewrite to paper route, not a hypothesis patch.**

## Remaining 20 Sorries

### NEW — pathPairing existence (2 sorries, Interface.lean)
| ID | Theorem | Line | Status | Notes |
|----|---------|------|--------|-------|
| new-1 | exists_structural_pathPairing | 478 | IN_PROGRESS | Construct matching from path-component endpoints |
| new-2 | exists_structural_rightPairing | 553 | IN_PROGRESS | Same for right subgraph |

### Switch.lean (4 sorries)
| ID | Theorem | Line | Status |
|----|---------|------|--------|
| 15 | packed_family_robustness_ax | 38 | OPEN |
| 16 | degree_change_iff_monochromatic_ax | 104 | OPEN — confirmed tractable, needs Finset work |
| 17 | degree_visibility_bias_bounds_ax | 156 | OPEN |
| 18 | swapped_toggle_forces_same_side_ax | 300 | QUARANTINED — structural divergence |

### Funnel.lean (7 sorries)
| ID | Theorem | Line | Status |
|----|---------|------|--------|
| 4 | consecutive_blocks_from_ham_cycle_ax | 38 | OPEN |
| 5 | degree_visible_supply_linear_density_ax | 157 | OPEN |
| 6 | greedy_packing_from_supply_ax | 214 | OPEN — depends on #15 |
| 7 | surviving_edges_pull_back_ax | 348 | OPEN (inner sorries on vertex_small) |
| 8 | carrier_extension_block_construction | 742 | OPEN |
| 9 | multi_carrier_suppression_child | 835 | OPEN |
| 12 | aho_ullman_yannakakis_formula_partition_bound_ax | 1230 | OPEN |

### Interface.lean (3 sorries, excluding new pathPairing)
| ID | Theorem | Line | Status |
|----|---------|------|--------|
| 10 | same_pairing_transfers_reachability | 749 | OPEN — needs pathPairing existence first |
| 11 | circuit_rectangle | 924 | OPEN |
| 1 | disconnected_overlay_not_connected | 1096 | OPEN |

### Stitch.lean (2 sorries)
| ID | Theorem | Line | Status |
|----|---------|------|--------|
| 13 | contraction_preserves_components | 149 | OPEN |
| 14 | matching_pairings_give_same_boundary_left_edges | 246 | OPEN — needs pathPairing existence first |

### Collision.lean (1 sorry)
| ID | Theorem | Line | Status |
|----|---------|------|--------|
| 2 | boundary_multigraph_equals_overlay_components | 234 | OPEN |

### Formula.lean (1 sorry)
| ID | Theorem | Line | Status |
|----|---------|------|--------|
| 3 | cross_pattern_rect_isolation_pp_bound_ax | 50 | OPEN |
