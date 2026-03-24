# SORRY BOARD — P ≠ NP Lean Formalization

## Status Key
- OPEN: ready to work
- BLOCKED: waiting on dependency
- IN_PROGRESS: assigned to worker
- MERGED: patch applied
- VERIFIED: builds clean

## Master Table

| ID | Theorem | File:Line | Paper Lines | Depends On | Unlocks | Status |
|----|---------|-----------|-------------|------------|---------|--------|
| 13 | pathPairingAux | Interface:264 | 207-215 | — | 16,21,1,18 | OPEN |
| 14 | rightPairingAux | Interface:302 | 223-241 | — | 1,18 | OPEN |
| 15 | IsConnectedEdgeSet_of_boundary_connected | Interface:455 | 417-419 | — | — | OPEN |
| 7 | surviving_edges_pull_back_ax | Funnel:348 | 1584-1604 | — | — | OPEN |
| 8 | block_edges_cancel_ax | Funnel:375 | 1590-1595 | — | — | OPEN |
| 3 | funnel_iteration_bound_ax | Formula:205 | 1701-1721 | — | — | OPEN |
| 11 | iterated_recurrence_exponential_bound | Funnel:1080 | 1701-1721 | — | — | OPEN |
| 19 | leftSubgraph_no_cycle_when_no_premature | Stitch:39 | 275-289 | — | — | OPEN |
| 23 | degree_change_iff_monochromatic_ax | Switch:104 | 971-998 | — | — | OPEN |
| 4 | consecutive_blocks_from_ham_cycle_ax | Funnel:38 | 1291-1304 | — | — | OPEN |
| 5 | degree_visible_supply_linear_density_ax | Funnel:157 | 1306-1334 | — | — | OPEN |
| 6 | greedy_packing_from_supply_ax | Funnel:214 | 1336-1350 | — | — | OPEN |
| 9 | carrier_extension_block_construction | Funnel:697 | 1481-1503 | — | — | OPEN |
| 10 | multi_carrier_suppression_child | Funnel:790 | 1563-1604 | — | — | OPEN |
| 22 | packed_family_robustness_ax | Switch:38 | 898-944 | — | — | OPEN |
| 25 | swapped_toggle_forces_same_side_ax | Switch:300 | 987-997 | — | — | OPEN |
| 24 | degree_visibility_bias_bounds_ax | Switch:156 | 1011-1069 | — | — | OPEN |
| 17 | circuit_rectangle | Interface:709 | 550-565 | — | — | OPEN |
| 20 | contraction_preserves_components | Stitch:139 | 368-420 | — | — | OPEN |
| 12 | aho_ullman_yannakakis_formula_partition_bound_ax | Funnel:1107 | 1734-1738 | — | — | OPEN |
| 2 | cross_pattern_rect_isolation_pp_bound_ax | Formula:50 | 1740-1751 | — | — | OPEN |
| 16 | same_pairing_transfers_reachability | Interface:534 | 487-511 | 13 | — | BLOCKED |
| 21 | matching_pairings_give_same_boundary_left_edges | Stitch:236 | 503-511 | 13 | — | BLOCKED |
| 1 | boundary_multigraph_equals_overlay_components | Collision:234 | 795-808 | 13,14 | — | BLOCKED |
| 18 | disconnected_overlay_not_connected | Interface:881 | 795-808 | 13,14 | — | BLOCKED |
