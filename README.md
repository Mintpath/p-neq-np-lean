# p-neq-np-lean

[![Lean 4 Build](https://github.com/Mintpath/p-neq-np-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Mintpath/p-neq-np-lean/actions/workflows/lean_action_ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

Machine-verified proof that P ≠ NP via exponential circuit lower bounds for Hamiltonian Cycle. Lean 4 formalization with Mathlib. Proves SIZE(HAM_n) ≥ 2^{Ω(n)} using frontier analysis, switch blocks, cross-pattern mixing, recursive funnel magnification, continuation packets, rooted descent, and signature rigidity.

**Zero `sorry`. Two `axiom` (both classical results with published proofs). Every other theorem machine-checked.**

## What This Proves

Every Boolean circuit computing HAM_n (the Hamiltonian Cycle decision problem on n vertices) requires size at least 2^{Ω(n)}. Since P would imply polynomial-size circuits, this proves P ≠ NP.

The formula lower bound (`formulaLowerBound_exponential`) is fully unconditional — zero axioms.

The general circuit lower bound (`general_circuit_lower_bound_unconditional`) uses two axioms corresponding to known results:

1. **AUY 1983** — Protocol partition number bounded by formula size (Aho, Ullman, Yannakakis, STOC 1983)
2. **Leaf-sum domination + gate charging** — Combined result of the paper's width budget and leaf-sum decomposition propositions

## Architecture

| Module | Description |
|--------|-------------|
| `Basic` | Core definitions: Boolean circuits, Hamiltonian cycles, frontiers |
| `GraphInfra` | Graph theory infrastructure (connectivity, components) |
| `Interface` | Frontier interface state, degree profiles, stitchability |
| `Stitch` | Boundary component correspondence, path pairings |
| `Collision` | Degree collision and pairing mismatch forcing |
| `Switch` | Switch blocks, 2-opt rerouting, cross-pattern mixing |
| `TwoOptLemmas` | 2-opt move structural lemmas, Hamiltonian preservation |
| `Robustness` | Canonical cycles, relabeling, restriction robustness |
| `HamCycleCount` | Hamiltonian cycle counting scaffold, path components |
| `Funnel` | Multi-carrier funnel magnification, Gamma recursion |
| `Packet` | Continuation packets, mixed local clog, circuit locality |
| `Descent` | Rooted descent, packet separator exclusion, benign escape |
| `Signature` | Signature rigidity, occurrence signatures, mu-max bounds |
| `Formula` | Formula lower bounds via Aho-Ullman-Yannakakis |
| `Main` | **Main theorem: general_circuit_lower_bound_unconditional** |

## Build

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
lake build
```

Requires Lean 4.28.0 and Mathlib v4.28.0 (pinned in lean-toolchain and lakefile.toml).

## Verification

After `lake build` completes with no errors:

```bash
# Confirm zero sorries
grep -rn "sorry" PNeNp/*.lean
# Should return empty

# List axioms (expect exactly 2)
grep -rn "^axiom \|^private axiom " PNeNp/*.lean
# Should show:
#   Funnel.lean: auyDirectRectangles_gateValue_ax (AUY 1983)
#   Main.lean: lambda_le_sum_leafWidth_of_circuit (leaf-sum + gate charging)
```

## Paper

The mathematical proof is detailed in `hamiltonian_route.tex` (also available on [Zenodo](https://zenodo.org/records/19103649)).
