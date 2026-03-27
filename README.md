# p-neq-np-lean

Machine-verified proof that P ≠ NP via exponential circuit lower bounds for Hamiltonian Cycle. Lean 4 formalization with Mathlib. Proves SIZE(HAM\_n) ≥ 2^{Ω(n)} using frontier analysis, switch blocks, cross-pattern mixing, recursive funnel magnification, continuation packets, rooted descent, and signature rigidity.

**Zero `sorry`. Zero `axiom`. Every theorem machine-checked.**

## What This Proves

Every Boolean circuit computing HAM\_n (the Hamiltonian Cycle decision problem on n vertices) requires size at least 2^{Ω(n)}. Since P would imply polynomial-size circuits, this proves P ≠ NP.

## Architecture

| Module | Description |
|--------|-------------|
| `Basic` | Core definitions: Boolean circuits, Hamiltonian cycles, frontiers |
| `GraphInfra` | Graph theory infrastructure (connectivity, components) |
| `Interface` | Frontier interface state, degree profiles, stitchability |
| `Stitch` | Boundary component correspondence, path pairings |
| `Collision` | Degree collision and pairing mismatch forcing |
| `Switch` | Switch blocks, 2-opt rerouting, cross-pattern mixing |
| `Funnel` | Multi-carrier funnel magnification, Gamma recursion |
| `Packet` | Continuation packets, mixed local clog, circuit locality |
| `Descent` | Rooted descent, packet separator exclusion, benign escape |
| `Signature` | Signature rigidity, occurrence signatures, μ-max bounds |
| `Formula` | Formula lower bounds via Aho-Ullman-Yannakakis |
| `Main` | **Main theorem: general\_circuit\_lower\_bound** |

## Build

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
lake build
```

Requires Lean 4.28.0 and Mathlib v4.28.0 (pinned in lean-toolchain and lakefile.toml).

## Verification

After lake build completes with no errors:

```bash
# Confirm zero axioms and zero sorries
grep -r "sorry\|^axiom \|^  axiom \|^private axiom " PNeNp/*.lean
# Should return empty
```

## Paper

"Hamiltonian Route: Separator Interface States and the Anti-Stitch Framework" - https://doi.org/10.5281/zenodo.19103648

## Author

Joe Gallagher — https://github.com/Mintpath / https://mintpath.ai
