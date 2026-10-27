# Finite Lean coefficient certificates

`Shuffle.lean` uses only Lean/Std, pinned to `leanprover/lean4:v4.34.0-rc2`.
From this directory, run `lean Shuffle.lean` with that toolchain.
CI downloads the exact official release archive and checks SHA-256
`3d011041203acacf300d343a39673f7d233743397993797c941346ae9e5df1a8`.

Declarations in namespace ECC:

- `paired_triangle_coefficient`: K(01,012,012)=312.
- `four_step_coefficients`: K(A,01,01)=(4,44,76,204), A ranging over
  the four patterns 0101,0102,0121,0123.
- `two_four_step_coefficients`: the complete 4 by 4 K-table for (4,4).
- `six_two_coefficients`: K for all 41 length-six patterns with an edge.
- `three_five_coefficients`: K for all 11 length-five patterns with a triangle.

Each theorem uses `by decide`, which creates a kernel-checked finite reduction
proof. There is no native evaluation axiom and no added axiom. The declarations'
transitive axioms are printed and checked in CI: exactly `[propext]` for
each of the five declarations. Coefficients are defined
through multiplicity-constrained word generation and pairwise distinct
reconstructed label tuples, without hardcoding the acceptable words.

These certificates do **not** formalize: completeness of restricted-growth
patterns; the general projection/quotient injection and shuffle bijection;
the 16-to-1 orbit quotient; five-/six-step motif classification; the general
graph formulas; or any source-owned graph-ring theorem. Those have their
separate working prose proof and Python checks. A successful finite Lean run
does not establish external mathematical acceptance or novelty.
