# Lean coefficients and coordinate decoding

`Shuffle.lean` uses only Lean/Std, pinned to `leanprover/lean4:v4.34.0-rc2`.
From the repository root, run `python3 formal/check.py` with that toolchain.
Set `LEAN_BINARY` to an explicit compiler path when needed. This compiles all
nine Lean sources, rebuilding all local imports in a temporary directory,
and verifies 82 exact named axiom sets. It does not rely on a cached olean.
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

`CollisionBridge.lean` now proves eight general lemmas about finite coordinate
decoding: equality and single-coordinate-step reflection, unique changing axis,
edge preservation, injectivity and support reflection, simple-cycle decoding,
and fixed-shape assignment recovery when every label is used. See the exact
assumptions and declaration table in
[proof/coordinate-collision-bridge.md](../proof/coordinate-collision-bridge.md).
Four declarations use only standard `Quot.sound` via function extensionality;
four use no axioms. Edge preservation requires no nonedge preservation.

`CollisionControls.lean` adds six formal control declarations. They show why
edge preservation cannot replace injectivity and why unseen labels defeat
assignment recovery. Five use standard `propext` and `Quot.sound`; one uses no
axioms. The audit permits no choice, placeholders, added axioms or native
evaluation axioms. Existing coefficient audits remain unchanged.

`CanonicalTrace.lean` adds 15 general bounded first-occurrence extraction
lemmas. They prove reconstruction, injective realization, visited-label
surjectivity, equality-pattern invariance and uniqueness of normalized
first-position shapes. `CanonicalControls.lean` adds three finite controls
distinguishing first-position labels from contiguous ordinal labels and
showing failure under noninjective relabeling. All 18 use exactly standard
`propext` and `Quot.sound`. See
[the exact scope](../proof/canonical-coordinate-extraction.md).

The complete projection/extraction and shuffle bijection is **not** formalized.
`RankCompression.lean` now proves 20 general lemmas giving an order-preserving
bijection from representative subtypes to `Fin r`, exact reconstruction,
injective decoding, label surjectivity and the literal restricted-growth
candidate bound. `RankControls.lean` checks the finite representative list,
compressed ordinal word and inverse lookup. All 23 audits use exactly standard
`propext` and `Quot.sound`, without choice. See
[the rank-compression scope](../proof/ordinal-rank-compression.md).

`EventShuffle.lean` adds 17 general lemmas proving an exact finite bijection
between event lists and compatible coordinate words/destination queues, and
conditional replay of coherent vertex paths after stationary-step deletion.
`EventControls.lean` adds five formal controls, including the recorded prism
eight-cycle path, exhausted/leftover queues and nonstationary coordinates.
Their exact hypotheses and axiom sets are in the audit and
[proof/coordinate-event-shuffle.md](../proof/coordinate-event-shuffle.md).

Closing/edge conditions for compressed coordinate walks, root/endpoint alignment,
typed-shape/executable-encoding correspondence, restricted-growth completeness,
quotient-motif classification, the cardinality identity and the free 16-to-1
orbit quotient remain open. The full graph formula and source-owned graph-ring
theorems are not promoted. Kernel checks of the specified components do not
establish external mathematical acceptance or novelty.
