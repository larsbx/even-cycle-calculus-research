# Research roadmap

## Delivered bootstrap

Pinned source references, separate claim authority, exact first experiment,
deterministic receipt, and independent replay instructions.

## Delivered lower-support increment

Working complete lower-support formulas, with an explicit projection/shuffle
bijection and finite coefficient derivation, are in
`proof/c8-lower-support.md`. Two- and three-coordinate terms distinguish
repeated edges, wedges, squares, paired triangles, and the five six-step
quotient motifs. Regressions compare the formulas to the unchanged independent
enumeration corpus. The pinned source owns the four-coordinate term.

## Next mathematical obligation

Independently review the general bijection and finite coefficient completeness;
reconcile prior literature; formalize the graph-level extraction/decoding
bijective count and five-/six-step quotient classification. Lean certificates
cover all five raw coefficient tables and now eight general coordinate-decoding
lemmas (collision/support reflection, edge preservation, cycle decoding and
fixed-shape assignment recovery). Six formal controls certify essential
assumptions. A further 15 general first-occurrence lemmas prove canonical
coordinate extraction and uniqueness in a first-position representation;
three controls delimit its encoding and injectivity assumptions. Remaining
formal work includes arbitrary-template normalization inverses, product-cycle composition,
motif isomorphism
classification and the 16-to-1 counting quotient. No conjectured
lower-support term remains in the displayed working decomposition.

Ordinal rank compression is now checked by 20 general lemmas and three finite
controls. The maps to/from `Fin r` are inverse and preserve equality and
representative order. Every ordinal is used, the first is zero, and subsequent
labels lie in the exact candidate range used by `growPatterns`. This is not
yet membership in the whole generated cyclic-pattern list.

Event projection/interleaving is now checked by 17 general lemmas and five
finite controls. Compatible coordinate words and destination queues have a
unique event realization; projection and replay recover coherent vertex paths
after stationary-step deletion. This does not automatically establish closed
coordinate-walk conditions or injectivity of the product path.

Closed coordinate-walk validity and closure are now checked by 19 general
lemmas and nine controls. Exact compatible word/queue data realize a unique
closed Cartesian walk iff every queue follows factor edges and closes. The
endpoint is removed exactly once; departure-list distinctness is equivalent
to trace injectivity. A colliding interleaving with the same prism queues and
a simple paired-triangle witness isolate the remaining cycle condition.
See `proof/closed-coordinate-walks.md`.

Modular cycle adjacency is now checked by ten general lemmas and seven
controls. For a closed event replay, the departure trace is a CycleEmbedding
exactly when its length is at least three, its departures are distinct and
its factor steps are valid. A self-contained criterion includes coordinate
closure on both sides. Changing just the final destination demonstrates why
closure cannot be inferred from the departure trace. See
`proof/modular-cycle-trace.md`.

The literal prefix-index trace and collision test are now connected to the
typed departure trace by 16 general lemmas and eight controls, for finite
bounded positive-period templates. Period-divisible coordinate step counts
give endpoint closure, including zero steps. Prism, colliding and paired-triangle
inputs match exactly; malformed default inputs isolate the required bounds.
See `proof/executable-coordinate-trace.md`. The generator and forward
canonical membership continuations below supply their specified interfaces.
Inverse/product composition and cardinality proofs remain open.

The literal axis-word generator now has 17 general lemmas and seven controls.
It emits exactly the bounded words with the requested multiplicities, each
once; collision filtering preserves uniqueness. Every emitted word constructs
a typed coordinate word with exactly those step counts. This closes axis-word
completeness. See `proof/axis-word-generator.md`.

The literal cyclic restricted-growth pattern generator now has 16 general
lemmas and seven controls. Its output is exactly the zero-first finite words
satisfying all prefix append bounds, unequal neighbors and unequal endpoints,
with no duplicates. The four four-step patterns and the 11/41 length-five/six
inventories are checked directly. See `proof/cyclic-pattern-generator.md`.
The coordinate membership continuation below supplies the forward canonical
extraction interface; inverse/product composition and the counting quotient
remain open.

Canonical coordinate-trace membership is now checked by 22 general lemmas
and ten controls. A trace with unequal neighbors and unequal endpoints
normalizes to a generated word exactly once, with injective reconstruction,
all labels visited and a unique assignment for that template. Canonical words
agree exactly when source equality patterns agree. Source selected steps are
preserved, with no inducedness requirement. See
`proof/canonical-pattern-membership.md`. Inverse normalization for arbitrary
generated templates, full product-cycle composition, motif classification
and the cardinality quotient remain open.

## Subsequent gates

The explicit novelty objective now has a scoped continuation in
[simple-projection-sectors](../proof/simple-projection-sectors.md): all-length
simple-coordinate sectors, the complete paired-triangle profile family and
the complete c10 support-four formula. Connected-partition enumeration and
known hypercube specializations are credited to prior work. New formula
priority and independent review are open, separate gates. The finite receipt
and new interval-collision formal lemma do not close those gates.

Next focused obligations are to independently review the component/gap
bijection, certify the new c10 coefficient sums in the proof kernel, and
formalize the finite ordinary-cycle quotient. The original c8 extraction
composition and motif-classification obligations remain active.

The independent partition-lattice comparison is delivered in
`proof/partition-inversion.md`: all 168 existing product cases agree profile by
profile with the old DFS, motif formulas and recorded receipts where present;
five additional boundary cases also pass. This uses the established Möbius
identity with weighted quotient edges, not the shuffle kernel. It strengthens
finite reproducibility without closing arbitrary-template inverses,
product-cycle composition, motif classification, the formal orbit quotient,
external mathematical review or novelty review.

1. Broaden independent fixtures, preserve negative controls and exact conventions.
2. Write a claim-specific proof or counterexample record; distinguish conjecture
   from finite observations and working derivation.
3. If formalized, record exact Lean declarations, toolchain/dependency pins and
   transitive axioms. A checked conditional statement must list its assumptions.
4. Reconcile external literature and source manuscript provenance before asking
   for mathematical acceptance. Do not edit the source registry from this repo.
5. Update the central map with any changed interface or dependency revision.

## Independent partition-lattice comparison delivered

The new histogram-assisted quotient-hom zeta and explicit Mobius inversion
recovers the c8 corpus, all 144 small graph pairs, and both c10 support-four
profiles, including the raw coefficients 660,2562,4008,8310,12540. A separate
quotient-block CSP oracle cross-checks the zeta route. Twelve Lean declarations
include conditional finite inversion transport with an explicit cancellation
hypothesis. Six regression tests preserve counting conventions. See
[the check note](../proof/partition-lattice-check.md). No formula discrepancy
was found; general graph cardinality formalization and expansion novelty
review remain open.
