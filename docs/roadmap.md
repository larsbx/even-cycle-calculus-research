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
formal work includes typed-pattern/executable-encoding correspondence,
motif isomorphism classification and the 16-to-1 counting quotient. No conjectured
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

## Subsequent gates

1. Broaden independent fixtures, preserve negative controls and exact conventions.
2. Write a claim-specific proof or counterexample record; distinguish conjecture
   from finite observations and working derivation.
3. If formalized, record exact Lean declarations, toolchain/dependency pins and
   transitive axioms. A checked conditional statement must list its assumptions.
4. Reconcile external literature and source manuscript provenance before asking
   for mathematical acceptance. Do not edit the source registry from this repo.
5. Update the central map with any changed interface or dependency revision.
