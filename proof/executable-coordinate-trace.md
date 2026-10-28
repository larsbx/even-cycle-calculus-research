# Literal prefix-index encoding and the collision test

`formal/ExecutableTrace.lean` adds 16 general finite lemmas connecting the
unchanged `ECC.vertices` and `ECC.distinct` code in Shuffle.lean to the typed
departure trace, its injectivity and the existing cycle criterion. Eight
controls are in `formal/ExecutableControls.lean`. This is a semantic bridge
for well-formed finite inputs; it is not a new cycle-counting formula.

## Finite inputs and exact correspondence

Fix q coordinates. Coordinate a has vertex type `Fin(n(a))`, a positive
period d(a), and a template

\[
 p_a:\operatorname{Fin}(d(a))\longrightarrow\operatorname{Fin}(n(a)).
\]

The template need not be injective. Repeated labels, backtracking and odd
periods are allowed. A counter pos(a) records the number of steps already
taken, and an axis word consists of `Fin q` values. Define the current vertex
by `read(p,pos)(a)=p_a(pos(a) mod d(a))`. A tick increments exactly the stated
coordinate counter. The corresponding event writes the template value at
the incremented counter in that coordinate.

`rawPatterns` lists all template values as natural numbers, in coordinate
order. `rawPos` lists all counters, and the raw word lists the axis values.
These arrays have exactly the coordinate count and the prescribed positive
row lengths. The theorem `vertices_eq_encoded_departures` proves

\[
\begin{aligned}
 &\operatorname{ECC.vertices}(\operatorname{rawPatterns}(p),
       \operatorname{rawWord}(w),\operatorname{rawPos}(pos))\\
 &\quad=\operatorname{map}(\operatorname{encode},
       \operatorname{before}(\operatorname{read}(p,pos),
                           \operatorname{events}(p,w,pos))).
\end{aligned}
\]

Here encode lists a product vertex's finite coordinate values. It is
injective. Both sides list departures, before the indicated axis step;
neither includes the final endpoint. The proof checks the actual list
`modify` and nested modular indexing in the executable, rather than replacing
the executable with another implementation.

Consequently `executable_injectivity_iff` proves that the literal
`ECC.distinct(ECC.vertices(...)) = true` is equivalent to `TraceInjective`
of the typed departure trace. This applies to every finite axis-word length
and every initial counter vector under the stated bounds, not only the
eight-step coefficient cases.

## Steps, endpoint and cycle criterion

| Declaration in ECC.ExecutableTrace | Conclusion |
| --- | --- |
| `encode_injective` | The list encoding preserves and reflects equality of product vertices. |
| `read_update` | Updating the stated coordinate equals reading all templates after its counter tick. |
| `get_modify_safe` | A structural bounded lookup identity for the literal list modification. |
| `raw_tick`, `raw_read` | Typed counters and template reads agree with their executable list forms. |
| `vertices_eq_encoded_departures` | The literal executable vertex list equals encoded typed departures. |
| `events_axes`, `events_length` | Generated events have exactly the supplied axis word and length. |
| `finish_events`, `endPos_coordinate` | The endpoint reads final counters; final counter a equals initial counter a plus its step count. |
| `closure_if_periods_divide_steps` | If every step count is zero modulo its positive template period, replay closes. |
| `distinct_iff_nodup`, `encoded_nodup_iff` | The literal Boolean collision test is list distinctness, which the encoding preserves and reflects. |
| `executable_collision_iff`, `executable_injectivity_iff` | Executable acceptance is exactly departure-list distinctness and trace injectivity. |
| `executable_cycle_iff` | The existing simple-cycle criterion can use the literal executable collision test. |

The endpoint condition includes zero steps and any whole number of template
periods. In the coefficient cases, using a coordinate exactly its template
length gives closure. This proves the implication under the stated step-count
hypothesis; it does not yet prove multiplicity correctness or completeness of
the `words` generator.

`executable_cycle_iff` keeps length at least three, factor-edge validity and
coordinate closure explicit. A passing collision test alone does not prove
these other conditions. The theorem combines the literal test with the
previously proved modular cycle criterion; it does not divide walks by 16.

## Exact controls and input bounds

The prism control uses raw templates `(0,1,2,3)` and `(0,1,0,1)` and the
alternating eight-axis word. Generated events equal the prior recorded prism
witness and the literal collision test passes. The colliding interleaving of
the same templates reproduces the prior colliding events and fails that test.

The paired-triangle control uses raw templates `(0,1)`, `(0,1,2)`, `(0,1,2)`
and the prior `(2,3,3)` witness word. Events match exactly and the literal test
passes. The general period/step theorem separately certifies closure for both
the prism and paired-triangle data.

Malformed inputs illustrate why the hypotheses matter. The raw function is
total through default natural-number values: an empty template can output
zeros, and an invalid axis can leave counters unchanged. A one-step invalid
axis example even passes the collision test. That is not an ordinary-cycle
counterexample: it has neither a legal coordinate event nor the minimum
cycle length. Such inputs cannot inhabit the bounded positive-period data
used by the general correspondence theorem. No invalid-input behavior or
production coefficient code is changed in this increment.

## Verification and remaining obligations

Of the 16 general declarations, one uses no axioms, two use only standard
`propext`, and 13 use standard `propext/Quot.sound`. Four controls use
`propext`; four use `propext/Quot.sound`. The pinned Std `getElem_modify`
lemma imports classical choice, so the bridge instead proves its required
bounded identity directly by structural recursion. No choice dependency is
admitted by the audit.

The complete audit checks 151 named declarations across 15 fresh source
builds: 105 general lemmas, 41 finite controls and five coefficient
certificates. The literal Shuffle.lean source and both arithmetic receipts
are unchanged. Source pin and theorem ownership remain unchanged.

Still open are the formal assembly from canonical coordinate extraction to
all generated bounded templates, whole cyclic-pattern and axis-word generator
completeness, quotient-motif classification and the finite cardinality/free
16-to-1 quotient. In particular, finite coefficient certificates and this
general encoding equivalence do not by themselves establish the full ordinary
c8 formula. It remains working, with external mathematical acceptance and
novelty separate.
