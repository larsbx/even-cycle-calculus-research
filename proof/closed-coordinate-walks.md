# Closed coordinate walks and endpoint normalization

`formal/ClosedWalk.lean` adds 19 general finite lemmas. Together with the event
projection/interleaving result, they characterize closed Cartesian walks by
their coordinate words and projected destination queues. They also identify
the positions on which a simple-cycle collision test must operate.
`formal/ClosedControls.lean` adds nine finite controls. These results do not
change the working status of the general c8 count.

## Exact closed-walk realization

Fix a finite coordinate vertex type `Vertex n`, a starting vertex v, an axis
word w and destination queues Q. `FactorWalk(edge,a,x,Q(a))` means that the
queue, read from x, follows factor edges and changes vertex at every step.
The explicit change condition is retained even for an arbitrary edge relation;
finite simple graph adjacency supplies it automatically.

Let `advance(x,L)` be x for an empty L, otherwise the final value of L.
Let `finish(v,events)` be the last product vertex reached by replay.
The checked identity is

\[
 \operatorname{finish}(v,E)(a)
 =\operatorname{advance}(v(a),\operatorname{project}(E,a)).
\]

Consequently `closed_walk_realizable_iff` proves:

\[
\begin{aligned}
 &\exists E:\quad \operatorname{axes}(E)=w,\quad
 \operatorname{project}(E)=Q,\\
 &\hspace{32mm} E\text{ replays a Cartesian walk from }v\text{ to }v\\
 &\quad\Longleftrightarrow\quad
 \operatorname{Compatible}(w,Q)\ \land\
 \forall a,\ \operatorname{FactorWalk}(edge,a,v(a),Q(a))
 \land\operatorname{advance}(v(a),Q(a))=v(a).
\end{aligned}
\]

The realizing event list is unique by the earlier `reconstruction_unique`
theorem. This is a finite closed-walk realization equivalence, with no parity
restriction on coordinate lengths. It permits repeated product vertices.
For unused coordinates the queue is empty, so closure holds automatically.
For used coordinates the final projected destination must be the root's
coordinate. A single used-coordinate step cannot both change and close.

| Declaration in ECC.ClosedWalk | Conclusion |
| --- | --- |
| `update_self`, `update_other` | An event changes only its stated coordinate. |
| `finish_coordinate`, `closure_iff` | Product closure is exactly coordinate closure, including empty queues. |
| `valid_iff_factor_walks`, `closed_valid_iff` | Valid product events are exactly the projected factor walks; closure can be added on both sides. |
| `coordinate_step_update`, `valid_head_cartesian` | Valid events give single-coordinate Cartesian edges. |
| `update_cartesian_iff`, `product_walk_iff_valid` | The validity condition is also necessary for the replayed Cartesian walk. |
| `closed_walk_realizable_iff` | Compatible closed factor walks have a realizing closed product walk, and conversely. |
| `replay_split`, `before_length`, `replay_length` | m events have m departure vertices and m+1 replayed vertices, including the endpoint. |
| `before_eq_dropLast`, `closed_replay_split` | Removing exactly the endpoint gives the departure list; a closed replay appends its initial vertex. |
| `trace_injective_iff_nodup` | The associated Fin m trace is injective exactly when its departure list has no repetitions. |
| `before_transitions` | For coherent transition records, that list is the original vertex path with its last vertex removed. |
| `closed_replay_not_nodup` | Every nonempty closed replay repeats a vertex if the endpoint is included. |

## Collision and endpoint conventions

`before(v,E)` lists the vertex immediately before each event. The formal
normalization identities are

\[
 |\operatorname{before}(v,E)|=|E|,\qquad
 \operatorname{replay}(v,E)=\operatorname{before}(v,E)
       \mathbin{+\!+}[\operatorname{finish}(v,E)].
\]

For a closed eight-step replay, the departure list has eight vertices and the
full replay has nine. Checking distinctness of all nine would reject every
ordinary eight-cycle. Checking closure and edges alone would accept colliding
walks. `trace_injective_iff_nodup` connects the correct departure-list condition
to the existing `TraceInjective` predicate. The
[executable bridge](executable-coordinate-trace.md) now proves its exact
correspondence with Shuffle.lean for bounded positive-period templates.
The [modular cycle extension](modular-cycle-trace.md) now proves the
modular-adjacency part of `CycleEmbedding` for this list-derived trace.

## Finite controls and relation to the enumeration corpus

The recorded C4 square K2 eight-cycle witness is now checked against the actual
C4 and K2 factor edges. It closes, and its eight departures are distinct; its
nine-vertex replay repeats the root. Its queues are
`(1,2,3,0)` and `(1,0,1,0)`.

A second interleaving first completes all four C4 steps, then all four K2
steps. It has exactly the same projected queues and valid factor edges and
closes, but returns to the product root after step four. Its departure list
is not injective. This proves that the collision correction depends on the
interleaving even after factor-walk validity and closure are fixed.

A third control has a closed replay but jumps from 1 to 3 in the C4 factor;
closure does not establish factor-edge validity.

In K2 square K3 square K3 the checked simple witness has events

```
(0,1),(1,1),(0,0),(1,2),(2,1),(1,0),(2,2),(2,0).
```

Its projected destination queues are `(1,0)`, `(1,2,0)`, `(1,2,0)`, giving
the profile `(2,3,3)`. Both odd projections traverse triangles. The control
checks factor edges, closure, distinct departures and, using the general
theorem, all three closed factor walks. This is a single exact witness in the
corpus's 1,404-cycle profile, not another enumeration of that count.

The unchanged Python regressions still compare all five original cases,
19 further products and 144 small labeled graph pairs with the working motif
formulas. No receipt or formula coefficient changes in this increment.

## Verification boundary

The 19 general declarations and nine controls are audited with exact standard
`propext` or `propext/Quot.sound` dependencies. Finite vertex-function equality
in the controls is decided by a bounded universal quantifier and function
extensionality, with no classical choice. The complete audit now checks
151 declarations in 15 freshly compiled sources: 105 general lemmas,
41 finite controls and five coefficient certificates.

Remaining formal obligations include assembling canonical extraction into
all generated bounded templates, whole cyclic-pattern and axis-word generator
completeness,
quotient-motif classification and the free 16-to-1 ordinary-cycle count.
The full c8 formula remains a working prose
derivation with finite exact checks. Source pin and theorem ownership are
unchanged; no external mathematical acceptance or novelty is claimed.
