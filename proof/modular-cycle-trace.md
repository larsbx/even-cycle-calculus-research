# Modular adjacency and the exact finite cycle criterion

`formal/CycleTrace.lean` adds ten general finite lemmas connecting an event
list's departure trace to the existing `CycleEmbedding` predicate. Seven
formal controls are in `formal/CycleControls.lean`. No coefficient or
independent enumeration receipt changes.

## Exact criterion

Fix a finite event list E of positive length m and an initial product vertex v.
`trace(v,E)` indexes its m departure vertices by `Fin m`; `Next` is the
existing modular successor. The principal checked identity is

\[
\begin{aligned}
 &\operatorname{CycleEmbedding}(edge,\operatorname{trace}(v,E))
 \ \land\ \operatorname{finish}(v,E)=v\\
 &\quad\Longleftrightarrow\quad m\ge3
 \ \land\ \operatorname{Nodup}(\operatorname{before}(v,E))\\
 &\hspace{27mm}\land\ \forall a,\quad
 \operatorname{FactorWalk}(edge,a,v(a),\operatorname{project}(E,a))\\
 &\hspace{61mm}\land\
 \operatorname{advance}(v(a),\operatorname{project}(E,a))=v(a).
\end{aligned}
\]

This is `cycle_data_iff`. Closure appears explicitly on both sides. FactorWalk
requires actual factor edges and a genuine coordinate change at each step;
it does not require the projected walk to be simple. Both even backtracking
projections and odd triangle projections are allowed. Product injectivity is
tested on departures, with the final repeated root removed exactly once.

For m=8 this is an exact criterion for a rooted directed ordinary eight-cycle
traversal represented by finite coordinate events. It is a structural
equivalence, not a cardinality or motif-counting theorem. The earlier
projection/interleaving result uniquely reconstructs E from compatible
coordinate words and destination queues.

## Modular successor proof

`state(v,E,k)` executes the first k events. Only 0 through m are used by the
proof. The checked declarations are:

| Declaration in ECC.CycleTrace | Conclusion |
| --- | --- |
| `state_zero`, `state_end` | State zero is the initial vertex; state m is the endpoint. |
| `before_get_state`, `trace_eq_state` | Departure k is exactly the vertex after k events. |
| `valid_iff_state_edges` | Event validity is equivalent to Cartesian adjacency between every consecutive pair of states. |
| `trace_next_eq_state` | For a closed replay, the modular next departure equals state k+1, including the wrap from m-1 to zero. |
| `closed_trace_edges_iff` | Under closure, every modular trace edge is Cartesian exactly when all events are valid. |
| `closed_cycle_iff` | Under closure, CycleEmbedding is equivalent to m at least three, distinct departures and valid events. |
| `closed_cycle_iff_factor_walks` | The same criterion expressed through the projected factor walks. |
| `cycle_data_iff` | The self-contained criterion above, with no unspoken closure assumption. |

The wrap case uses k+1=m, state m=finish and finish=v. The other case uses
k+1<m, so reduction modulo m leaves k+1 unchanged. No limit, analytic or
infinite counting argument is involved.

## Checked controls and essential assumptions

The prior prism witness and paired-triangle witness are now certified as
`CycleEmbedding` instances, using the general criterion. Their lengths are
eight and their profiles are respectively (4,4) and (2,3,3). This does not
re-enumerate the corpus totals 6 or 2,700, or the 1,404-cycle (2,3,3) profile.

The colliding prism interleaving is formally rejected as a cycle. The closed
prism variant with a missing C4 factor edge is also rejected.

The closure control changes only the last destination of the prism replay
from coordinate value 0 to 1. Its eight departures, hence its modular cycle
trace, remain exactly the same. That trace is still a CycleEmbedding, while
the altered event replay neither closes nor follows its last factor edge.
Thus trace cyclicity alone cannot be used to infer event validity without
checking endpoint closure. This is why `cycle_data_iff` includes closure and
the conditional `closed_cycle_iff` requires it explicitly.

Finally, an edge traversed out and back has valid factor steps, closes and
has two distinct departure vertices. It is rejected as a CycleEmbedding
because m=2. The minimum-length assumption cannot be omitted even when
closure and injectivity hold.

## Verification and remaining count

Two new general lemmas use no axioms, three use only standard `propext`, and
five use standard `propext/Quot.sound`. All seven controls use standard
`propext/Quot.sound`. The exact audit checks 175 named declarations across
17 freshly compiled sources: 122 general lemmas, 48 finite controls and five
coefficient certificates. Choice, placeholders and native-evaluation axioms
are forbidden.

The [executable bridge](executable-coordinate-trace.md) now identifies the
literal modular-prefix vertex list and collision test for bounded positive-period
templates. Remaining work includes assembly with canonical extraction, whole
cyclic-pattern generator completeness, motif classification,
the finite cardinality and free 16-to-1 root/direction quotient.
These have not been inferred from the
structural cycle criterion. The general c8 formula remains working, with
unchanged source pin and shared theorem ownership. No external mathematical
acceptance or novelty is claimed.
