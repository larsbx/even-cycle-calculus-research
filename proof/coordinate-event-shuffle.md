# Finite coordinate-event projection and exact interleaving

`formal/EventShuffle.lean` adds 17 general declarations for finite coordinate
event lists and vertex-path replay. The result is independent of the numerical
c8 coefficients. It proves exact event projection/interleaving and conditional
recovery of the original vertex path after deleting stationary coordinate steps.
Five finite controls are in `formal/EventControls.lean`.

## Finite data and exact event bijection

Coordinates are a : Fin q, with vertices in Fin(n_a). A coordinate event is
a dependent pair `(a,u)`, where u is the destination vertex in coordinate a.
The functions are:

```
axes(events)       = the coordinate word in chronological order
project(events,a)  = the destinations of events in coordinate a, in order
steps(word,a)      = the number of occurrences of a in the word
Compatible(word,Q) = for every a, length(Q(a)) = steps(word,a).
```

`weave(word,Q)` consumes the first destination in Q(a) for each a in the
word. It returns either failure from an exhausted queue, or an event list
and all remaining queues. Every list and vertex alphabet is finite.

The checked statements give:

| Declaration (namespace ECC.EventShuffle) | Conclusion |
| --- | --- |
| `project_head`, `project_other` | A head event contributes exactly to its own coordinate. |
| `project_length`, `projection_compatible` | Every event list yields exactly compatible data. |
| `queue_after_project_head` | Consuming the projected head leaves the tail projections. |
| `weave_project` | Interleaving an event list's word and projections returns that exact list and empty residual queues. |
| `weave_sound` | A successful interleaving has the requested word; each initial queue equals its consumed projection followed by its residual queue. |
| `compatible_tail` | Consuming the requested head preserves compatibility with the remaining word. |
| `weave_complete` | Compatible input always interleaves successfully and consumes every queue. |
| `compatible_reconstruction` | Compatible word/queues have a realizing event list. |
| `reconstruction_unique` | Equal coordinate words and projections imply equal event lists. |
| `reconstruction_iff_compatible` | Realizability is equivalent to the exact coordinate-length condition. |

Together, compatibility, reconstruction and uniqueness prove a finite bijection
between event lists and pairs `(word,Q)` satisfying Compatible. This is the
event-level bijection; it is not yet an ordinary-cycle counting formula.

Residual queues matter. A decoder returning an event list is not by itself
an exact inverse: unused supplied values must be excluded. The compatibility
condition is checked for every coordinate, including unused ones.

## Deleting stationary steps and recovering the vertex path

A transition record consists of an axis a and a full destination vertex w.
Starting from v, `Coherent(v,records)` requires each record to change exactly
its stated coordinate and leave every other coordinate unchanged, using the
existing `CoordinateStep` predicate. It does not require or infer factor edges.

`transitionEvents` retains only `(a,w(a))` from each transition. `project`
then deletes every event stationary in a given coordinate. The root of that
coordinate walk is supplied by the starting vertex v(a); its destination
queue is `project(transitionEvents(records),a)`.

The remaining checked declarations are:

| Declaration | Conclusion |
| --- | --- |
| `update_of_stationary` | Updating the recorded coordinate recovers the full destination when all other coordinates are stationary. |
| `update_of_coordinate_step` | The same conclusion follows from CoordinateStep. |
| `transition_axis_word` | Extraction recovers the recorded coordinate word exactly. |
| `replay_transitions` | Replaying extracted events recovers the initial vertex and every recorded destination vertex. |
| `weave_replay_transitions` | Projection, interleaving and replay together recover that whole vertex path. |

These are proved for every finite list, not fitted to examples. A graph walk
whose transitions satisfy CartesianAdj supplies the needed single-coordinate
conditions; graph adjacency and cycle properties retain their separate formal
predicates. The current result does not independently prove that every
compressed coordinate walk is closed or that the product path is injective.

## Controls, normalization and remaining interface

The finite prism control reproduces the recorded C4 square K2 c8 witness:

```
(0,0),(0,1),(1,1),(1,0),(2,0),(2,1),(3,1),(3,0),(0,0).
```

Its projected destination queues are `(1,2,3,0)` and `(1,0,1,0)`. The
control checks exact reconstruction of all nine displayed vertices, including
the final root. Further controls certify that:

- a queue missing its final value causes decoding to fail;
- an extra value can remain after successful decoding, and violates Compatible;
- a transition changing two coordinates cannot be recovered by one stated
  coordinate event.

All 22 new declarations have exact audits using only standard `propext` and,
where function extensionality is needed, `Quot.sound`. The full audit checks
**110 named declarations across 11 sources**, rebuilding imports in a
temporary directory. There is no choice, placeholder or native-evaluation
axiom. Source pin, arithmetic receipts and theorem ownership are unchanged.

The [closed-walk continuation](closed-coordinate-walks.md) now proves the
closing and factor-edge conditions and normalizes the endpoint and departure
list. The remaining interface connects ordinal patterns to the executable
prefix-index collision test and proves whole cyclic-pattern generator
completeness. Motif classification and the free
16-to-1 cardinality quotient also remain open. The general c8 formula keeps
working status; no external mathematical acceptance or novelty is asserted.
