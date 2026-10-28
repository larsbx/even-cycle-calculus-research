# Canonical first-occurrence extraction of a coordinate trace

`formal/CanonicalTrace.lean` proves 15 general declarations about a finite,
nonempty coordinate trace, independently of the c8 coefficient tables. The
algorithm scans only a bounded prefix. It uses neither an unbounded search
nor a choice of representatives. The three exact control declarations are
in `formal/CanonicalControls.lean`.

Take `v : Fin(m+1) -> A` with decidable equality on values. In the graph
application A is a finite factor-vertex set. The proofs require no enumeration
of A and all scans are bounded by a traversal position at most m. Define

```
first_v(t) = the least s <= t with v(s) = v(t).
```

The implementation maintains the earliest match while scanning positions
0,...,t. `scan_spec` proves the maintained position stays in the prefix,
all earlier positions fail to match the target, and a nonmatching result
must be the final prefix position. For target v(t), the final alternative
cannot occur, so the result matches v(t).

## Checked extraction and recovery statements

| Declaration (namespace ECC.CanonicalTrace) | Conclusion |
| --- | --- |
| `scan_spec` | Bounded scan invariant, including the no-earlier-match condition. |
| `first_le` | first_v(t) <= t. |
| `first_value` | v(first_v(t)) = v(t). |
| `first_minimal` | v(s)=v(t) implies first_v(t) <= s, including s after t. |
| `first_eq_of_value_eq` | Equal values have the same first position. |
| `first_eq_iff` | first_v(s)=first_v(t) iff v(s)=v(t). |
| `first_idempotent` | first_v(first_v(t)) = first_v(t). |
| `realize_extract` | Decoding the extracted representative recovers v(t). |
| `extract_representative` | Extracting a representative position recovers that representative. |
| `realize_injective` | Distinct representative labels realize distinct coordinate values. |
| `first_injective_relabeling` | An injective relabeling preserves every first-position label. |
| `first_equality_relation` | Two traces with the same equality relation have identical first-position encodings, even in different value types. |
| `normalized_shape_recovered` | A shape that labels each class by its first position and has the trace's equality relation is recovered by extraction. |
| `canonical_shape_unique` | Any two such normalized shapes for the same trace are equal. |
| `extract_surjective` | Every representative label is visited by extraction. |

The representative alphabet is the explicit finite subtype

```
Representative(v) = { r : Fin(m+1) | first_v(r) = r }.
extract_v(t) = first_v(t), with its fixed-position proof.
realize_v(r) = v(r).
```

Thus the coordinate equality classes have canonical finite representative
labels, all labels are visited, and their realization is injective. The
two round-trip identities above are the coordinate-level extraction/decoding
component. This is not a bijection between traversal positions and labels:
several positions may realize the same coordinate vertex.

The `canonical_shape_unique` hypotheses specify normalization and the exact
coordinate equality relation. They do not assume the desired shape equality.
Applying these statements separately to each coordinate gives its canonical
equality partition, including stationary positions in the full product trace.

## Representation boundary and controls

For the finite trace `(0,1,0,2,1)`, the checked first-position encoding is
`(0,1,0,3,1)`. The contiguous restricted-growth ordinal encoding remains
`(0,1,0,2,1)`. The control `positions_are_not_ordinals` certifies their
inequality at position 3. There is no identification of these encodings.

The control `noninjective_relabel_changes_first` sends label 1 to 1 and
labels 0 and 2 to 0. Position 3 then has first position 0 rather than 3.
This certifies that the injectivity hypothesis in relabeling invariance
cannot be dropped. `first_positions` independently kernel-checks the full
five-position example above.

## Scope and next obligation

All 18 new declaration audits list only standard `propext` and `Quot.sound`;
there is no choice, placeholder, added axiom or native-evaluation axiom.
`formal/check.py` now checks the complete exact set of 127 named declarations,
rebuilding imported local modules in a temporary directory.

This component's representation is a subtype of traversal positions. The
[rank-compression extension](ordinal-rank-compression.md) now proves its
bijection with a contiguous `Fin r` label set and the enumerator's candidate
append bound. [Event projection and replay](coordinate-event-shuffle.md) now
check stationary-step deletion and coordinate-word recovery for coherent
transition records. The [closed-walk extension](closed-coordinate-walks.md)
supplies factor-edge and closure conditions and endpoint normalization. Full
correspondence with `Shuffle.lean` remains open. So do quotient-motif
classification and the free 16-to-1 cardinality quotient. In particular this
does not yet prove the full product-cycle/shuffle counting bijection.

The general c8 formula keeps its working status. Source pin and shared theorem
ownership are unchanged; no external mathematical acceptance or novelty is
claimed.
