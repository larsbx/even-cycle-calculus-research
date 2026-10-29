# Finite ordinal compression of coordinate equality classes

`formal/RankCompression.lean` proves 20 general declarations extending the
canonical first-occurrence extraction. The representative alphabet is now
constructively compressed to `Fin r`, where r is exactly the number of
visited coordinate values. The new proofs also give the initial-zero and
append-admissibility conditions used by the equality-pattern enumerator.

For a nonempty finite trace v, let P(v) be the list of first-occurrence
representative positions in increasing order. It is obtained by filtering
`List.finRange` with the checked fixed-representative predicate. Set

```
r(v)       = length(P(v))
rank_v(a)  = the index of representative position a in P(v)
unrank_v(i)= the representative position at index i
encode_v(t)= rank_v(extract_v(t))
decode_v(i)= realize_v(unrank_v(i)).
```

All indexing is bounded by proof. There is no choice of an enumeration,
unbounded search, or division. The ordering is the traversal-position order,
not a supplied order on factor vertices.

## Checked statements

| Declaration (namespace ECC.RankCompression) | Conclusion |
| --- | --- |
| `positions_mem_iff` | List membership is exactly the representative predicate. |
| `positions_nodup`, `positions_sorted` | The list has no repetitions and is strictly increasing. |
| `unrank_rank`, `rank_unrank` | Both round-trip identities hold. |
| `rank_injective`, `unrank_injective` | Both maps are injective. |
| `rank_lt_implies`, `rank_lt_iff` | Ordinal order agrees exactly with representative-position order. |
| `decode_encode` | Decoding every encoded position recovers its original coordinate value. |
| `encode_representative`, `encode_surjective` | Every ordinal label actually occurs in the trace. |
| `decode_injective` | Distinct ordinal labels realize distinct coordinate values. |
| `encode_eq_iff` | Encoded labels are equal iff the original coordinate values are equal. |
| `initial_segment_seen` | Every label smaller than encode_v(t) occurred at a position before t. |
| `encode_zero` | The first ordinal label is zero. |
| `predecessor_seen` | A positive label j has an earlier occurrence of label j-1. |
| `fold_max_bounds` | A finite maximum fold bounds its initial value and all list members. |
| `append_bound` | The next label is at most one plus the maximum of preceding labels. |
| `enumerator_label_allowed` | The next label belongs to the exact finite candidate range used by growPatterns. |

The first two round trips give a finite bijection between the representative
subtype and `Fin r`. They do not assert that traversal positions are in
bijection with labels: coordinate values may repeat.

## Restricted-growth condition and enumerator interface

Let p be the list of encoded labels strictly before position t. The literal
formal append bound is

```
encode_v(t).val <= p.foldl Nat.max 0 + 1,
```

and hence

```
encode_v(t).val in List.range (p.foldl Nat.max 0 + 2).
```

This is the candidate-label range in `growPatterns` in `formal/Shuffle.lean`.
Together with `encode_zero`, it proves the restricted-growth normalization
requirements. The stronger `initial_segment_seen` rules out gaps in the
already visited alphabet; the bound does not merely allocate unused labels.

This proves candidate-label admissibility, not membership in the whole
generated cyclic-pattern list. The latter also requires adjacent/final
inequalities, deletion of stationary coordinate steps, and a formal connection
between the full typed trace and the executable list recursion.

## Exact controls and audit

`formal/RankControls.lean` reuses the existing finite trace `(0,1,0,2,1)`.
Three kernel-checked controls establish:

- its representative-position list is `(0,1,3)`;
- its compressed ordinal trace is `(0,1,0,2,1)`;
- ordinal 2 unpacks to representative position 3.

The new 23 declarations use exactly standard `propext` and `Quot.sound`.
The constructive equality-equivalence instance is selected explicitly for
the finite index bound, avoiding an order-derived instance that imports
choice. `formal/check.py` compiles all 21 source files with fresh local
imports and enforces all **238 exact named axiom sets**, rejecting any extra
axiom or missing declaration. No choice, placeholders or native-evaluation
axioms are permitted.

The [event extension](coordinate-event-shuffle.md) now proves projection,
interleaving and vertex-path replay for coherent transition records. Remaining
formal obligations include inverse normalization for arbitrary generated
templates, full product-cycle composition, motif classification and the free
16-to-1 ordinary-cycle count. The
[canonical membership bridge](canonical-pattern-membership.md) now checks the
forward coordinate-trace membership and injective assignment interface.
The [cyclic-pattern generator](cyclic-pattern-generator.md) now has whole-list
membership and uniqueness proofs. The
[executable bridge](executable-coordinate-trace.md) now proves prefix-index
trace and collision-test correspondence for bounded positive-period templates.
The [closed-walk extension](closed-coordinate-walks.md) supplies factor-edge
and closure conditions and the departure/endpoint normalization.
The general c8 formula stays working, with unchanged shared source pin and
theorem ownership. No external mathematical acceptance or novelty is claimed.
