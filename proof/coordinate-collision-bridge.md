# Finite coordinate decoding: formal collision bridge

This component of the c8 proof is kernel-checked in
`formal/CollisionBridge.lean`. It applies to any finite number of coordinates,
any finite factor orders and any finite traversal length. It uses only Lean/Std;
the shared graph-ring source pin and theorem ownership are unchanged.

For coordinate a, take labels in `Fin(n_a)`, target vertices in `Fin(N_a)`,
and an **injective** assignment `f_a : Fin(n_a) -> Fin(N_a)`. A label shape
is a sequence `L : Fin(m) -> product_a Fin(n_a)`. Its decoded traversal is

```
D_f(L)(t)(a) = f_a(L(t)(a)).
```

## Exact statements and assumptions

| Declaration (namespace ECC.CollisionBridge) | Conclusion and assumptions |
| --- | --- |
| `decode_equal_iff` | With each f_a injective, D_f(x)=D_f(y) iff x=y. |
| `coordinate_step_iff` | With each f_a injective, exactly coordinate a changes in the decoded edge iff exactly a changes in the label edge. |
| `coordinate_axis_unique` | Two witnesses for a single-coordinate change identify the same coordinate. No factor assignments are needed. |
| `cartesian_adj_preserved` | Injective assignments preserving the declared label edges preserve Cartesian adjacency. No nonedge preservation is assumed. |
| `trace_injective_iff` | With each f_a injective, the decoded traversal has distinct vertices iff the label shape does. |
| `used_coordinate_iff` | With each f_a injective, a coordinate is nonconstant in the traversal iff it is nonconstant in the shape. |
| `decoded_cycle_iff` | For a prescribed closed label walk, edge-preserving injective factor assignments give a simple decoded cycle iff the label walk is a simple cycle. The formal predicate requires m>=3 and includes the last-to-first edge. |
| `assignments_recovered` | If every label in every coordinate is visited, two assignments producing the same rooted traversal are equal. This recovery statement does not require injectivity. |

`CartesianAdj` explicitly requires exactly one changing coordinate and a
declared edge in that coordinate. The lemmas allow arbitrary edge relations,
so in particular specialize to the finite simple undirected graphs in the
ordinary-cycle formula. `decoded_cycle_iff` assumes the closed label edges
are already present; it does not infer nonexistent label edges by reflecting
extra target edges. This preserves ordinary, non-induced conventions.

Equality of decoded vertices is equivalent to equality of all coordinate
labels. Thus the collision decision depends on the shape, not on which
allowed injective factor embeddings realize that shape. This supplies the
general graph-level justification for testing label collisions before
multiplying by injection counts in the working c8 derivation.

The recovery theorem gives a separate no-overcount fact for **one fixed,
fully visited label shape**. It is not the statement that two different
canonical shapes cannot encode the same rooted traversal.

## Formal negative controls

`formal/CollisionControls.lean` proves two failures of weakened assumptions:

1. The parity map from C4 onto K2 preserves all selected square edges. The
   square is an injective closed label traversal, but its image identifies
   traversal positions 0 and 2. Edge preservation alone cannot replace
   injective coordinate assignments.
2. A shape visiting only label 0 in a two-label coordinate cannot distinguish
   the injective assignments `0->0, 1->1` and `0->0, 1->2` into three vertices.
   Decoded traversals agree, but assignments differ. Recovery requires every
   label to be visited.

These are kernel-checked finite statements, not sampled Python observations.

## Formal scope and audit

The eight general declarations use either no axioms or Lean's standard
`Quot.sound` through function extensionality. The six control declarations
use either no axioms or standard `propext` and `Quot.sound`. They use no
choice, placeholders, added axioms or native-evaluation axioms. Together with
the five existing coefficient declarations and the canonical coordinate
extraction component, `formal/check.py` compiles and compares **37 exact named
axiom sets**; imports are built afresh in a temporary
directory. Hosted CI uses the unchanged, digest-pinned official compiler.

The general c8 formula remains **working**, not externally accepted. Open
formal obligations remain:

- Construct the typed shape from the executable shuffle/prefix-index encoding
  and connect its collision predicate to the checked finite tables.
- Rank-compress the now-checked canonical first-position coordinate
  representatives to ordinal labels and connect them to the compressed
  coordinate walks. The [coordinate-level extraction and recovery lemmas](canonical-coordinate-extraction.md)
  do not yet establish the full cycle/shuffle bijection.
- Verify completeness of the equality-pattern enumeration and the quotient
  motif isomorphism classification.
- Prove the finite cardinality identity and the free 16-to-1 root/direction
  quotient used for ordinary eight-cycle counts.

This component does not promote the source-owned symbol theorem or establish
literature/novelty or independent mathematical acceptance.
