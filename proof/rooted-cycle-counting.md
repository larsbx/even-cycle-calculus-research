# Kernel c10 certificates and fixed-cycle root/direction counting

Internal research note, 2026-10-30. These results strengthen verification of
the candidate mixed-motif formulas. The coefficient values and standard
2m representation principle are not claimed as new mathematics. Priority
and independent review of the factor-motif expansion remain open.

## 1. Exact length-ten kernel certificates

`formal/TenCycle.lean` uses the unchanged literal `ECC.words`,
`ECC.vertices` and `ECC.distinct` definitions. `kernelAt` is the same
collision-filtered word count at a specified finite length. It does not use
the connected-partition recurrence, graph DFS, either partition-inversion
oracle, the Python receipt, native evaluation or an external arithmetic oracle.

The five certified identities are

| Profile | Canonical templates | Valid axis words |
|---|---|---:|
| (4,2,2,2) | A=0101,01,01,01 | 660 |
| (4,2,2,2) | B=0102,01,01,01 | 2562 |
| (4,2,2,2) | C=0121,01,01,01 | 4008 |
| (4,2,2,2) | D=0123,01,01,01 | 8310 |
| (3,3,2,2) | 012,012,01,01 | 12540 |

Directly reducing the full length-ten word list exhausted local memory.
The proof therefore establishes `countFrom_succ`, an exact prefix-extension
identity obtained from the literal generator's recursion, distribution of
filter over flatMap and list-length addition. `split_4222` and `split_3322`
apply it twice, for arbitrary input templates. No axis-word case is removed.

For each pattern tuple, sixteen certificates check all two-step prefixes,
then four row identities group them by the first axis. These eighty cell
certificates and twenty rows exhaust all two-step prefixes. Each suffix count uses the actual
collision test on the **whole prefix plus suffix**, with counters starting
at zero. Counting only the suffix would incorrectly discard prefix/suffix
collisions. The five final coefficients follow by rewriting the proven
decomposition with the four corresponding row certificates and adding.
Each row lives in a separate `C10Coefficients/` module, so the compiler
releases its reduction workspace before the next row. The shared source
`TenCycleBase.lean` proves the decomposition; `TenCycle.lean` imports and
combines the opaque row certificates. This changes proof resource use,
not the enumerated words or collision predicate.
The rows use `decide +kernel`: reduction is performed by Lean's proof kernel,
avoiding the redundant elaborator reduction. This is distinct from native
evaluation and introduces no native-evaluation axiom.

The eighty finite cell reductions and twenty row identities use exactly
`propext`. The three
decomposition declarations and five combined coefficient declarations use
exactly `propext/Quot.sound`. The source includes two further ground controls
with no axioms:

    660*2*8 = 20*528,
    (2562+4008)*2*8 = 20*5256,
    8310*8*8 = 20*26592,
    12540*36*4 = 20*90288.

The individual rooted B and C terms have remainders 12 and 8 modulo 20;
their sum has remainder zero. Thus the ordinary-cycle division must follow
the sum of these root-dependent categories. The existing formula is unchanged.

These are ground certificates. The existing canonical four-step inventory
and axis-word completeness interfaces remain available, but their assembly
with graph motif identification into an arbitrary-product counting theorem
is still a separate obligation.

## 2. Exactly 2m representations of a fixed injective trace

`formal/RootedCycle.lean` works with a trace v : Fin m -> Fin N. Both its
departure positions and host vertex labels are finite. A parameter is a pair
(r,b), where r : Fin m is the root and b selects forward or backward traversal.

The reindexing functions are defined by bounded arithmetic:

    forward(r,t)  = r+t       if r+t<m, otherwise r+t-m;
    backward(r,t) = r-t       if t<=r, otherwise m+r-t.

They stay in Fin m. At departure zero both recover r; both reindexing maps
are injective. For m>=3 their values at departure one are different.

Suppose v is injective and two reindexed traces agree. Comparing departure
zero and using injectivity recovers the same root. Comparing departure one
then recovers the same direction. Consequently all root/direction parameters
give different traces. This proof does not assume that a raw closed walk is
injective; injectivity is an explicit hypothesis.

An explicit bijection from Fin(2*m) to Fin m x Bool lists each root once in
each direction. `representations_length` proves that the resulting list has
length 2*m; `representations_nodup` proves no repetitions when m>=3 and v
is injective. `mem_representations_iff` characterizes its complete membership.
`representation_injective` proves every listed trace is still injective.

The adjacency argument is also checked. `forward_next` commutes with the
existing modular successor; `backward_next` reverses it. For any symmetric
adjacency relation, `representation_edges` transports every cyclic edge,
including the closing edge. Nonedge preservation is not required. Thus the
representations of a fixed simple finite cycle retain its cycle edges.

The file has eighteen general declarations and four finite controls, all
with exactly `propext/Quot.sound`. The controls certify:

* Injective eight- and ten-position traces give 16 and 20 distinct entries.
* At length two, directions coincide even for an injective trace.
* For the repeated trace 0101, roots zero and two give the same forward trace.
* Reversal of a directed triangle fails adjacency, isolating the symmetry
  assumption needed for undirected cycles.

## 3. What remains separate

This closes the fixed-trace representation multiplicity component. It does
not yet construct the partition of an arbitrary graph's rooted injective
walk inventory into ordinary-cycle classes, prove the corresponding global
cardinality sum, or formally transport coordinate-profile counts across those
classes. Those assembly steps remain distinct from the fixed-cycle theorem.

Other open formal obligations are arbitrary-template normalization inverses,
product extraction/shuffle composition, quotient-motif classification, the
connected-partition recurrence, and the factorial cancellation hypothesis
in `PartitionInversion.finite_inversion`. None is silently discharged by
the new coefficient certificates or the 2m representation theorem.

The mathematical claims in `simple-projection-sectors.md` remain working
general results. Their finite coefficients are now kernel-certified as well
as independently checked by product adjacency DFS and two partition-inversion
routes. Known counting principles remain attributed to prior work; no new
priority claim follows from completing a proof certificate.
