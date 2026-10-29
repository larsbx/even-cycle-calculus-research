# Cyclic restricted-growth pattern completeness

`formal/PatternGenerator.lean` adds 16 general finite lemmas for the unchanged
`ECC.growPatterns` and `ECC.patterns` functions in Shuffle.lean. The result
characterizes their entire output lists by positionwise prefix conditions
and proves that no output word is emitted twice. Seven finite controls are
in `formal/PatternControls.lean`.

## Explicit semantic condition

For an initial list p and a finite extension t, `Extension(p,t)` means that,
for every index i < length(t), with previous prefix s = p ++ take(i,t),

\[
 t_i < \operatorname{foldl}(\max,0,s)+2,
 \qquad t_i\ne\operatorname{last}(s).
\]

For the canonical wrapper p=(0), the first condition allows exactly the labels
0 through one plus the previous maximum. The second excludes equality with
the immediately previous label. It permits nonadjacent repeats, backtracking
projections and odd lengths. Define `CyclicPattern(w)` by

\[
 \exists t,\quad w=(0)::t,\quad \operatorname{Extension}((0),t),
 \quad \operatorname{last}(w)\ne0.
\]

This is a positionwise condition on the complete finite word; it is not
defined by membership in either generator. It expresses the usual zero-first
restricted-growth convention, internal properness and the final closing
inequality. The closing condition applies to a coordinate projection: it
ensures the last projected vertex differs from its root before the last
factor edge returns to that root. It does not require all projected labels
to be distinct.

## Checked completeness and uniqueness

`mem_grow_iff` proves, for every finite extension length k and initial list p,

\[
\begin{aligned}
 w\in\operatorname{growPatterns}(k,p)
 \ \Longleftrightarrow\ \exists t,\quad
 &w=p\mathbin{+\!+}t,\quad |t|=k,\\
 &\operatorname{Extension}(p,t),\quad
 \operatorname{head}(w)\ne\operatorname{last}(w).
\end{aligned}
\]

For the actual canonical wrapper, `mem_patterns_iff` gives the exact all-length
criterion

\[
 w\in\operatorname{ECC.patterns}(m)
 \quad\Longleftrightarrow\quad |w|=m\ \land\operatorname{CyclicPattern}(w).
\]

It covers lengths zero and one as well: neither has an accepted word.
`grow_nodup` and `patterns_nodup` prove uniqueness of enumeration. Branches
with different appended labels are disjoint because those labels occupy the
same next position after their common initial prefix. Induction gives unique
outputs within each branch. These statements concern normalized equality
words; they do not classify the associated quotient motifs up to isomorphism.

| Declaration in ECC.PatternGenerator | Conclusion |
| --- | --- |
| `extension_nil`, `extension_cons_iff` | Positionwise prefix conditions decompose exactly into a head condition and the remaining extension. |
| `mem_grow_zero`, `mem_grow_succ` | Exact literal generator membership for the base and append cases. |
| `mem_grow_iff` | Full extension soundness/completeness and final closing condition. |
| `grow_length`, `grow_prefix` | Every output has its prescribed extension length and retains the initial prefix. |
| `grow_branches_disjoint`, `pattern_branch_mem`, `pattern_branches_disjoint` | Distinct appended-label branches have no common output, including the executable neighbor guard. |
| `grow_nodup` | Arbitrary finite extension enumeration has no repeated words. |
| `cyclic_starts_zero`, `cyclic_length_ge_two`, `patterns_zero` | The semantic canonical pattern starts at zero and has length at least two; the literal zero-length inventory is empty. |
| `mem_patterns_iff`, `patterns_nodup` | The canonical wrapper is complete and emits each accepted word once. |

The prior ordinal compression proves the literal next-label candidate bound.
These new theorems establish the whole generator's semantics and uniqueness.
They do not silently supply the remaining composition from arbitrary graph
cycles through stationary-step deletion, canonical extraction and all bounded
templates. The [canonical membership continuation](canonical-pattern-membership.md)
now checks the forward coordinate-trace membership and assignment interface.
Arbitrary-template normalization inverses and full product composition remain open.

## Exact controls

The four-step inventory is exactly `(0101,0102,0121,0123)`, reusing the
existing A, B, C, D definitions. Kernel reductions check inventory sizes

| Length | Patterns |
| --- | ---: |
| 0 | 0 |
| 1 | 0 |
| 2 | 1 |
| 3 | 1 |
| 4 | 4 |
| 5 | 11 |
| 6 | 41 |

The words `01234` and `012034`, used for the pentagon and paired-triangle
quotient walks, occur once. This verifies the selected equality words;
it is not a new motif-isomorphism classification theorem.

Four negative controls reject `0112` (adjacent repetition), `0120` (equal
first/last labels), `0212` (skipped first-appearance label), and `1010`
(nonzero first label). In contrast, the accepted pattern `0101` demonstrates
that repeated nonadjacent coordinate labels are allowed. Thus no
simple-projection-only or even-projection-only shortcut is introduced.

## Verification and acceptance boundary

Four general declarations use no axioms, one uses standard `propext`, and 11
use `propext/Quot.sound`. Two controls use no axioms and five use
`propext/Quot.sound`. The full audit checks 238 named declarations in 22 fresh
source builds: 165 general lemmas, 68 finite controls and five coefficient
certificates. No choice, placeholders or native-evaluation axioms are allowed.
The literal generators, both arithmetic receipts and coefficient code remain
unchanged. Source pin and theorem ownership are unchanged.

PR #3's preceding 175-declaration increment passed both hosted jobs at exact
head `4d3d85b0a51828bcb80ebca91b8b749dc6bad914` in
[run 40803497078](https://github.com/larsbx/even-cycle-calculus-research/actions/runs/40803497078)
and merged as `acb8fe4e9806d18dc357ac98554e47ad31b5b905`. Those checks do not
replace hosted acceptance for this extension's own final head.

Remaining work is arbitrary-template normalization inverses, full product-cycle
composition, quotient-motif classification and the finite cardinality/free
16-to-1 quotient. The full
ordinary c8 formula remains working; external mathematical acceptance and
novelty remain separate.
