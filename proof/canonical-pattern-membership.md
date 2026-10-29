# Canonical coordinate traces enter the generated inventory

`formal/NormalizedPattern.lean` adds 22 general finite lemmas connecting the
existing first-occurrence/ordinal encoding to the literal cyclic-pattern
generator. Ten controls are in `formal/NormalizedControls.lean`.

## Coordinate trace convention

The input is a nonempty finite coordinate trace
`v : Fin(m+1) -> Fin N`. It lists the vertices before successive coordinate
steps, omitting the final repeated root. Thus a triangle is represented by
three vertices, not by those three followed by its root again. `Proper(v)`
requires unequal consecutive vertices and an unequal last/first pair. It
does not require all vertices to be distinct: projected walks may revisit
vertices, including the root at an internal position.

Actual factor-edge validity is a separate condition on the source graph.
The encoding theorems need its equality information; they do not infer graph
edges from inequalities. Stationary-step deletion and the full product trace
are not inputs synthesized by this component.

## Exact generator membership

Use the existing ordinal `encode(v,t)` and injective `decode(v,label)` from
RankCompression. Define the literal list

\[
 W(v)=[\operatorname{val}(\operatorname{encode}(v,t))]_{t=0}^{m}.
\]

The checked criterion `normalized_mem_iff_proper` is

\[
 W(v)\in\operatorname{ECC.patterns}(m+1)
 \quad\Longleftrightarrow\quad \operatorname{Proper}(v).
\]

It is a general statement for every finite source alphabet and positive trace
length, not a lookup on the four-, five- or six-step fixtures. The proof
identifies RankCompression.prefixLabels with the actual list prefix used by
the generator, transfers the existing append bound to each position, and
uses equality reflection for the adjacent and closing inequalities. The
converse reflects those inequalities back to the source trace. The existing
generator uniqueness theorem then gives exactly one occurrence of W(v).

`word_eq_iff_equality` also proves, across possibly different finite source
alphabets,

\[
 W(v)=W(w)\quad\Longleftrightarrow\quad
 \forall s,t,\ v_s=v_t\ \Longleftrightarrow\ w_s=w_t.
\]

Thus the canonical output depends exactly on the source equality pattern,
rather than on the numeric names of its vertices.

## Injective assignment and selected steps

`canonical_factorization` constructs a finite label count r, a template
`p : Fin(m+1) -> Fin r` and an assignment `f : Fin r -> Fin N` with:

- the template's raw word in the literal generated inventory;
- `f(p(t)) = v(t)` at every position;
- f injective;
- every label visited by p;
- uniqueness of f among assignments reconstructing v from this fixed p.

The construction reuses encode/decode and their existing reconstruction,
injectivity and surjectivity proofs. Assignment uniqueness follows from
visiting every label; no unused labels are introduced.

`SelectedStep(v,i,j)` records an actual cyclic template step, including the
last-to-root step. If the original trace follows a specified factor-edge
relation at every cyclic step, `selected_step_preserved` proves that decode
preserves these selected steps. `selected_loopless` excludes selected loops
when that source edge relation is loopless. No nonedge-preservation assumption
is made. These are selected-step statements, not a quotient-motif
isomorphism classification.

| Declaration in ECC.NormalizedPattern | Conclusion |
| --- | --- |
| `word_length`, `tail_length`, `word_split` | Exact list length and initial-zero decomposition. |
| `prefix_labels_eq_take`, `word_take_last`, `word_last`, `initial_prefix` | The bounded rank prefix and endpoint conventions match the literal list conditions. |
| `normalized_extension`, `normalized_closing`, `normalized_cyclic` | A proper source trace satisfies every generator bound and inequality. |
| `normalized_mem_patterns`, `normalized_occurs_once` | Its canonical word is generated once. |
| `proper_of_normalized_cyclic`, `normalized_mem_iff_proper` | Generator membership of the canonical word also reflects source properness. |
| `positions_same_equality`, `word_eq_of_equality`, `word_lookup_eq_iff`, `word_eq_iff_equality` | The canonical list preserves and exactly characterizes source equality patterns. |
| `assignment_unique`, `canonical_factorization` | Generated canonical template, injective reconstruction, complete label use and fixed-template assignment uniqueness. |
| `selected_step_preserved`, `selected_loopless` | Selected source edges are preserved, and a loopless source gives no selected quotient loops. |

## Exact controls

Four traces with arbitrary vertex names normalize to the existing A/B/C/D
four-step patterns. All four are generated once. An odd three-step trace
normalizes to the triangle word 012, and the repeated-vertex trace
`(8,2,5,8,9,1)` normalizes to 012034 and occurs once among the six-step
patterns. This retains the paired-triangle/bowtie projection rather than
discarding it as nonsimple.

Another wedge trace over a different finite alphabet has the same canonical
word because its equality relation is the same. Repeated adjacent vertices
and a repeated root supplied as the last listed vertex are rejected by the
general membership equivalence. The latter is an endpoint-convention control:
a closed walk must have its final repeated endpoint removed before applying
this normalization.

Further controls verify reconstruction, the three-label wedge alphabet and
selected-step looplessness. In K10 the reconstructed wedge leaves have an
extra edge absent from the selected quotient steps in either direction;
the injective assignment remains valid. This certifies the non-induced
convention without changing any motif count.

## Verification and remaining composition

All 22 general declarations and ten controls have exactly the standard
`propext/Quot.sound` dependencies. The audit now checks 238 named declarations
across 22 fresh source builds: 165 general lemmas, 68 finite controls and five
coefficient certificates. Choice, placeholders and native-evaluation axioms
are forbidden. Original arithmetic receipts, coefficient/generator source,
source pin and theorem ownership remain unchanged.

This closes the forward coordinate-trace extraction-to-generator membership
and assignment interface. It does not yet prove that every arbitrary generated
bounded template is unchanged by canonical normalization, or assemble all
coordinate interfaces with stationary-step deletion and product replay into
a full product-cycle counting bijection. Those inverse/composition steps,
quotient-motif classification and the finite cardinality/free 16-to-1 quotient
remain open. The full ordinary c8 formula retains working status; external
mathematical acceptance and novelty remain separate.
