# Canonical matching–word count closure

Internal research note, 2026-10-30. Continuation of PR #11 at
`bcd79a0bd1eab5a45c655c4a3ff8ef4b8172c070`. The canonical matching/word
inventory obligation recorded at that head is now closed as a **general finite
Lean theorem**. The rooted-input/product-trace correspondence remains open.
No external mathematical acceptance or priority determination is claimed.

## The result and the remaining boundary

`JointMatchingCount.labeled_joint_count r` proves, without a counting hypothesis,

    accepted labeled words of profile (4,2^r) = r! * jointMatchingCount r.

`jointMatchingCount` is a finite, label-free matching cardinality, represented
constructively by a complete duplicate-free canonical inventory. Acceptance is
exactly connectivity of both distinguished chord resolutions. The proof does
not import the Python matching evaluator or assume its enumeration is correct.

`UnlabeledMatchingData.rootedInputs_length r` then proves

    rooted inputs = 2^(r+1) * r! * jointMatchingCount r.

These inputs are accepted words together with initial endpoint choices. Their
inventory is complete and duplicate-free. **They have not yet been identified
generally with the product graph's rooted trace inventory.**

`RepeatedEdgeAssembly.formula_from_trace_transport` reduces the last coefficient
step to a concrete map from those inputs to a `GlobalCycleCount.Inventory`:
its injectivity on inputs and exact image membership must be proved. Once
supplied, the existing global 2L quotient yields

    ordinary selected-edge cycles = 2^r r! jointMatchingCount r / (2r+4).

The new assembly theorem has those explicit trace-transport hypotheses. It is
not reported as a complete general proof of the product-sector formula.

## 1. Occurrence extraction is a genuine inverse

`OccurrenceMatching.positions w a` is the ordered list of positions bearing
label a in the literal typed finite word w. `Profile w` requires exactly four
occurrences of label zero and exactly two occurrences of every other label.
Membership, increasing order and no duplicates are proved for these lists.

`OccurrenceMatching.extract w h` constructs the endpoint matching from the
four zero occurrences and the ordered occurrence pairs of the other labels.
Every position is covered, endpoints are disjoint, and both distinguished and
ordinary endpoint orders are proved. The following inverse identities are
proved:

- Extract a word, then read its endpoint labels: recover the original word.
- Read a matching's labels, then extract occurrences: recover the original
  matching, including every endpoint position.

The reverse proof establishes uniqueness of sorted finite occurrence lists
from their members. It uses no choice-dependent sorting or permutation lemma.
Malformed word budgets, incomplete endpoint cover, shared endpoints and
reversed endpoint order are rejected by the hypotheses and finite controls.

## 2. Label-free matching data and its canonical inventory

For a valid word w, `UnlabeledMatchingData.data w` consists of:

1. The Boolean characteristic function of the distinguished four-set.
2. The Boolean relation `w(p)!=0 and w(p)=w(q)` on the complement.

The second field records the two-element blocks of the complementary matching;
its diagonal entries contain no additional information. This avoids imposing
arbitrary names or a sorting convention on those pairs.

`MatchingRelabel.Same w v` says that the zero sets and equality relations agree.
`same_data_iff` proves this is exactly equality of the label-free data. The
finite `select` transversal therefore chooses one representative per matching,
and its image under `data` has no duplicates.

Completeness is proved in both directions. Every word of the profile has its
data in this canonical inventory. Every canonical datum has a valid word and
hence an actual endpoint matching witnessing it. Conversely, every valid
endpoint matching supplies a canonical datum. `accepted_matching_data` proves
that such a datum occurs in the accepted inventory exactly when both chord
resolutions are connected.

Thus J is an actual finite cardinality of the stated matching configurations,
not a quotient introduced by dividing the desired word count. The formal
inventory uses all finite functions and a transversal; it is intentionally
independent of the production matching recursion and is not proposed as an
efficient evaluator. Refining the literal Python enumerator into Lean remains
a separate implementation-verification task.

## 3. Every global matching fiber has exactly r! words

From two words with the same unlabeled data, read the second word at the first
occurrence of each label in the first. This constructs a renaming that fixes
zero and bijects the other r labels. Its inverse/surjectivity comes from actual
occurrences, not a pigeonhole axiom.

The resulting label list is proved to be a permutation of `List.range r`.
Constructive local erase/membership/permutation lemmas avoid standard-library
lemmas whose transitive axiom sets include classical choice.

The converse is also proved: every permutation labeling of a fixed matching
preserves precisely its distinguished four-set and complementary pairs.
Consequently, for valid words w and v,

    Same w v iff v is in the fixed matching's complete labeling fiber.

`MatchingFiber.fiber` gives a typed list of those words. Its exact membership
is `Profile v and Same w v`, it has no duplicates, and its length is r!.
The two inverse occurrence constructions make this a statement about actual
position-indexed words, rather than abstract assignments alone.

## 4. Acceptance is invariant on each fiber

The label renaming preserves the ordered distinguished occurrence list and
transports every ordinary occurrence pair. These statements give equality of
the distinguished prefix phases and equality of all remaining parity states
after the explicit coordinate renaming.

`same_folded_iff` proves folded departure injectivity is invariant under `Same`.
`connectedCheck` is the complete finite-cut predicate from the independently
proved connected-chord characterization. `jointCheck_iff` connects its two
resolution checks to folded injectivity. Therefore `accepted_stable` proves
actual two-resolution acceptance is constant across every matching fiber.

This stability is a real hypothesis of the generic filtered quotient theorem;
it is proved for the actual predicate. A finite control shows that the
label-sensitive predicate "the first nonzero label is 1" accepts only one
member of a two-element matching fiber, so the cardinality formula cannot be
applied to arbitrary predicates.

## 5. Global cardinality and rooted inputs

`MatchingCount.inventory` enumerates all functions Fin L -> Fin(r+1), filtered
by the occurrence profile. Its membership is proved equivalent to that profile.
The finite transversal has subset, coverage, separation and uniqueness proofs.

The accepted word inventory is proved equal, by membership and duplicate-free
cardinality, to the disjoint union of the accepted representatives' fibers.
Each fiber has cardinality r!, so the general labeled count follows. No global
cardinality identity is supplied as an assumption.

`acceptedData` is the image of accepted representatives under the label-free
matching data. Its uniqueness, membership and equality with the matching count
are proved separately. This rules out confusing representative labels with
unlabeled configurations.

Finally, independently enumerate every initial endpoint assignment
Fin(r+1) -> Fin 2. Its cardinality is 2^(r+1). The Cartesian list of accepted
words and these assignments is complete and has no duplicates, giving the
proved rooted-input count. The trace map itself is the next proof obligation.

## 6. Independent exact finite checks

`experiments/canonical_matching.py` imports only the preceding independent
checker. It uses explicit occurrence lists, label-free Boolean relations,
multiset words, restricted-growth endpoint matchings and product-adjacency
paths. No production matching counter, coefficient formula or production DFS
is imported.

| r | Profile words | Unlabeled data | J | Accepted words | Rooted inputs / distinct traces | Ordinary cycles |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 1 | 1 | 0 | 0 | 0 | 0 |
| 1 | 15 | 15 | 0 | 0 | 0 | 0 |
| 2 | 420 | 210 | 2 | 4 | 32 | 2 |
| 3 | 18900 | 3150 | 110 | 660 | 10560 | 528 |

For every word, including rejected words, the checker verifies both occurrence
inverses. The canonical data agree bijectively with an independently generated
ordered-four-set/complementary-matching inventory. Every fiber is compared
with all label permutations, not merely with its expected cardinality.

For every accepted word and every initial endpoint assignment through r=3,
the checker constructs the literal product trace, recovers the word from its
changed coordinate at each step and recovers the initial assignment from its
root. All generated traces are distinct. Their complete canonical cycle-image
sets equal independent product-adjacency enumeration in each row, and every
orbit has exactly 2L rooted representations. These are bounded observations,
separate from the general word/data count proof.

Negative controls remove an accepted word, omit r!, apply a label-sensitive
predicate, use only one resolution, or violate profile/endpoint/Cartesian-step
guards. Five new unit tests retain those boundaries. The previous seven receipt
files and the source pin remain unchanged; the eighth receipt is
`conformance/canonical-matching.json`.

### Kernel-control resource boundary

The small Lean controls certify the complete profile inventories 1 and 15 for
r=0,1 and their zero accepted matching counts, plus a two-element label fiber,
a label-sensitive filter counterexample and malformed inputs. They use kernel
reduction, not native evaluation.

An exploratory ground Lean enumeration including r=2 (3^8 candidate functions)
was killed with exit 137 before producing a certificate. That resource failure
is not a counterexample and is not counted as a passed check. The large ground
reduction is excluded from required CI; the general r!J theorem and the
independent exact r=2,3 replay remain distinct successful evidence.

## Next reproducible general proof

Construct the rooted product trace from an accepted typed word and its initial
endpoint assignment. Prove that successive vertices change exactly the axis
named by the word, including the final edge back to the root. Recover both
inputs from every rooted product trace of the selected-edge profile. Supply
that inverse pair to `formula_from_trace_transport`, then specialize the
selected-copy, coordinate-allocation and inactive-fiber transport to arbitrary
factors. This discharges the remaining trace-inventory hypotheses; further
computational agreement alone will not do so.

Connected pairings, finite permutation counting and the 2L orbit principle
retain their established prior-work status. The two-resolution application
and universal motif assembly remain candidate contributions with priority and
independent mathematical acceptance open.
