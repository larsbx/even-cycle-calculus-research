# Exact multiplicities and uniqueness of generated axis words

`formal/WordGenerator.lean` adds 17 general finite lemmas about the unchanged
`ECC.words` generator in Shuffle.lean. They prove its exact membership
criterion, uniqueness of its emitted words, preservation of uniqueness by
filtering, and a constructive lift to bounded typed coordinate axes.
Seven finite controls are in `formal/WordControls.lean`.

## Soundness and completeness

For a finite counter list c, define `Matches(c,w)` by both conditions:

1. Every axis a occurring in w satisfies a < length(c).
2. For every a < length(c), the number of occurrences of a in w is exactly c[a].

The theorem `mem_words_iff` proves, for every finite length m,

\[
 w\in\operatorname{ECC.words}(m,c)
 \quad\Longleftrightarrow\quad
 |w|=m\ \land\ \operatorname{Matches}(c,w).
\]

The bounded-axis condition is essential: checking only counts for the valid
axes would otherwise say nothing about an invalid axis appearing in a word.
The criterion includes zero counts and the empty coordinate list; there is
no positive-count hypothesis on the inventory.

The proof follows the literal remaining-inventory recursion. The base case
accepts the empty word exactly when every counter is zero. In a nonempty
word a::tail, its head must be in range and have positive inventory. Removing
that head decrements exactly counter a and gives the same Matches condition
for the tail. Conversely that positive-head/tail data reconstruct Matches.
The decrement guard prevents truncated subtraction from accepting excess
occurrences. No separate enumeration implementation replaces `ECC.words`.

## Each word is emitted exactly once

`words_nodup` proves that the output list of words has no duplicates. This
does not prohibit repeated letters within a word; those letters are the
coordinate multiplicities being counted.

Within one head branch, prefixing a fixed axis preserves uniqueness of the
recursive tail list. Different head branches cannot share a word because
their first axes differ. The range of head axes is itself duplicate-free.
A bounded structural proof of this range fact avoids the choice dependency
of the pinned Std `nodup_range` theorem.

Filtering by any Boolean predicate preserves this uniqueness. In particular,
the actual collision-filtered list whose length is `ECC.kernel` contains each
admissible axis word once. Its length therefore counts accepted words, rather
than recursion paths with possible repetitions. This does not yet count
ordinary cycles or perform the division by 16.

| Declaration in ECC.WordGenerator | Conclusion |
| --- | --- |
| `matches_nil_iff`, `matches_cons_iff` | Exact inventory semantics of the base and head-removal cases. |
| `mem_words_zero`, `mem_words_succ` | Literal generator membership in each recursive case. |
| `mem_words_iff` | Full soundness and completeness for finite axis words of the prescribed multiplicities. |
| `range_nodup_safe`, `prefix_nodup` | Bounded head enumeration and fixed-head prefixing preserve uniqueness. |
| `branch_head`, `branches_disjoint` | Every branch emits its own head; distinct heads give disjoint branches. |
| `words_nodup`, `accepted_nodup` | Generated and Boolean-filtered word lists have no duplicates. |
| `mem_accepted_iff` | Filtered membership is exactly length, Matches and predicate acceptance. |
| `map_lift`, `steps_eq_raw_count` | Bounded raw words lift without changing their values; typed step counts agree with raw occurrence counts. |
| `generated_typed_axes` | Every emitted raw word admits a constructive Fin(length(c)) axis list with exactly inventory c. |
| `kernel_membership_iff`, `kernel_words_nodup` | The actual eight-step collision-filtered kernel list has the stated exact membership and uniqueness properties. |

The lift processes the word directly using its proved bounds. It uses no
classical selection. It supplies the finite axes required by the prior
[executable trace bridge](executable-coordinate-trace.md), so generated axes
cannot silently use the raw executable's out-of-range defaults. The
[cyclic-pattern extension](cyclic-pattern-generator.md) now separately proves
whole pattern membership and unique enumeration.

## Finite controls

Kernel-checked finite reductions give these numbers of axis words before
any collision filtering:

| Profile | Axis words |
| --- | ---: |
| (6,2) | 28 |
| (3,5) | 56 |
| (4,4) | 70 |
| (4,2,2) | 420 |
| (2,3,3) | 560 |
| (2,2,2,2) | 2,520 |

The prior prism and paired-triangle witness words each occur exactly once,
using the general uniqueness theorem and finite membership checks. The prism
word's constructive typed lift retains its values and has step counts (4,4).
Controls also reject an eight-letter word with wrong multiplicities, an
eight-letter word containing invalid axis 2 for a two-coordinate inventory,
and the seven-step budget with inventory (4,4). An exhausted inventory accepts
one empty word at length zero, but no positive-length word. A nonzero inventory
does not accept the empty word.

These counts are shuffle inventories, not ordinary cycle totals. The corpus's
6 prism cycles, 81 K3 square K3 cycles and 1,404 cycles of profile (2,3,3)
still require the factor assignments, collision test and quotient conventions
in the working c8 derivation. Neither arithmetic receipt changes.

## Verification boundary

Of the 17 general declarations, `map_lift` uses no axioms and the other 16
use standard `propext/Quot.sound`. Three controls use only `propext`; four
use `propext/Quot.sound`. The complete audit checks 230 exact named declarations
across 21 fresh source builds: 160 general lemmas, 65 finite controls and five
coefficient certificates. No choice, placeholders or native-evaluation axioms
are permitted. The literal generator and coefficient source is unchanged.

The [canonical membership bridge](canonical-pattern-membership.md) now checks
the forward coordinate-trace membership and assignment interface. Remaining
work includes arbitrary-template normalization inverses, full product-cycle
composition, quotient-motif classification and the finite cardinality/free
16-to-1 quotient.
The full c8 formula remains working. Shared source pin and theorem ownership
are unchanged; external mathematical acceptance and novelty remain separate.
