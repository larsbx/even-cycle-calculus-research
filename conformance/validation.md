# Bootstrap validation

Executed 2026-10-26 with the environment in `environment.json`.
`python3 tools/validate.py` passed: all source digests and preserved source
claim statuses checked, and the finite receipt reproduced byte-for-byte.
This records local validation; hosted CI status is reported separately on the PR.
No Lean build or independent mathematical acceptance was performed.

## Subsequent c8 acceptance

PR #2's original final-head hosted run has now been inspected and confirms
success for both `finite-replay` and `finite-lean` at
`c27c296665913bc8d3f71cbe9a353c8c2f70809e`:
[run 40555414697](https://github.com/larsbx/even-cycle-calculus-research/actions/runs/40555414697).
Merged main `fc4c7e3f646d59e92b224041d7939261c2bd0979` also passed
[run 40555781489](https://github.com/larsbx/even-cycle-calculus-research/actions/runs/40555781489).
These supersede the runner-queued observation recorded at merge time; earlier
candidate runs failed before the correction already present at that final head.

## Coordinate decoding continuation

`python3 tools/validate.py` continues to pass the unchanged pinned-source and
byte-for-byte finite receipts, including seven regression tests.
`python3 formal/check.py` now checks the pinned compiler version and all 19
declaration axiom sets: five coefficient tables, eight general finite
coordinate-decoding lemmas and six formal control declarations. Imports are
rebuilt in a temporary directory. Local checking used the executable-path
compatibility shim described in PR #2; hosted CI uses the unmodified official
digest-pinned compiler. New PR-head hosted evidence is recorded on that PR.
Full extraction/counting formalization and external mathematical acceptance
remain open.

## Canonical coordinate extraction continuation

The extension of PR #3 adds 15 general bounded first-occurrence theorems and
three finite representation controls. `formal/check.py` now checks 37 exact
declaration axiom sets across five source files, rebuilding both local imports
in a temporary directory. Existing coefficient and collision-bridge audits
are retained. Source pin and both arithmetic receipts are unchanged. Final-head
hosted acceptance is still required by PR #3; earlier-head results do not
validate this extension.

## Ordinal rank-compression continuation

The next extension of PR #3 adds 20 general ordinal rank-compression lemmas
and three finite controls. The exact audit now checks 60 declarations across
seven sources with fresh local imports. The rank bound explicitly selects a
constructive equality-equivalence instance; no choice dependency is permitted.
Arithmetic receipts, source pin and existing declarations are unchanged.
Final-head hosted acceptance remains required; earlier-head runs do not
validate the extension.

## Coordinate-event projection and replay continuation

The next extension adds 17 general finite event/path lemmas and five controls,
including exact replay of the recorded prism eight-cycle witness. The audit
checks 82 declarations across nine sources with fresh imports. It rejects
choice, placeholders and native-evaluation axioms. Both original arithmetic
receipts and the source pin remain unchanged. Final-head hosted acceptance is
still required by PR #3; no earlier run substitutes for it.

## Closed-coordinate-walk continuation

The next extension adds 19 general lemmas and nine controls, proving exact
factor-walk and closure conditions, a closed-walk realization equivalence,
endpoint normalization and departure-list injectivity. Controls cover the
prism, a colliding interleaving of the same queues, a missing factor edge and
paired odd triangle projections. `formal/check.py` passes 110 exact declaration
audits across 11 sources with fresh imports; no choice, placeholders or
native-evaluation axioms are allowed. `tools/validate.py` passes both unchanged
receipts, preserved source pin/status checks and seven regressions. Local
execution uses the same documented executable-path compatibility shim.
Final-head hosted acceptance remains required by PR #3. The full ordinary-cycle
counting theorem and external mathematical acceptance remain open.

## Modular cycle-trace continuation

The next extension adds ten general lemmas and seven controls. They connect
the event replay's departure list to modular CycleEmbedding adjacency in both
directions, and give a self-contained cycle criterion with explicit coordinate
closure, factor-edge validity, minimum length and departure injectivity.
Controls certify the prism and paired-triangle witnesses, reject colliding
and missing-edge witnesses, and demonstrate that closure and length at least
three are essential. `formal/check.py` passes 127 exact declaration audits
across 13 freshly compiled sources; the permitted axioms remain exactly the
listed standard dependencies. `tools/validate.py` passes the unchanged source
pin/status checks, both receipts and seven regressions. Final-head hosted
acceptance is still required by PR #3 before merge. Executable pattern
correspondence, enumeration completeness and the cardinality quotient remain
separate from this structural criterion.

## Literal executable trace continuation

The next extension adds 16 general lemmas and eight controls. For finite
bounded positive-period templates, the literal Shuffle.vertices output equals
encoded typed departures and its distinct test is equivalent to trace
injectivity. Final counters equal initial counters plus coordinate step
counts; period-divisible counts give closure. The prism, colliding and paired
triangle inputs match exactly; malformed default inputs isolate the bounds.
The exact audit passes 151 named declarations across 15 freshly compiled
sources, with no choice, placeholders or native-evaluation axioms. A direct
structural list-modification proof avoids a choice-dependent Std lookup lemma.
Both arithmetic receipts, Shuffle.lean, the source pin and source statuses
are unchanged; all seven regressions pass. Local Lean uses the same documented
executable-path compatibility shim. Final-head hosted acceptance remains
required by PR #3. Canonical extraction/template assembly, whole generator
completeness, motif classification and the cardinality quotient remain open.

## Axis-word generator continuation

The next extension adds 17 general lemmas and seven controls for the unchanged
literal axis-word generator. Exact membership is characterized by word length,
bounded axes and coordinate occurrence counts. Every emitted word occurs once;
collision filtering preserves uniqueness. A constructive typed-axis lift has
the requested step counts. Controls check all six profile inventories, witness
uniqueness and invalid inventory/axis/budget cases. The exact audit passes 175
named declarations across 17 fresh source builds with the existing strict
axiom policy. Both arithmetic receipts, Shuffle.lean and the source pin/statuses
are unchanged; all seven regressions pass. Local Lean uses the same documented
executable-path shim. Hosted final-head acceptance remains required by PR #3.
Whole cyclic equality-pattern completeness, canonical extraction/template
assembly, quotient-motif classification and the cardinality quotient remain open.

## PR #3 hosted acceptance and merge

Both `finite-replay` and `finite-lean` completed successfully at exact final
head `4d3d85b0a51828bcb80ebca91b8b749dc6bad914` in
[run 40803497078](https://github.com/larsbx/even-cycle-calculus-research/actions/runs/40803497078).
No submitted review findings, review threads or change requests were recorded.
The older bot notice reporting a running review at 469de73 is not treated as
final-head review approval. PR #3 merged as
`acb8fe4e9806d18dc357ac98554e47ad31b5b905` after its recorded CI gate passed.
This is engineering acceptance of the specified components, not external
mathematical acceptance of the full c8 theorem.

## Cyclic-pattern generator continuation

The next focused increment adds 16 general lemmas and seven controls for the
unchanged literal restricted-growth generator. Output membership is exactly
the positionwise append-bound, neighbor and closing conditions. Both extension
and canonical pattern lists have no duplicate words. Controls reproduce A-D
and the 11/41 length-five/six inventories, verify selected words occur once,
and reject four distinct malformed conditions. The exact audit checks 198
named declarations across 19 freshly compiled sources; no choice, placeholders
or native-evaluation axioms are allowed. The original receipts, Shuffle.lean,
source pin/statuses and seven regressions remain unchanged. The local compiler
archive matches the CI SHA-256; execution uses the same documented PID-path
shim. This increment requires its own final-head hosted acceptance. Canonical
extraction/template assembly, motif classification and the counting quotient
remain open.

## PR #4 hosted acceptance and merge

Both `finite-replay` and `finite-lean` completed successfully at exact final
head `b64307c26806e16b34cf2a0b15e1d6f06c944534` in
[run 40858189895](https://github.com/larsbx/even-cycle-calculus-research/actions/runs/40858189895).
No submitted review findings, unresolved threads or change requests were recorded.
PR #4 merged as `777ddc5ef704664d1e60650c7f1289261c486139` after its recorded
final-head CI gate passed. This records engineering acceptance of the specified
generator component, not external mathematical acceptance of the c8 theorem.

## Canonical coordinate membership continuation

The next increment adds 22 general lemmas and ten controls. A nonempty finite
coordinate trace's canonical ordinal word is generated iff the source has
unequal neighbors and unequal endpoints. The assignment reconstructs every
source vertex, is injective, visits all labels and is unique for that fixed
template. Equality patterns characterize canonical words exactly. Source
selected steps are preserved without inducedness. Controls cover A-D, an odd
triangle, a repeated-vertex six-step projection, faithful equality-pattern
relabeling, adjacent/endpoint collapses, reconstruction and an extra graph edge.
The exact audit passes 230 named declarations across 21 fresh source builds
under the existing strict axiom policy. Both arithmetic receipts, Shuffle.lean,
the source pin/statuses and all seven regressions are unchanged. Local Lean
uses the documented PID-path shim. This increment requires its own final-head
hosted acceptance. Arbitrary-template normalization inverses, full product-cycle
composition, motif classification and the cardinality quotient remain open.
