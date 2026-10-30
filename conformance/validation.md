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

## PR #5 hosted acceptance and merge

Both `finite-replay` and `finite-lean` completed successfully at final head
`11f900b93043a33191475a4ed94c0421c974cdae` in
[run 40871170599](https://github.com/larsbx/even-cycle-calculus-research/actions/runs/40871170599).
Jobs 123438298996 and 123438299315 succeeded. Fresh review inspection found
no submitted reviews or threads. PR #5 merged as
`eec9c407721e7515cf747c16f8d0225edd47eaf2`. This is formal/executable component
acceptance, not external mathematical acceptance or novelty evidence.

## Mixed-projection and c10 support-four continuation

The new independent receipt is `near-top.json`. It records the four four-step
coefficient sums 660, 2562, 4008, 8310, the paired-triangle coefficient 12540,
eight product-adjacency DFS strata and seven bounded evaluations of the
paired-triangle recurrence. Only the first three recurrence rows have an
independent product DFS comparison. New negative controls distinguish closed
walks from simple cycles, nonsimple projections from square projections, and
support four from support five. No original receipt is changed.

Local exact replay passes all three receipts and thirteen tests. The complete
fresh Lean audit passes 238 declarations across 22 sources: 165 general lemmas,
68 finite controls and five coefficient certificates. The five new general
interval-collision lemmas use exactly `propext/Quot.sound`; their three controls
use no axioms. Local compilation uses the previously documented executable-path
shim with the same pinned official archive. The connected-partition recurrence,
c10 numeric coefficient sums and ordinary-cycle cardinality quotient remain
prose/computational results, separate from the new kernel-checked component.
This increment requires its own final-head hosted acceptance before merging.
Mathematical priority and independent review remain open.

## Completed final-head evidence for merged PR #6

PR #6 merged as `76d00684013a8038d73e646ef043faa9c699ae3e` after the earlier
user instruction to merge while checks were queued. A fresh inspection on
2026-10-30 found that its final resolved head
`89e85cb57108bff9055453c87bcc4bd7575a41c0` subsequently passed both jobs in
[PR run 40947582908](https://github.com/larsbx/even-cycle-calculus-research/actions/runs/40947582908):
`finite-replay` 123706895883 and `finite-lean` 123706896226. These are completed
results at the final integrated tree, not earlier-head evidence. They do not
retroactively change the recorded merge timing or establish external
mathematical acceptance or priority.

## Fixed-cycle representations and c10 kernel certificates

The continuation adds the explicit fixed-trace root/direction parameterization,
injectivity and cyclic-edge preservation, with length-two, repeated-vertex and
directed-edge negative controls. Prefix decomposition connects the unchanged
literal ten-step collision count to eighty individual two-step-prefix cells,
twenty row identities and five complete raw coefficient identities. Exact
multiplier arithmetic and root-dependent wedge divisibility are checked
separately. See `proof/rooted-cycle-counting.md` for the formal boundaries.

The audit procedure now checks 388 exact named declarations across 46 fresh
source builds, including the isolated coefficient modules. No native evaluation
or added axiom is permitted. The local official compiler archive has the same
verified digest as CI; the previously documented executable-path shim is used
only for local process-path compatibility. The Lean workflow receives a
45-minute budget for the added kernel reductions. The five existing exact
receipts replay unchanged. The added all-length wedge identity test brings
the suite to 26 regressions; it checks recurrence values through r=6, direct
B/C word sums through r=3, and independent adjacency DFS isolation for r=1..3.

The global graph-inventory orbit partition, coordinate-profile cardinality
transport, full motif assembly and partition-weight cancellation theorem remain
open. Both final-head hosted jobs are required for this increment's merge;
external mathematical review and expansion novelty are separate obligations.

The same increment derives the working all-length identity T_(r+2)=4W_r+S_r
by grouping two edge axes into C4. Its four selected wedge classes and one
square class partition the source top-support cycles. This prose proof and
its finite regression are distinct from the kernel coefficient certificates;
the all-r coarsening theorem is not claimed formally verified.

## Matching-count transport continuation

The new scope is recorded in `proof/matching-count-transport.md`. The checker
now expects 469 exact named declaration audits across 56 source builds. The
74 added declarations cover connected chords, constructed simultaneous
resolutions, fixed-matching factorial label fibers, complete finite-graph
ordinary-cycle orbits, selected-copy transport and dependent coordinate fibers.
Every new axiom set is a subset of propext/Quot.sound. The final repeated-edge
arithmetic theorem retains the explicit assembled-rooted-count hypothesis.

An independent extension/support build passed all 111 relevant exact audits.
The new independent receipt exhausts diagrams through six chords and labeled
folded words through r=3, and checks rooted adjacency orbits, all allocations
in five small next-to-top hosts, inactive fibers and paired triangles. Eight
new regression controls enforce the hypotheses. Full fresh-replay/audit and
hosted final-head results must be recorded separately; these component results
do not establish a complete all-factor machine proof or external mathematical
acceptance. The six earlier receipt files and source pin are unchanged.

Local full finite replay passed all seven byte-exact receipts and all 39
regressions. A subsequent strengthening of the independent checker verifies
individual selected-copy classes (3,7,17,33,21 across its five product hosts)
and confirms that K4 has three distinct ordinary four-cycles on the same vertex
set. Its updated receipt and eight controls are replayed separately. The Lean
sources and exact audit manifest are unchanged by this strengthening.
