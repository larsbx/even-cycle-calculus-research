# Independent replay

Use Python 3.11+ and Git; the chord experiment also requires g++ with C++17.
No pip packages, floating-point arithmetic, random seeds, or remote services
are required by an experiment after the source checkout is prepared.

From this repository root:

```sh
mkdir -p .deps
git clone https://github.com/larsbx/graph-product-ring-research.git .deps/graph-product-ring-research
git -C .deps/graph-product-ring-research checkout --detach 28d022402037274a9fe85c1fd64ecda2532dceb9
python3 experiments/first.py > /tmp/first.json
diff -u conformance/first.json /tmp/first.json
python3 tools/validate.py
python3 formal/check.py
```

For an existing checkout, set `GPR_SOURCE=/absolute/path/to/pinned/source`.
Replay rejects another source HEAD or changed pinned input bytes.
`tools/validate.py` parses the registry, checks preserved source statuses,
and recomputes all seven receipts byte-for-byte. These include the symbolic
coefficients, 144 small graph pairs and independent finite partition-lattice
inversion check. It then runs the exact regression suite. The finite
Lean step needs the version in `formal/lean-toolchain`; it uses Std only and
compiles all 49 Lean sources and enforces 429 exact named axiom sets. Set
`LEAN_BINARY` if the compiler is not on PATH. See `formal/README.md`.
The printed JSON is deterministic;
tool versions and execution date are recorded separately in `conformance/environment.json`.
The new sector receipt can also be replayed with
`python3 experiments/near_top.py > /tmp/near-top.json` followed by
`diff -u conformance/near-top.json /tmp/near-top.json`. It uses only the Python
standard library. The all-length recurrence and scoped c10 formulas have a
working prose proof, separately from the eight new formal collision declarations.
Use a clean checkout for independent reproduction. Passing this finite replay
does not close an all-graph proof or external literature/acceptance obligation.

The histogram-assisted inversion receipt uses `g++ -std=c++17` and Python only:

```sh
python3 experiments/partition_histogram.py > /tmp/partition-inversion.json
diff -u conformance/partition-histogram.json /tmp/partition-inversion.json
```

It checks unrestricted adjacency walks through explicit finite vertex-partition
Mobius inversion, without importing a shuffle or connected-axis recurrence.
The entire original/additional c8 corpus, 144 small graph pairs, and eight
near-top profiles are compared. See `proof/partition-lattice-check.md` for
quotient-hom oracle coverage, cancellation ledgers and formal boundaries.

The independently merged direct quotient oracle from PR #7 is preserved
byte-for-byte in `kernels/partition_inversion.py`; its original receipt is
`conformance/partition-inversion.json`. Replay it separately with:

```sh
python3 experiments/partition_inversion.py > /tmp/direct-inversion.json
diff -u conformance/partition-inversion.json /tmp/direct-inversion.json
```

This standard-library-only route counts weighted quotient maps by frontier
dynamic programming. The histogram route additionally checks c10 and the raw
projection coefficients. Both receipts are mandatory, and all 35 regressions
run together. See `proof/partition-inversion.md` for the direct oracle's scope.

The two-resolution receipt is independently replayable:

```sh
python3 experiments/repeated_edge.py > /tmp/repeated-edge.json
diff -u conformance/repeated-edge.json /tmp/repeated-edge.json
```

It distinguishes exact matching evaluations r=0..5 from independent adjacency
DFS r=0..4, plus three mixed twelve-cycle products isolating all four
coefficients at that length. Five regression tests also check every labeled word through r=3,
connectivity against endpoint intervals, original c8/c10 corpus agreement,
coordinate permutations, inactive fibers and single-resolution failures.
See `proof/repeated-edge-resolutions.md` for the all-length identity and
precise formal limits. The seven new Lean audits cover the collision component.

The simultaneous even-edge resolution receipt is replayed with:

```sh
python3 experiments/even_edge_resolutions.py > /tmp/even-edge-resolutions.json
diff -u conformance/even-edge-resolutions.json /tmp/even-edge-resolutions.json
```

It checks four selected-edge profiles by independent product-adjacency DFS,
recovers cube specializations through Q4 c12, preserves the original Q4 c8
receipt and exhibits failure of the two constant resolution choices. Four
new regressions compare every word in ten finite profile families with both
a literal endpoint-parity trace and the old collision kernel; check block
inventory, existing coefficients, scope and finite boundaries. All six prior
receipts remain mandatory and unchanged. The 34 new formal declarations are
components of the stated proof, not formal certification of the Python
block-partition enumerator or a claim of mathematical novelty.
