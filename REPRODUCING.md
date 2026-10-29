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
and recomputes all three receipts byte-for-byte, including all symbolic coefficients,
144 small graph pairs and the independent quotient inversion, then runs the
13-test regression suite. The finite
Lean step needs the version in `formal/lean-toolchain`; it uses Std only and
compiles all 21 Lean sources and enforces 230 exact named axiom sets. Set
`LEAN_BINARY` if the compiler is not on PATH. See `formal/README.md`.
The printed JSON is deterministic;
tool versions and execution date are recorded separately in `conformance/environment.json`.
Use a clean checkout for independent reproduction. Passing this finite replay
does not close an all-graph proof or external literature/acceptance obligation.

To replay only the new independent comparison:

```sh
python3 experiments/partition_inversion.py > /tmp/partition-inversion.json
diff -u conformance/partition-inversion.json /tmp/partition-inversion.json
```

`kernels/partition_inversion.py` has no repository imports. The experiment
imports motif fixtures/formulas and the old DFS only on the comparison side;
the oracle constructs its own colored Cartesian adjacency and counts arbitrary
maps of weighted quotients. The same CI finite-replay job enforces this third
receipt. New regressions cover every simple host of order at most four,
complete-host selected-cycle counts, direct all-map checks of the frontier
algorithm, Möbius cancellation, loops and parallel-edge exponents.
