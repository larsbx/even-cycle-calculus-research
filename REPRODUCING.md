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
```

For an existing checkout, set `GPR_SOURCE=/absolute/path/to/pinned/source`.
Replay rejects another source HEAD or changed pinned input bytes.
`tools/validate.py` parses the registry, checks preserved source statuses,
and recomputes the receipt byte-for-byte. The printed JSON is deterministic;
tool versions and execution date are recorded separately in `conformance/environment.json`.
Use a clean checkout for independent reproduction. Passing this finite replay
does not close an all-graph proof or external literature/acceptance obligation.
