# First c8 inventory

Historical bootstrap record. The subsequent working derivation is
[proof/c8-lower-support.md](../proof/c8-lower-support.md); its separate receipt
is `conformance/lower-support.json`. The original receipt and its historical
open-formula status are preserved byte-for-byte.

The new vertex DFS uses pinned generic graph constructors but imports no cycle
count formula. It visits each ordinary cycle once by requiring its smallest
vertex as root and choosing one of the two traversal directions. Selected edges,
not inducedness, determine a copy. Coordinates with zero steps remain in the
reported profile, including fixed-coordinate multiplicity.

| Product | Ordinary c8 copies |
| --- | ---: |
| C4 square K2 | 6 |
| K3 square K3 | 81 |
| P3 square K3 | 15 |
| K2 square K3 square K3 | 2,700 |
| Q4 | 696 |

Q4 splits into 648 full-support copies and 48 lower-support copies. In
K2 square K3 square K3, profile (2,3,3) has 1,404 copies; the two length-three
closed projections traverse triangles. Profile (4,2,2) has 18 copies even though
K2 has no simple four-cycle: projected walks can revisit vertices. This is a
negative control against treating every projection as a simple cycle.

The complete profiles and one actual witness per profile are in
`conformance/first.json`. Counts diagnose missing terms; no full lower-support
formula or classification of collision corrections is asserted.
