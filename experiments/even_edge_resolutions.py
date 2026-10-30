"""Finite parity-resolution receipt with independent closed-cycle checks."""
from collections import Counter
from itertools import product
from pathlib import Path
import json
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from kernels.even_edge_resolutions import (unlabeled_count, even_edge_coefficient,
    cube_profile_totals, pairing, crossing_connected)
from experiments.near_top import profile_count, motif
from kernels.eight_cycles import collision_free


def receipt():
    profiles = ((4, 2, 2), (4, 2, 2, 2), (6, 2, 2, 2), (4, 4, 2, 2))
    edge = motif([(0, 1)], 2)
    rows = []
    for p in profiles:
        c = even_edge_coefficient(p)
        observed = profile_count([edge]*len(p), p)
        assert c == observed
        rows.append({'profile': p, 'unlabeled_accepted_partitions': unlabeled_count(p),
                     'coefficient': c, 'independent_adjacency_dfs': observed})
    corpus = json.loads((Path(__file__).resolve().parents[1]/'conformance/first.json').read_text())
    q4 = next(c for c in corpus['cases'] if c['case'] == 'Q4')
    baseline = Counter()
    for s in q4['strata']:
        baseline[tuple(sorted(d for d in s['coordinate_steps'] if d))] += s['count']
    assert cube_profile_totals(4, 8) == baseline
    cubes = []
    for d, length, expected in ((3, 8, 6), (4, 8, 696), (4, 10, 2112), (4, 12, 5024)):
        totals = cube_profile_totals(d, length)
        assert sum(totals.values()) == expected
        cubes.append({'dimension': d, 'length': length,
                      'total': expected, 'strata': [{'steps': p, 'total': n}
                                                  for p, n in sorted(totals.items())]})
    blocks = ((1, 6), (0, 2, 4, 8), (3, 5, 7, 9))
    outcomes = []
    for bits in product(range(2), repeat=2):
        chords = tuple(c for b, flag in zip(blocks, (0,)+bits) for c in pairing(b, flag))
        outcomes.append(crossing_connected(chords))
    assert outcomes == [True, True, False, True]
    word = tuple(next(a for a, block in enumerate(blocks) if i in block) for i in range(10))
    literal = collision_free(word, ((0, 1),)*3)
    assert not literal
    return {
        'scope': 'working all-even-profile selected-edge sector, not all motifs in arbitrary factors',
        'independent_profile_checks': rows,
        'cube_specializations': cubes,
        'negative_controls': {
            'diagonal_resolutions_only': {'blocks': blocks, 'word': word,
                                         'choices_00_01_10_11': outcomes,
                                         'literal_folded_simple': literal},
            'Q4_c12_top_support_only': 0,
            'Q4_c12_top_and_next_support_only': 0,
            'Q4_c12_actual': 5024,
            'K3_square_K3_c8_selected_edge_sector': 0,
            'K3_square_K3_c8_original_ordinary_total': 81,
        },
    }


if __name__ == '__main__':
    print(json.dumps(receipt(), indent=2))
