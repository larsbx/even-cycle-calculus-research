"""Compile all Lean components and enforce each declaration's exact axiom set."""
from pathlib import Path
import os
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
LEAN = os.environ.get('LEAN_BINARY', 'lean')
EXPECTED = {
    **{'ECC.'+n: {'propext'} for n in (
        'paired_triangle_coefficient', 'four_step_coefficients',
        'two_four_step_coefficients', 'six_two_coefficients', 'three_five_coefficients')},
    **{'ECC.CollisionBridge.'+n: {'Quot.sound'} for n in (
        'decode_equal_iff', 'trace_injective_iff', 'decoded_cycle_iff', 'assignments_recovered')},
    **{'ECC.CollisionBridge.'+n: set() for n in (
        'coordinate_step_iff', 'coordinate_axis_unique', 'cartesian_adj_preserved', 'used_coordinate_iff')},
    'ECC.CollisionControls.fold_edges_preserved': set(),
    **{'ECC.CollisionControls.'+n: {'propext', 'Quot.sound'} for n in (
        'square_is_cycle', 'folded_trace_not_injective', 'unseen_assignments_injective',
        'unseen_assignments_same_trace', 'unseen_assignments_differ')},
    **{'ECC.CanonicalTrace.'+n: {'propext', 'Quot.sound'} for n in (
        'scan_spec', 'first_le', 'first_value', 'first_minimal',
        'first_eq_of_value_eq', 'first_eq_iff', 'first_idempotent',
        'realize_extract', 'extract_representative', 'realize_injective',
        'first_injective_relabeling', 'first_equality_relation',
        'normalized_shape_recovered', 'canonical_shape_unique', 'extract_surjective')},
    **{'ECC.CanonicalControls.'+n: {'propext', 'Quot.sound'} for n in (
        'first_positions', 'positions_are_not_ordinals', 'noninjective_relabel_changes_first')},
    **{'ECC.RankCompression.'+n: {'propext', 'Quot.sound'} for n in (
        'positions_mem_iff', 'positions_nodup', 'positions_sorted', 'unrank_rank', 'rank_unrank',
        'rank_injective', 'unrank_injective', 'rank_lt_implies', 'rank_lt_iff', 'decode_encode',
        'encode_representative', 'encode_surjective', 'decode_injective', 'encode_eq_iff',
        'initial_segment_seen', 'encode_zero', 'predecessor_seen', 'fold_max_bounds',
        'append_bound', 'enumerator_label_allowed')},
    **{'ECC.RankControls.'+n: {'propext', 'Quot.sound'} for n in (
        'representative_positions', 'compressed_ordinals', 'last_ordinal_recovers_position')},
    **{'ECC.EventShuffle.'+n: {'propext'} for n in (
        'project_head', 'project_other', 'project_length', 'projection_compatible',
        'weave_sound', 'compatible_tail', 'transition_axis_word')},
    **{'ECC.EventShuffle.'+n: {'propext', 'Quot.sound'} for n in (
        'queue_after_project_head', 'weave_project', 'weave_complete',
        'compatible_reconstruction', 'reconstruction_unique', 'reconstruction_iff_compatible',
        'update_of_stationary', 'update_of_coordinate_step', 'replay_transitions',
        'weave_replay_transitions')},
    **{'ECC.EventControls.'+n: {'propext'} for n in (
        'prism_projections', 'prism_vertex_path', 'short_queue_fails',
        'extra_queue_not_exact', 'stationarity_required')},
    **{'ECC.ClosedWalk.'+n: {'propext'} for n in (
        'update_self', 'update_other', 'finish_coordinate', 'coordinate_step_update',
        'valid_head_cartesian', 'replay_split', 'before_length', 'replay_length',
        'before_eq_dropLast', 'closed_replay_split', 'update_cartesian_iff',
        'product_walk_iff_valid')},
    **{'ECC.ClosedWalk.'+n: {'propext', 'Quot.sound'} for n in (
        'closure_iff', 'valid_iff_factor_walks', 'closed_valid_iff',
        'closed_walk_realizable_iff', 'trace_injective_iff_nodup',
        'before_transitions', 'closed_replay_not_nodup')},
    **{'ECC.ClosedControls.'+n: {'propext'} for n in (
        'colliding_same_queues', 'paired_triangle_profile')},
    **{'ECC.ClosedControls.'+n: {'propext', 'Quot.sound'} for n in (
        'prism_valid_closed', 'prism_departures_distinct', 'prism_full_replay_repeats',
        'colliding_closed_walk_not_cycle', 'closure_not_edges',
        'paired_triangles_valid_simple', 'paired_closed_factor_walks')},
    **{'ECC.CycleTrace.'+n: set() for n in ('state_zero', 'state_end')},
    **{'ECC.CycleTrace.'+n: {'propext'} for n in (
        'before_get_state', 'trace_eq_state', 'valid_iff_state_edges')},
    **{'ECC.CycleTrace.'+n: {'propext', 'Quot.sound'} for n in (
        'trace_next_eq_state', 'closed_trace_edges_iff', 'closed_cycle_iff',
        'closed_cycle_iff_factor_walks', 'cycle_data_iff')},
    **{'ECC.CycleControls.'+n: {'propext', 'Quot.sound'} for n in (
        'prism_is_cycle', 'paired_is_cycle', 'colliding_is_not_cycle',
        'invalid_closed_trace_not_cycle', 'open_endpoint_same_trace',
        'closure_assumption_needed', 'length_bound_needed')},
    'ECC.ExecutableTrace.events_axes': set(),
    **{'ECC.ExecutableTrace.'+n: {'propext'} for n in ('get_modify_safe', 'events_length')},
    **{'ECC.ExecutableTrace.'+n: {'propext', 'Quot.sound'} for n in (
        'encode_injective', 'read_update', 'raw_tick', 'raw_read',
        'vertices_eq_encoded_departures', 'finish_events', 'endPos_coordinate',
        'closure_if_periods_divide_steps', 'distinct_iff_nodup', 'encoded_nodup_iff',
        'executable_collision_iff', 'executable_injectivity_iff', 'executable_cycle_iff')},
    **{'ECC.ExecutableControls.'+n: {'propext'} for n in (
        'prism_literal_inputs', 'prism_events_match', 'colliding_shuffle_fails',
        'paired_literal_inputs_and_events')},
    **{'ECC.ExecutableControls.'+n: {'propext', 'Quot.sound'} for n in (
        'prism_collision_passes', 'paired_collision_passes',
        'profile_counts_give_closure', 'malformed_default_controls')},
    'ECC.WordGenerator.map_lift': set(),
    **{'ECC.WordGenerator.'+n: {'propext', 'Quot.sound'} for n in (
        'matches_nil_iff', 'matches_cons_iff', 'mem_words_zero', 'mem_words_succ',
        'mem_words_iff', 'range_nodup_safe', 'prefix_nodup', 'branch_head',
        'branches_disjoint', 'words_nodup', 'accepted_nodup', 'mem_accepted_iff',
        'steps_eq_raw_count', 'generated_typed_axes', 'kernel_membership_iff',
        'kernel_words_nodup')},
    **{'ECC.WordControls.'+n: {'propext'} for n in (
        'profile_word_counts', 'zero_inventory_controls', 'inconsistent_budget_rejected')},
    **{'ECC.WordControls.'+n: {'propext', 'Quot.sound'} for n in (
        'wrong_multiplicity_rejected', 'illegal_axis_rejected', 'witnesses_occur_once',
        'typed_lift_control')},
    **{'ECC.PatternGenerator.'+n: set() for n in (
        'extension_nil', 'pattern_branch_mem', 'cyclic_starts_zero', 'patterns_zero')},
    'ECC.PatternGenerator.extension_cons_iff': {'propext'},
    **{'ECC.PatternGenerator.'+n: {'propext', 'Quot.sound'} for n in (
        'mem_grow_zero', 'mem_grow_succ', 'mem_grow_iff', 'grow_length', 'grow_prefix',
        'grow_branches_disjoint', 'pattern_branches_disjoint', 'grow_nodup',
        'cyclic_length_ge_two', 'mem_patterns_iff', 'patterns_nodup')},
    **{'ECC.PatternControls.'+n: set() for n in (
        'four_patterns_exact', 'bounded_inventory_sizes')},
    **{'ECC.PatternControls.'+n: {'propext', 'Quot.sound'} for n in (
        'motif_words_occur_once', 'adjacent_collision_rejected', 'closing_collision_rejected',
        'skipped_label_rejected', 'nonzero_first_rejected')},
}


def main():
    version = subprocess.check_output([LEAN, '--version'], cwd=ROOT, text=True).strip()
    expected_version = (ROOT/'lean-toolchain').read_text().strip().rsplit(':', 1)[1].removeprefix('v')
    if not version.startswith('Lean (version '+expected_version+','):
        raise RuntimeError('Compiler differs from lean-toolchain: '+version)
    print(version, flush=True)
    actual = {}
    pattern = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)$")
    with tempfile.TemporaryDirectory(prefix='ecc-lean-') as build:
        env = dict(os.environ, LEAN_PATH=build)
        for args in [('-o', str(Path(build)/'Shuffle.olean'), 'Shuffle.lean'),
                     ('-o', str(Path(build)/'CollisionBridge.olean'), 'CollisionBridge.lean'),
                     ('CollisionControls.lean',),
                     ('-o', str(Path(build)/'CanonicalTrace.olean'), 'CanonicalTrace.lean'),
                     ('-o', str(Path(build)/'CanonicalControls.olean'), 'CanonicalControls.lean'),
                     ('-o', str(Path(build)/'RankCompression.olean'), 'RankCompression.lean'),
                     ('RankControls.lean',),
                     ('-o', str(Path(build)/'EventShuffle.olean'), 'EventShuffle.lean'),
                     ('-o', str(Path(build)/'EventControls.olean'), 'EventControls.lean'),
                     ('-o', str(Path(build)/'ClosedWalk.olean'), 'ClosedWalk.lean'),
                     ('-o', str(Path(build)/'ClosedControls.olean'), 'ClosedControls.lean'),
                     ('-o', str(Path(build)/'CycleTrace.olean'), 'CycleTrace.lean'),
                     ('-o', str(Path(build)/'CycleControls.olean'), 'CycleControls.lean'),
                     ('-o', str(Path(build)/'ExecutableTrace.olean'), 'ExecutableTrace.lean'),
                     ('ExecutableControls.lean',),
                     ('-o', str(Path(build)/'WordGenerator.olean'), 'WordGenerator.lean'),
                     ('WordControls.lean',),
                     ('-o', str(Path(build)/'PatternGenerator.olean'), 'PatternGenerator.lean'),
                     ('PatternControls.lean',)]:
            run = subprocess.run([LEAN, *args], cwd=ROOT, env=env, text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            print(run.stdout, end='', flush=True)
            run.check_returncode()
            for line in run.stdout.splitlines():
                match = pattern.fullmatch(line)
                if not match:
                    raise RuntimeError('Unexpected Lean output: '+line)
                name, axioms = match.groups()
                if name in actual:
                    raise RuntimeError('Duplicate axiom declaration: '+name)
                actual[name] = {a.strip() for a in axioms.split(',')} if axioms else set()
    if actual != EXPECTED:
        raise RuntimeError('Axiom audit differs: '+repr(actual))
    print('PASS: 198 exact declaration audits; no placeholders, choice, or native-evaluation axioms')


if __name__ == '__main__':
    main()
