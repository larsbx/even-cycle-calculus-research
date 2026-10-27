"""New ordinary-cycle DFS using only pinned generic adjacency constructors."""
from pathlib import Path
import importlib.util, sys, json
from collections import Counter
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
from source import checked_source
src = checked_source()
spec = importlib.util.spec_from_file_location('gpr_generic', src/'oracles/graph_ring_support.py')
gpr = importlib.util.module_from_spec(spec); spec.loader.exec_module(gpr)

def inventory(factors, m=8):
    adj = gpr.cartesian(factors)
    counts = Counter()
    witnesses = {}
    for root in sorted(adj):
        def dfs(path, axes):
            v = path[-1]
            if len(path) == m:
                for w, a in adj[v]:
                    if w == root and path[1] < path[-1]:
                        word = axes + [a]
                        steps = tuple(word.count(i) for i in range(len(factors)))
                        counts[steps] += 1
                        witnesses.setdefault(steps, path + [root])
                return
            for w, a in adj[v]:
                if w > root and w not in path:
                    dfs(path+[w], axes+[a])
        dfs([root], [])
    return {'total': sum(counts.values()), 'strata': [
        {'coordinate_steps': list(k), 'count': v, 'witness': witnesses[k]}
        for k,v in sorted(counts.items())]}

def main():
    k2 = gpr.graph(2, [(0,1)])
    p3 = gpr.graph(3, [(0,1),(1,2)])
    k3 = gpr.graph(3, [(0,1),(1,2),(2,0)])
    c4 = gpr.graph(4, [(i,(i+1)%4) for i in range(4)])
    rows = [{'case': name, **inventory(factors)} for name,factors in [
        ('C4 square K2',[c4,k2]), ('K3 square K3',[k3,k3]),
        ('P3 square K3',[p3,k3]), ('K2 square K3 square K3',[k2,k3,k3]), ('Q4',[k2]*4)]]
    assert rows[0]['total'] == 6
    assert any(s['coordinate_steps']==[2,3,3] and s['count']>0 for s in rows[3]['strata'])
    assert rows[-1]['total'] == 696
    assert next(s['count'] for s in rows[-1]['strata'] if s['coordinate_steps']==[2]*4) == 648
    assert sum(s['count'] for s in rows[-1]['strata'] if len([x for x in s['coordinate_steps'] if x]) < 4) == 48
    # Negative control: dividing ordinary copies again by 16 loses integrality on Q3.
    assert rows[0]['total'] % 16 != 0
    print(json.dumps({'domain':'five specified products; ordinary c8', 'cases':rows,
        'status':'bounded inventory; lower-support formula remains open'}, indent=2))


if __name__ == "__main__":
    main()
