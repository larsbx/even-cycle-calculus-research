"""Independent inversion, quotient-hom and counting-convention regressions."""
from collections import Counter
from itertools import permutations
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from kernels.partition_lattice import (partitions, refines, refinements,
                                       mobius, invert, quotient_homs)
from experiments.partition_inversion import UnrestrictedWalks, fixture, combine


class PartitionInversion(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.context = UnrestrictedWalks()
        cls.engine = cls.context.__enter__()

    @classmethod
    def tearDownClass(cls):
        cls.context.__exit__(None, None, None)

    def test_lattice_refinements_and_mobius_cancellation(self):
        self.assertEqual([len(partitions(n)) for n in range(11)],
                         [1,1,2,5,15,52,203,877,4140,21147,115975])
        for n in range(1,7):
            for kappa in partitions(n):
                explicit = {rho for rho in partitions(n) if refines(rho,kappa)}
                generated = refinements(kappa)
                self.assertEqual(len(generated),len(set(generated)))
                self.assertEqual(set(generated),explicit)
                self.assertEqual(sum(map(mobius,generated)),int(max(kappa)+1 == n))
        self.assertEqual(mobius((0,0,0,1,1)), -2)

    def test_all_small_target_traces_against_direct_quotient(self):
        # Directly assign vertices of every quotient, with coincidences allowed.
        for name in ('edge','wedge','triangle'):
            factors = [fixture(name)]
            for length in range(3,7):
                hist, adj = self.engine.run(factors,length)
                answer,homs,_ = invert(combine(hist.values()),length)
                for rho in partitions(length):
                    self.assertEqual(quotient_homs(adj,rho),homs[rho],(name,length,rho))
                # Closed source walks in K2 have no injective cycle.
                if name == 'edge': self.assertEqual(answer,0)

    def test_repeated_vertices_and_wrong_mobius(self):
        hist,_ = self.engine.run([fixture('edge')],4)
        answer,homs,ledger = invert(combine(hist.values()),4)
        self.assertEqual((answer,dict(ledger)),(0,{2:2,3:-4,4:2}))
        # Omitting nondiscrete terms retains two repeated-vertex closed walks.
        self.assertEqual(homs[(0,1,2,3)],2)
        self.assertEqual(sum(abs(mobius(p))*v for p,v in homs.items()),8)
        self.assertEqual(quotient_homs([{1:0},{0:0}],(0,0,1,1)),0)

    def test_nonsimple_projection_and_root_dependent_patterns(self):
        hist,_ = self.engine.run([fixture('wedge')]+[fixture('edge')]*3,
                                10,(4,2,2,2),0)
        rooted = {pattern:invert(counts,10)[0] for (_,pattern),counts in hist.items()}
        self.assertEqual(rooted,{'0101':21120,'0102':40992,'0121':64128})
        self.assertNotEqual(rooted['0102'] % 20,0)
        self.assertEqual(sum(rooted.values())//20,6312)
        # Keeping only simple four-step projections incorrectly predicts zero.
        self.assertNotIn('0123',rooted)
        with self.assertRaises(ValueError):
            self.engine.run([fixture('edge')],8,(4,))

    def test_ordinary_induced_and_rooted_quotients(self):
        factor = fixture('K4')
        hist,_ = self.engine.run([factor],4)
        answer,_,_ = invert(combine(hist.values()),4)
        self.assertEqual(answer//8,3)
        induced = sum(all(t[j] not in factor[t[i]] for i in range(4) for j in range(i+1,4)
                          if (j-i) not in (1,3)) for t in permutations(range(4)))//8
        self.assertEqual(induced,0)
        hist,_ = self.engine.run([fixture('edge')]*2+[fixture('triangle')]*2,
                                10,(2,2,3,3))
        answer,_,_ = invert(combine(hist.values()),10)
        self.assertEqual(answer,1805760)
        self.assertEqual(sum(combine(hist.values()).values())//20,181440)
        self.assertEqual(answer//20,90288)
        self.assertNotEqual(answer//10,90288)
        self.assertEqual((answer//20)%20,8) # cannot divide already ordinary copies again

    def test_disconnected_fibers_and_relabeling(self):
        edge,triangle = fixture('edge'),fixture('triangle')
        hist,_ = self.engine.run([edge,triangle,triangle],8,(2,3,3))
        base=invert(combine(hist.values()),8)[0]
        hist,_ = self.engine.run([edge,[set()]*3,triangle,triangle],8,(2,0,3,3))
        self.assertEqual(invert(combine(hist.values()),8)[0],3*base)
        renamed=[{2-v for v in triangle[2-u]} for u in range(3)]
        hist,_ = self.engine.run([renamed,edge,triangle],8,(3,2,3))
        self.assertEqual(invert(combine(hist.values()),8)[0],base)
        # c10: permuting coordinates preserves the marked profile, and an
        # independent repeated-edge factor contributes its two selected edges.
        wedge=fixture('wedge')
        hist,_ = self.engine.run([edge,wedge,edge,wedge],10,(2,4,2,2))
        self.assertEqual(invert(combine(hist.values()),10)[0]//20,2*6312)
        hist,_ = self.engine.run([[],triangle],8)
        self.assertEqual(hist,{})


if __name__ == '__main__':
    unittest.main()
