/-
  Cross-check (not part of the build): count crossing and touching curve pairs over all faces of the certificate.
  The independent Python referee ref37_v2.py reports 526 crossing pairs and 475 touching pairs.
-/
import Venn37.Cert
import Venn37.Decide

namespace Venn8

def pairsOn (f : Face) : List (ℕ × ℕ) :=
  ((List.range 8).flatMap fun i => (List.range 8).map fun k => (i, k)).filter fun p =>
    p.1 < p.2 && (dirPositions f p.1).length == 2 && (dirPositions f p.2).length == 2

#eval (cert.flatMap fun f => (pairsOn f).filter fun p => decide (CrossAt f p.1 p.2)).length
#eval (cert.flatMap fun f => (pairsOn f).filter fun p => !decide (CrossAt f p.1 p.2)).length
#eval decide (CrossingAtEachPoint cert)
-- the 4-cycle 0,1,3,2 has direction pattern 0,1,0,1 (i,k,i,k): a crossing
#eval decide (CrossAt [0, 1, 3, 2] 0 1)

end Venn8
