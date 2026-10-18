/-
  Fast compiled evaluation of every condition on the certificate, plus negative controls. Not part of the proof.
-/
import Venn37.Cert
import Venn37.Decide

namespace Venn8

#eval (decide (Q8Subgraph cert), decide (Spanning cert), decide (FacesBalanced cert), decide (DartsPaired cert))
#eval (decide (LinksSingleCycles cert), decide (Connected cert), decide (EulerSphere cert), decide (CurvesSimple cert))
#eval (cert.length, (darts cert).length, (edges cert).length)
#eval decide (PreservesFaces cert halfTurn)
-- negative controls: each should give `false` somewhere
#eval (decide (Spanning cert.tail), decide (EulerSphere cert.tail), decide (DartsPaired cert.tail))
#eval let bad := (cert.head!.reverse) :: cert.tail
  (decide (DartsPaired bad), decide (LinksSingleCycles bad))
#eval decide (PreservesFaces cert (fun x => x ^^^ 1))

end Venn8
