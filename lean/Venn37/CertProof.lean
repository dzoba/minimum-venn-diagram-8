/-
  The 37-face certificate satisfies the BGMV dual conditions. Every proof is by kernel reduction (`decide +kernel`):
  no `native_decide`, no compiled code in the trusted base.
-/
import Venn37.Cert
import Venn37.Decide

namespace Venn8

set_option maxRecDepth 100000

theorem cert_length : cert.length = 37 := by decide +kernel

theorem cert_q8 : Q8Subgraph cert := by decide +kernel
theorem cert_spanning : Spanning cert := by decide +kernel
theorem cert_balanced : FacesBalanced cert := by decide +kernel
theorem cert_paired : DartsPaired cert := by decide +kernel
theorem cert_links : LinksSingleCycles cert := by decide +kernel
theorem cert_connected : Connected cert := by decide +kernel
theorem cert_euler : EulerSphere cert := by decide +kernel
theorem cert_in0 : InducedConnected cert (fun x => x.testBit 0) := by decide +kernel
theorem cert_out0 : InducedConnected cert (fun x => !x.testBit 0) := by decide +kernel
theorem cert_in1 : InducedConnected cert (fun x => x.testBit 1) := by decide +kernel
theorem cert_out1 : InducedConnected cert (fun x => !x.testBit 1) := by decide +kernel
theorem cert_in2 : InducedConnected cert (fun x => x.testBit 2) := by decide +kernel
theorem cert_out2 : InducedConnected cert (fun x => !x.testBit 2) := by decide +kernel
theorem cert_in3 : InducedConnected cert (fun x => x.testBit 3) := by decide +kernel
theorem cert_out3 : InducedConnected cert (fun x => !x.testBit 3) := by decide +kernel
theorem cert_in4 : InducedConnected cert (fun x => x.testBit 4) := by decide +kernel
theorem cert_out4 : InducedConnected cert (fun x => !x.testBit 4) := by decide +kernel
theorem cert_in5 : InducedConnected cert (fun x => x.testBit 5) := by decide +kernel
theorem cert_out5 : InducedConnected cert (fun x => !x.testBit 5) := by decide +kernel
theorem cert_in6 : InducedConnected cert (fun x => x.testBit 6) := by decide +kernel
theorem cert_out6 : InducedConnected cert (fun x => !x.testBit 6) := by decide +kernel
theorem cert_in7 : InducedConnected cert (fun x => x.testBit 7) := by decide +kernel
theorem cert_out7 : InducedConnected cert (fun x => !x.testBit 7) := by decide +kernel

theorem cert_curves : CurvesSimple cert := by
  intro j hj
  interval_cases j
  · exact ⟨cert_in0, cert_out0⟩
  · exact ⟨cert_in1, cert_out1⟩
  · exact ⟨cert_in2, cert_out2⟩
  · exact ⟨cert_in3, cert_out3⟩
  · exact ⟨cert_in4, cert_out4⟩
  · exact ⟨cert_in5, cert_out5⟩
  · exact ⟨cert_in6, cert_out6⟩
  · exact ⟨cert_in7, cert_out7⟩

/-- **The 37-face certificate satisfies the BGMV dual conditions for an 8-Venn diagram.** -/
theorem cert_isVennDual8 : IsVennDual8 cert :=
  ⟨cert_q8, cert_spanning, cert_balanced, cert_paired, cert_links, cert_connected, cert_euler, cert_curves⟩

/-- At every crossing point of the certificate some two curves cross (BGMV's definition). -/
theorem cert_crossing : CrossingAtEachPoint cert := by decide +kernel

/-- The half-turn (curves (0 6)(1 5)(2 4), then complement by XOR 247) is an orientation-preserving automorphism of
the certificate's face list. -/
theorem cert_halfTurn : PreservesFaces cert halfTurn := by decide +kernel

end Venn8
