/-
  Main statement: the 37-face certificate is a BGMV dual of an 8-Venn diagram, and no face list satisfying the BGMV
  dual conditions has fewer than 37 faces. Together with BGMV's characterization theorem (cited, not formalized), a
  minimum 8-Venn diagram has exactly 37 crossings.
-/
import Venn37.CertProof
import Venn37.LowerBound
import Venn37.Sound

namespace Venn8

/-- The certificate satisfies the BGMV dual conditions together with "at every crossing point some two curves
cross"; it has 37 faces; and every face list satisfying the (weaker) BGMV dual conditions alone has at least 37
faces. -/
theorem min_venn8_37 :
    (IsVennDual8 cert ∧ CrossingAtEachPoint cert) ∧ cert.length = 37 ∧
      ∀ fs : List Face, IsVennDual8 fs → 37 ≤ fs.length :=
  ⟨⟨cert_isVennDual8, cert_crossing⟩, cert_length, faces_ge_37⟩

end Venn8
