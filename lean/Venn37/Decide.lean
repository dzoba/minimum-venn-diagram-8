/-
  Decidability instances for the conditions in Defs.lean (by unfolding to the standard instances).
-/
import Venn37.Defs

namespace Venn8

instance (fs : List Face) : Decidable (Q8Subgraph fs) := by unfold Q8Subgraph IsQ8Edge; infer_instance
instance (fs : List Face) : Decidable (Spanning fs) := by unfold Spanning; infer_instance
instance (fs : List Face) : Decidable (FacesBalanced fs) := by unfold FacesBalanced; infer_instance
instance (fs : List Face) : Decidable (DartsPaired fs) := by unfold DartsPaired; infer_instance
instance (fs : List Face) : Decidable (LinksSingleCycles fs) := by unfold LinksSingleCycles; infer_instance
instance (fs : List Face) (S : ℕ → Bool) : Decidable (InducedConnected fs S) := by
  unfold InducedConnected; infer_instance
instance (fs : List Face) : Decidable (Connected fs) := by unfold Connected; infer_instance
instance (fs : List Face) : Decidable (EulerSphere fs) := by unfold EulerSphere; infer_instance
instance (fs : List Face) : Decidable (CurvesSimple fs) := by unfold CurvesSimple; infer_instance
instance (f : Face) (i k : ℕ) : Decidable (CrossAt f i k) := by unfold CrossAt; infer_instance
instance (fs : List Face) : Decidable (CrossingAtEachPoint fs) := by unfold CrossingAtEachPoint; infer_instance
instance (fs : List Face) (g : ℕ → ℕ) : Decidable (PreservesFaces fs g) := by
  unfold PreservesFaces; infer_instance

end Venn8
