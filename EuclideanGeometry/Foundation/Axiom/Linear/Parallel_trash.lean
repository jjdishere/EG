import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

-- Later we need a version of this theorem in class DirFig
theorem Seg_nd.para_self_rev (seg_nd : Seg_nd P) : seg_nd ∥ seg_nd.reverse := Eq.symm (Seg_nd.toproj_of_rev_eq_toproj seg_nd)
-- The followings are corollaries:

theorem Seg_nd.para_rev_of_para (seg_nd seg_nd' : Seg_nd P) : (seg_nd ∥ seg_nd') ↔ (seg_nd ∥ seg_nd'.reverse) := ⟨fun z => Eq.trans z (Seg_nd.para_self_rev seg_nd'), fun z => Eq.trans z (Eq.symm (Seg_nd.para_self_rev seg_nd'))⟩

theorem Seg_nd.not_para_rev_of_not_para (seg_nd seg_nd' : Seg_nd P) : (¬ seg_nd ∥ seg_nd') → (¬ seg_nd ∥ seg_nd'.reverse) := by
  let g := (Seg_nd.para_rev_of_para seg_nd seg_nd').2
  tauto

end EuclidGeom
