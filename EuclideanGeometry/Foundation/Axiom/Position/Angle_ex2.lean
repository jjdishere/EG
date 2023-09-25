import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex
import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Convex
import EuclideanGeometry.Foundation.Axiom.Linear.Colinear


noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]



section AngleValue


/- theorem - π < angle.value, angle.value ≤ π,  -/
theorem val_gt_neg_pi (oang : OAngle P) : -π < oang.value := sorry

theorem val_le_pi (oang : OAngle P) : oang.value < π := sorry

/- theorem when angle > 0, IsInt means lies left of start ray + right of end ray; when angle < 0, ...  -/

theorem 

end AngleValue

section OAngleSum

namespace OAngle

theorem source_start_ray_eq_source_end_ray (oang : OAngle P) : oang.start_ray.source = oang.end_ray.source := sorry


-- Can use congrArg @Ray.source P _) h to turn h into the sources of two terms being equal.
theorem source_eq_source_of_adj {oang₁ oang₂: OAngle P} (h : oang₁.end_ray = oang₂.start_ray) : oang₁.start_ray.source = oang₂.end_ray.source := sorry


def sum_adj {oang₁ oang₂: OAngle P} (h :oang₁.end_ray = oang₂.start_ray) : OAngle P := OAngle.mk oang₁.start_ray oang₂.end_ray (source_eq_source_of_adj h)




theorem ang_eq_ang_add_ang_mod_pi_of_adj_oang (oang₁ oang₂ : OAngle P) (h: oang₁.end_ray = oang₂.start_ray) : (sum_adj h).value = oang₁.value + oang₂.value ∨ (sum_adj h).value = oang₁.value + oang₂.value + π ∨ (sum_adj h).value = oang₁.value + oang₂.value - π := sorry



end OAngle 

end OAngleSum

section AngleColinear

namespace OAngle

theorem colinear_of_zero_angle (A O B : P) (h₁ : A ≠ O) (h₂ : B ≠ O) : (OAngle.mk_pt_pt_pt A O B h₁ h₂).value = 0 → colinear A O B  := by sorry

end OAngle

end AngleColinear

end EuclidGeom