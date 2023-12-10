import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Linear.Colinear

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]



section AngleValue


/- theorem - π < angle.value, angle.value ≤ π,  -/
theorem val_gt_neg_pi (ang : Angle P) : -π < ang.value.toReal := sorry

theorem val_le_pi (ang : Angle P) : ang.value.toReal < π := sorry

/- theorem when angle > 0, IsInt means lies left of start ray + right of end ray; when angle < 0, ...  -/

theorem undefined : sorry := sorry

end AngleValue

section AngleSum

namespace Angle

theorem source_start_ray_eq_source_end_ray (ang : Angle P) : ang.start_ray.source = ang.end_ray.source := sorry


-- Can use congrArg @Ray.source P _) h to turn h into the sources of two terms being equal.
theorem source_eq_source_of_adj {ang₁ ang₂: Angle P} (h : ang₁.end_ray = ang₂.start_ray) : ang₁.start_ray.source = ang₂.end_ray.source := sorry

def sum_adj {ang₁ ang₂: Angle P} (h :ang₁.end_ray = ang₂.start_ray) : Angle P := Angle.mk ang₁.start_ray ang₂.end_ray (source_eq_source_of_adj h)

theorem ang_eq_ang_add_ang_mod_pi_of_adj_ang (ang₁ ang₂ : Angle P) (h: ang₁.end_ray = ang₂.start_ray) : (sum_adj h).value = ang₁.value + ang₂.value := sorry

end Angle

end AngleSum

section colinear

theorem colinear_of_angle_eq_zero {A O B : P} {h₁ : A ≠ O} {h₂ : B ≠ O} : ∠ A O B h₁ h₂ = 0 → colinear O A B := by sorry

theorem colinear_of_angle_eq_pi {A O B : P} {h₁ : A ≠ O} {h₂ : B ≠ O} : ∠ A O B h₁ h₂ = π → colinear O A B := by sorry

end colinear

end EuclidGeom
