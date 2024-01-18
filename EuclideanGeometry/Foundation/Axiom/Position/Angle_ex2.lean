import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Linear.Collinear

noncomputable section

namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]



section AngleValue

/- theorem when angle > 0, IsInt means lies left of start ray + right of end ray; when angle < 0, ...  -/

end AngleValue

section angle_sum

namespace Angle

-- Can use congrArg @Ray.source P _) h to turn h into the sources of two terms being equal.
theorem source_eq_source_of_adj {ang₁ ang₂: Angle P} (h : ang₁.end_ray = ang₂.start_ray) : ang₁.start_ray.source = ang₂.end_ray.source := sorry

def sum_adj {ang₁ ang₂: Angle P} (h : ang₁.end_ray = ang₂.start_ray) : Angle P :=
  Angle.mk_two_ray_of_eq_source ang₁.start_ray ang₂.end_ray (source_eq_source_of_adj h)

theorem ang_eq_ang_add_ang_mod_pi_of_adj_ang (ang₁ ang₂ : Angle P) (h: ang₁.end_ray = ang₂.start_ray) : (sum_adj h).value = ang₁.value + ang₂.value := sorry

end Angle

end angle_sum

section angle_sub

end angle_sub


end EuclidGeom
