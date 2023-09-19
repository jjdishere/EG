import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex
import EuclideanGeometry.Foundation.Axiom.Position.Angle


noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

section OAngleSum

namespace OAngle

theorem source_start_ray_eq_source_end_ray (oang : OAngle P) : oang.start_ray.source = oang.end_ray.source := sorry


-- Can use congrArg @Ray.source P _) h to turn h into the sources of two terms being equal.
theorem source_eq_source_of_adj {oang₁ oang₂: OAngle P} (h :oang₂.start_ray = oang₁.end_ray) : oang₁.source = oang₂.source := sorry


def sum_adj (oang₁ oang₂: OAngle P) (h :oang₂.start_ray = oang₁.end_ray) : OAngle P := OAngle.mk oang₁.start_ray oang₂.end_ray (source_eq_source_of_adj h)

theorem ang_eq_ang_add_ang_mod_pi_of_adj_oang (oang₁ oang₂ oang₃: OAngle P) (h: oang₁.end_ray = oang₂.start_ray)

/- Theorems such as if two adjacent angle add up to π, then the other ray form a line. -/

end OAngle 

section OAngleSum

end EuclidGeom