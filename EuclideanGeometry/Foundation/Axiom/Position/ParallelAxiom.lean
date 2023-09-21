import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem ang_eq_ang_of_toDir_eq_toDir {oang₁ oang₂ : OAngle P} (hs : oang₁.start_ray.toDir = oang₂.start_ray.toDir) (he : oang₁.end_ray.toDir = oang₂.end_ray.toDir) : oang₁.value = oang₂.value := sorry

theorem start_ray_toDir_eq_toDir_of_ang_eq_ang {oang₁ oang₂ : OAngle P} (hs : oang₁.end_ray.toDir = oang₂.end_ray.toDir) (h : oang₁.value = oang₂.value) : oang₁.start_ray.toDir = oang₂.start_ray.toDir := sorry

theorem end_ray_toDir_eq_toDir_of_ang_eq_ang {oang₁ oang₂ : OAngle P} (hs : oang₁.start_ray.toDir = oang₂.start_ray.toDir) (h : oang₁.value = oang₂.value) : oang₁.end_ray.toDir = oang₂.end_ray.toDir := sorry

end EuclidGeom