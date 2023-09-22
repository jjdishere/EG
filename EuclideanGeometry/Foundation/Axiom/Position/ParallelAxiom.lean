import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem ang_eq_ang_of_toDir_eq_toDir {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = ang₂.start_ray.toDir) (he : ang₁.end_ray.toDir = ang₂.end_ray.toDir) : ang₁.value = ang₂.value := sorry

theorem start_ray_toDir_eq_toDir_of_ang_eq_ang {ang₁ ang₂ : Angle P} (hs : ang₁.end_ray.toDir = ang₂.end_ray.toDir) (h : ang₁.value = ang₂.value) : ang₁.start_ray.toDir = ang₂.start_ray.toDir := sorry

theorem end_ray_toDir_eq_toDir_of_ang_eq_ang {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = ang₂.start_ray.toDir) (h : ang₁.value = ang₂.value) : ang₁.end_ray.toDir = ang₂.end_ray.toDir := sorry

end EuclidGeom