import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash

namespace EuclidGeom

open AngValue

variable {P : Type _} [EuclideanPlane P]

theorem end_ray_toDir_rev_toDir_of_ang_rev_ang {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = (ang₂.start_ray).reverse.toDir) (h : ang₁.value = ang₂.value) : ang₁.end_ray.toDir = (ang₂.end_ray).reverse.toDir := sorry

theorem start_ray_toDir_rev_toDir_of_ang_rev_ang {ang₁ ang₂ : Angle P} (hs : ang₁.end_ray.toDir = (ang₂.end_ray).reverse.toDir) (h : ang₁.value = ang₂.value) : ang₁.start_ray.toDir = (ang₂.start_ray).reverse.toDir := sorry

theorem ang_eq_ang_of_toDir_rev_toDir {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = - ang₂.start_ray.toDir) (he : ang₁.end_ray.toDir = - ang₂.end_ray.toDir) : ang₁.value = ang₂.value := sorry

theorem neg_dvalue_of_rev_ang {A B O: P} (h₁ : A ≠ O) (h₂ : B ≠ O) : (ANG A O B h₁ h₂).dvalue = -(ANG B O A h₂ h₁).dvalue := sorry

namespace Angle

end Angle

end EuclidGeom
