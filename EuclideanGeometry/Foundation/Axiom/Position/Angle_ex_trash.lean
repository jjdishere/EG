import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem perp_foot_lies_int_ray_of_acute_ang {A B C : P} (b_ne_a : B ≠ A) (c_ne_a : C ≠ A) (acu : Angle.IsAcu (ANG B A C b_ne_a c_ne_a)) : (perp_foot C (LIN A B b_ne_a)) LiesInt (RAY A B b_ne_a) := by sorry

theorem ang_acute_of_is_isoceles {A B C : P} (not_collinear_ABC : ¬ Collinear A B C) (isoceles_ABC : (▵ A B C).IsIsoceles) : Angle.IsAcu (ANG C B A (ne_of_not_collinear not_collinear_ABC).1 (ne_of_not_collinear not_collinear_ABC).2.2.symm) := by sorry

theorem ang_acute_of_is_isoceles_variant {A B C : P} (not_collinear_ABC : ¬ Collinear A B C) (isoceles_ABC : (▵ A B C).IsIsoceles) : Angle.IsAcu (ANG A C B (ne_of_not_collinear not_collinear_ABC).2.1 (ne_of_not_collinear not_collinear_ABC).1.symm) := by sorry

theorem is_acute_of_is_acute_rev {O A B : P} (h1 : A ≠ O) (h2 : B ≠ O) (h3 : Angle.IsAcu (ANG A O B h1 h2)) : Angle.IsAcu (ANG B O A h2 h1) := by sorry

theorem ang_eq_ang_of_toDir_eq_neg_toDir {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = - ang₂.start_ray.toDir) (he : ang₁.end_ray.toDir = - ang₂.end_ray.toDir) : Angle.value ang₁ = Angle.value ang₂ := by sorry

end EuclidGeom
