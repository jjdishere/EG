import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex2

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem perp_foot_lies_int_ray_of_acute_ang {A B C : P} (b_ne_a : B ≠ A) (c_ne_a : C ≠ A) (acu : Angle.IsAcu (ANG B A C b_ne_a c_ne_a)) : (perp_foot C (LIN A B b_ne_a)) LiesInt (RAY A B b_ne_a) := by sorry

theorem perp_foot_lies_int_ray_rev_of_acute_ang {A B C : P} [b_ne_a : PtNe B A] [c_ne_a : PtNe C A] (obt : Angle.IsObtuseAngle (ANG B A C)) : (perp_foot C (LIN A B)) LiesInt (RAY A B).reverse := by sorry

theorem perp_foot_eq_source_of_right_ang {A B C : P} [b_ne_a : PtNe B A] [c_ne_a : PtNe C A] (rgt : Angle.IsRightAngle (ANG B A C)) : (perp_foot C (LIN A B)) = A := by sorry

theorem ang_acute_of_is_isoceles {A B C : P} (not_colinear_ABC : ¬ colinear A B C) (isoceles_ABC : (▵ A B C).IsIsoceles) : Angle.IsAcuteAngle (ANG C B A (ne_of_not_colinear not_colinear_ABC).1 (ne_of_not_colinear not_colinear_ABC).2.2.symm) := by sorry

theorem ang_acute_of_is_isoceles_variant {A B C : P} (not_collinear_ABC : ¬ Collinear A B C) (isoceles_ABC : (▵ A B C).IsIsoceles) : Angle.IsAcu (ANG A C B (ne_of_not_collinear not_collinear_ABC).2.1 (ne_of_not_collinear not_collinear_ABC).1.symm) := by sorry

theorem is_acute_of_is_acute_rev {O A B : P} (h1 : A ≠ O) (h2 : B ≠ O) (h3 : Angle.IsAcu (ANG A O B h1 h2)) : Angle.IsAcu (ANG B O A h2 h1) := by sorry

theorem ang_eq_ang_of_toDir_eq_neg_toDir {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = - ang₂.start_ray.toDir) (he : ang₁.end_ray.toDir = - ang₂.end_ray.toDir) : Angle.value ang₁ = Angle.value ang₂ := by sorry

theorem ang_value_eq_ang_value_add_ang_value (A B C O : P) [hne1 : PtNe A O] [hne2 : PtNe B O] [hne3 : PtNe C O]: (∠ A O B) + (∠ B O C) = (∠ A O C) := by
  symm;
  apply Angle.ang_eq_ang_add_ang_mod_pi_of_adj_ang (ANG A O B) (ANG B O C) _
  unfold Angle.mk_pt_pt_pt
  rfl

end EuclidGeom
