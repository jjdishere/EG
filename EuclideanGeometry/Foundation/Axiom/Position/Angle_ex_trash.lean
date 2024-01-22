import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex2

namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

theorem perp_foot_lies_int_ray_of_acute_ang {A B C : P} (b_ne_a : B ≠ A) (c_ne_a : C ≠ A) (acu : Angle.IsAcu (ANG B A C b_ne_a c_ne_a)) : (perp_foot C (LIN A B b_ne_a)) LiesInt (RAY A B b_ne_a) := by sorry

theorem perp_foot_lies_int_ray_rev_of_acute_ang {A B C : P} [b_ne_a : PtNe B A] [c_ne_a : PtNe C A] (obt : Angle.IsObt (ANG B A C)) : (perp_foot C (LIN A B)) LiesInt (RAY A B).reverse := by sorry

theorem perp_foot_eq_source_of_right_ang {A B C : P} [b_ne_a : PtNe B A] [c_ne_a : PtNe C A] (rgt : Angle.IsRight (ANG B A C)) : (perp_foot C (LIN A B)) = A := by sorry

theorem is_acute_of_is_acute_rev {O A B : P} (h1 : A ≠ O) (h2 : B ≠ O) (h3 : Angle.IsAcu (ANG A O B h1 h2)) : Angle.IsAcu (ANG B O A h2 h1) := by sorry

theorem ang_eq_ang_of_toDir_eq_neg_toDir {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = - ang₂.start_ray.toDir) (he : ang₁.end_ray.toDir = - ang₂.end_ray.toDir) : Angle.value ang₁ = Angle.value ang₂ := by sorry

theorem ang_value_eq_ang_value_add_ang_value (A B C O : P) [hne1 : PtNe A O] [hne2 : PtNe B O] [hne3 : PtNe C O]: (∠ A O B) + (∠ B O C) = (∠ A O C) := by
  symm;
  apply Angle.ang_eq_ang_add_ang_mod_pi_of_adj_ang (ANG A O B) (ANG B O C) _
  unfold Angle.mk_pt_pt_pt
  rfl

end EuclidGeom
