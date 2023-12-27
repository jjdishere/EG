import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

namespace Congruence_exercise_ygr_7

/-
Let $A, B, C, D$ be four points on the plane such that $A, B, C$ are not colinear, and that $A, B, D$ are not colinear.Let $O$ be the intersection of segment $AD$ and segment $BC$.
If $\angle ACO = - \angle BDO$ and $OA = OB$, Prove that $AD = BC$.
-/

structure Setting (Plane : Type _) [EuclideanPlane Plane] where
-- Let $A, B, C, D$ be four points on the plane,
  A : Plane
  B : Plane
  C : Plane
  D : Plane
-- such that $A, B, C$ are not colinear,
  not_colinear_ABC : ¬ colinear A B C
-- and that $A, B, D$ are not colinear.
  not_colinear_ABD : ¬ colinear A B D
-- Let $O$ be the intersection of segment $AD$ and segment $BC$.
  O : Plane
  O_int_AD : O LiesInt (SEG A D)
  O_int_BC : O LiesInt (SEG B C)
-- Claim : $C \ne A$.
  C_ne_A : PtNe C A := ⟨(ne_of_not_colinear not_colinear_ABC).2.1.symm⟩
-- Claim : $D \ne B$.
  B_ne_D : PtNe B D := ⟨(ne_of_not_colinear not_colinear_ABD).1.symm⟩
-- Claim : $O \ne C$.
  O_ne_C : PtNe O C := ⟨ne_source_of_lies_int_seg C B O (Seg.lies_int_rev_iff_lies_int.mpr O_int_BC)⟩
-- Claim : $O \ne D$.
  O_ne_D : PtNe O D := ⟨ne_source_of_lies_int_seg D A O (Seg.lies_int_rev_iff_lies_int.mpr O_int_AD)⟩
-- If $\angle ACO = - \angle BDO$
  angle_ACO_eq_neg_angle_BDO : ∠ A C O = - (∠ B D O)
-- and $OA = OB$.
  OA_eq_OB : (SEG O A).length = (SEG O B).length

theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : (SEG e.A e.D).length = (SEG e.B e.C).length := by sorry


end Congruence_exercise_ygr_7

end EuclidGeom
