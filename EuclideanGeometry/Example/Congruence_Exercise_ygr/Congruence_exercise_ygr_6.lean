import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

namespace Congruence_exercise_ygr_6

/-
In $\triangle ABC$, let $D$, $E$ be points on the segment $BC$, such that $AD = AE$ and $\angle BAD = - \angle CAE$.

Prove that $AB = AC$
-/

structure Setting1 (Plane : Type _) [EuclideanPlane Plane] where
-- Let $\triangle ABC$ be a triangle.
  A : Plane
  B : Plane
  C : Plane
  not_colinear_ABC : ¬ colinear A B C
-- Claim : $B \ne A$.
  B_ne_A : PtNe B A := ⟨(ne_of_not_colinear not_colinear_ABC).2.2⟩
-- Claim : $C \ne A$.
  C_ne_A : PtNe C A := ⟨(ne_of_not_colinear not_colinear_ABC).2.1.symm⟩
-- Let $D$ be a point on the segment $BC$.
  D : Plane
  D_int_BC : D LiesInt (SEG B C)
-- Let $E$ be a point on the segment $BC$.
  E : Plane
  E_int_BC : E LiesInt (SEG B C)

attribute [instance] Setting1.B_ne_A Setting1.C_ne_A
instance D_ne_A {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.D e.A := by
  have h1 : ¬ colinear e.A e.B e.C := e.not_colinear_ABC
  have : e.D ≠ e.A := by
    by_contra h
    have h2 : ¬ colinear e.D e.B e.C := by simp only [h]; exact h1
    absurd h2
    have h3 : e.D LiesOn (SEG e.B e.C) := by apply Seg.lies_on_of_lies_int e.D_int_BC
    have h4 : e.B LiesOn (SEG e.B e.C) := by apply Seg.source_lies_on
    have h5 : e.C LiesOn (SEG e.B e.C) := by apply Seg.target_lies_on
    exact Seg.colinear_of_lies_on h3 h4 h5
  exact ⟨this⟩

instance E_ne_A {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.E e.A := by
  have h1 : ¬ colinear e.A e.B e.C := e.not_colinear_ABC
  have : e.E ≠ e.A := by
    by_contra h
    have h2 : ¬ colinear e.E e.B e.C := by simp only [h]; exact h1
    absurd h2
    have h3 : e.E LiesOn (SEG e.B e.C) := by apply Seg.lies_on_of_lies_int e.E_int_BC
    have h4 : e.B LiesOn (SEG e.B e.C) := by apply Seg.source_lies_on
    have h5 : e.C LiesOn (SEG e.B e.C) := by apply Seg.target_lies_on
    exact Seg.colinear_of_lies_on h3 h4 h5
  exact ⟨this⟩

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends Setting1 Plane where
-- such that $AD = AE$.
  AD_eq_AE : (SEG A D).length = (SEG A E).length
-- and $\angle BAD = - \angle CAE$
  angle_BAD_eq_neg_angle_CAE : ∠ B A D = - ∠ C A E

-- Prove that $AB = AC$.
theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting2 Plane) : (SEG e.A e.B).length = (SEG e.A e.C).length := by
  haveI D_ne_B : PtNe e.D e.B := ⟨ne_source_of_lies_int_seg e.B e.C e.D e.D_int_BC⟩
  haveI E_ne_C : PtNe e.E e.C := ⟨ne_source_of_lies_int_seg e.C e.B e.E (Seg.lies_int_rev_iff_lies_int.mp e.E_int_BC)⟩
  have not_colinear_BAD : ¬ colinear e.B e.A e.D := by sorry
  have not_colinear_CAE : ¬ colinear e.C e.A e.E := by sorry
  have angle_ABD_eq_neg_angle_ACE : (ANG e.A e.D e.B).dvalue = - (ANG e.A e.E e.C).dvalue := by sorry
  have triangle_BAD_acongr_triangle_CAE : (TRI_nd e.B e.A e.D not_colinear_BAD) ≅ₐ (TRI_nd e.C e.A e.E not_colinear_CAE) := by sorry
  calc
  (SEG e.A e.B).length
  _= (SEG e.B e.A).length := by apply length_of_rev_eq_length'
  _= (SEG e.C e.A).length := triangle_BAD_acongr_triangle_CAE.edge₃
  _= (SEG e.A e.C).length := by apply length_of_rev_eq_length'
end Congruence_exercise_ygr_6

end EuclidGeom
