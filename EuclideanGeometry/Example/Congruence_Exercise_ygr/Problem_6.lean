import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex_trash

noncomputable section

namespace EuclidGeom

namespace Problem_6

/-
In $\triangle ABC$, let $D$, $E$ be different points on the segment $BC$, such that the points on segment $BC$ are arranged in the order $B, D, E, C$, $AD = AE$ and $\angle BAD = - \angle CAE$.

Prove that $AB = AC$
-/

structure Setting1 (Plane : Type _) [EuclideanPlane Plane] where
-- Let $\triangle ABC$ be a triangle.
  A : Plane
  B : Plane
  C : Plane
  not_collinear_ABC : ¬ Collinear A B C
-- Claim : $B \ne A$.
  B_ne_A : PtNe B A := ⟨(ne_of_not_collinear not_collinear_ABC).2.2⟩
-- Claim : $C \ne A$.
  C_ne_A : PtNe C A := ⟨(ne_of_not_collinear not_collinear_ABC).2.1.symm⟩
-- Let $D$ be a point on the segment $BC$.
  D : Plane
  D_int_BC : D LiesInt (SEG B C)
-- Let $E$ be a point on the segment $BC$, different to $D$.
  E : Plane
  E_int_BC : E LiesInt (SEG B C)
  E_ne_D : PtNe E D
-- Claim : $E \ne B$.
  E_ne_B : PtNe E B := ⟨E_int_BC.2⟩
-- Claim : $D \ne C$.
  D_ne_C : PtNe D C := ⟨(Seg.lies_int_rev_iff_lies_int.mpr D_int_BC).2⟩
-- such that the points on segment $BC$ are arranged in the order $B, D, E, C$
  D_int_BE : D LiesInt (SEG_nd B E)
  E_int_DC : E LiesInt (SEG_nd D C)


attribute [instance] Setting1.B_ne_A Setting1.C_ne_A Setting1.E_ne_D Setting1.E_ne_B Setting1.D_ne_C
instance D_ne_A {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.D e.A := by
  have h1 : ¬ Collinear e.A e.B e.C := e.not_collinear_ABC
  have : e.D ≠ e.A := by
    by_contra h
    have h2 : ¬ Collinear e.D e.B e.C := by simp only [h]; exact h1
    absurd h2
    have h3 : e.D LiesOn (SEG e.B e.C) := by apply Seg.lies_on_of_lies_int e.D_int_BC
    have h4 : e.B LiesOn (SEG e.B e.C) := by apply Seg.source_lies_on
    have h5 : e.C LiesOn (SEG e.B e.C) := by apply Seg.target_lies_on
    exact Seg.collinear_of_lies_on h3 h4 h5
  exact ⟨this⟩

instance E_ne_A {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.E e.A := by
  have h1 : ¬ Collinear e.A e.B e.C := e.not_collinear_ABC
  have : e.E ≠ e.A := by
    by_contra h
    have h2 : ¬ Collinear e.E e.B e.C := by simp only [h]; exact h1
    absurd h2
    have h3 : e.E LiesOn (SEG e.B e.C) := by apply Seg.lies_on_of_lies_int e.E_int_BC
    have h4 : e.B LiesOn (SEG e.B e.C) := by apply Seg.source_lies_on
    have h5 : e.C LiesOn (SEG e.B e.C) := by apply Seg.target_lies_on
    exact Seg.collinear_of_lies_on h3 h4 h5
  exact ⟨this⟩

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends Setting1 Plane where
-- such that $AD = AE$.
  AD_eq_AE : (SEG A D).length = (SEG A E).length
-- and $\angle BAD = - \angle CAE$
  angle_BAD_eq_neg_angle_CAE : ∠ B A D = - ∠ C A E

-- Prove that $AB = AC$.
theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting2 Plane) : (SEG e.A e.B).length = (SEG e.A e.C).length := by
  haveI D_ne_B : PtNe e.D e.B := ⟨e.D_int_BC.2⟩
  haveI E_ne_C : PtNe e.E e.C := ⟨(Seg.lies_int_rev_iff_lies_int.mpr e.E_int_BC).2⟩
  have not_collinear_BAD : ¬ Collinear e.B e.A e.D := by sorry
  have not_collinear_CAE : ¬ Collinear e.C e.A e.E := by sorry
  have not_collinear_ADE : ¬ Collinear e.A e.D e.E := by sorry
  have isoceles_ADE : (TRI e.A e.D e.E).IsIsoceles := by
    calc
    (SEG e.E e.A).length = (SEG e.A e.E).length := by apply length_of_rev_eq_length'
    _= (SEG e.A e.D).length := e.AD_eq_AE.symm
  have angle_DAB_eq_neg_angle_EAC : ∠ e.D e.A e.B = - (∠ e.E e.A e.C) := by
    calc
    ∠ e.D e.A e.B = - (∠ e.B e.A e.D) := by apply Angle.neg_value_of_rev_ang
    _= ∠ e.C e.A e.E := by simp only [e.angle_BAD_eq_neg_angle_CAE, neg_neg]
    _= - (∠ e.E e.A e.C) := by apply Angle.neg_value_of_rev_ang
  have angle_BDA_eq_neg_angle_CEA : ∠ e.B e.D e.A = - (∠ e.C e.E e.A) := by
    calc
    (∠ e.B e.D e.A)
    _= ((∠ e.B e.D e.A) + (∠ e.A e.D e.E)) - (∠ e.A e.D e.E) := by abel
    _= (∠ e.B e.D e.E) - (∠ e.A e.D e.E) := by
      congr 1; exact ang_value_eq_ang_value_add_ang_value e.B e.A e.E e.D
    _= ↑ (π) - (∠ e.A e.D e.E) := by
      congr 1; exact Angle.value_eq_pi_of_lies_int_seg_nd e.D_int_BE
    _= ↑ (π) + (- ∠ e.A e.D e.E) := by abel
    _= ↑ (π) + (∠ e.E e.D e.A) := by
      congr 1; symm;
      apply Angle.neg_value_of_rev_ang
    _= ↑ (π) + (∠ e.A e.E e.D) := by
      congr 1;
      exact (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (TRI_nd e.A e.D e.E not_colinear_ADE)).mp isoceles_ADE
    _= (∠ e.D e.E e.C) + (∠ e.A e.E e.D) := by
      congr 1; symm; exact Angle.value_eq_pi_of_lies_int_seg_nd e.E_int_DC
    _= (∠ e.A e.E e.D) + (∠ e.D e.E e.C) := by abel
    _= (∠ e.A e.E e.C) := by exact ang_value_eq_ang_value_add_ang_value e.A e.D e.C e.E
    _= - (∠ e.C e.E e.A) := by apply Angle.neg_value_of_rev_ang
  have triangle_BAD_acongr_triangle_CAE : (TRI_nd e.B e.A e.D not_collinear_BAD) ≅ₐ (TRI_nd e.C e.A e.E not_collinear_CAE) := by
    apply TriangleND.acongr_of_ASA
    · exact angle_DAB_eq_neg_angle_EAC
    · exact e.AD_eq_AE
    · exact angle_BDA_eq_neg_angle_CEA
  calc
  (SEG e.A e.B).length
  _= (SEG e.B e.A).length := by apply length_of_rev_eq_length'
  _= (SEG e.C e.A).length := triangle_BAD_acongr_triangle_CAE.edge₃
  _= (SEG e.A e.C).length := by apply length_of_rev_eq_length'
end Problem_6

end EuclidGeom
