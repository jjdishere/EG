import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Linear.Line_trash

noncomputable section

namespace EuclidGeom

namespace Problem_5

/-
Let $l$ be a directed line on the plane.
Let $A, F, C, D$ be four points on $l$ in this order.
Let $B, E$ be two points on the plane such that they lies on different sides of $l$, and that $BC \parallel EF$.
If $\angle BAC = - \angle EDF$ and $AF = DC$, prove that $AB = DE$.
-/

structure Setting1 (Plane : Type _) [EuclideanPlane Plane] where
-- Let $l$ be a directed line on the plane
  l : DirLine Plane
-- Let $A, F, C, D$ be four points on $l$ in this order.
  A : Plane
  F : Plane
  C : Plane
  D : Plane
  A_on_l : A LiesOn l
  F_on_l : F LiesOn l
  C_on_l : C LiesOn l
  D_on_l : D LiesOn l
  A_lt_F_on_l : (⟨A, A_on_l⟩ : l.carrier.Elem) < ⟨F, F_on_l⟩
  F_lt_C_on_l : (⟨F, F_on_l⟩ : l.carrier.Elem) < ⟨C, C_on_l⟩
  C_lt_D_on_l : (⟨C, C_on_l⟩ : l.carrier.Elem) < ⟨D, D_on_l⟩
-- Let $B, E$ be two points on the plane,
  B : Plane
  E : Plane
-- such that they lies on different sides of $l$,
  B_E_IsOnOppositeSide_l : IsOnOppositeSide B E l

-- Claim : $A \ne C$.
lemma A_ne_C' {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : e.A ≠ e.C := by
  apply (DirLine.ne_iff_ne_as_line_elem e.A_on_l e.C_on_l).mpr; apply ne_of_lt;
  calc
  (⟨e.A, e.A_on_l⟩ : e.l.carrier.Elem)
  _< ⟨e.F, e.F_on_l⟩ := e.A_lt_F_on_l
  _< ⟨e.C, e.C_on_l⟩ := e.F_lt_C_on_l
instance A_ne_C {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.A e.C := ⟨A_ne_C'⟩
-- Claim : $D \ne F$.
lemma D_ne_F' {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : e.D ≠ e.F := by
  symm; apply (DirLine.ne_iff_ne_as_line_elem e.F_on_l e.D_on_l).mpr; apply ne_of_lt;
  calc
  (⟨e.F, e.F_on_l⟩ : e.l.carrier.Elem)
  _< ⟨e.C, e.C_on_l⟩ := e.F_lt_C_on_l
  _< ⟨e.D, e.D_on_l⟩ := e.C_lt_D_on_l
instance D_ne_F {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.D e.F := ⟨D_ne_F'⟩
lemma not_colinear_BCA {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : ¬ colinear e.B e.C e.A := by
  have h : IsOnOppositeSide e.B e.E (RAY e.C e.A) := by sorry
  have h1 : ¬ colinear e.C e.A e.B := (not_colinear_of_IsOnOppositeSide e.C e.A e.B e.E h).1
  sorry
lemma not_colinear_EFD {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : ¬ colinear e.E e.F e.D := by sorry
-- Claim : $C \ne B$.
instance C_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.C e.B := ⟨(ne_of_not_colinear not_colinear_BCA).2.2⟩
-- Claim : $A \ne B$.
instance A_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.A e.B := ⟨(ne_of_not_colinear not_colinear_BCA).2.1.symm⟩
-- Claim : $E \ne F$.
instance E_ne_F {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.E e.F := ⟨(ne_of_not_colinear not_colinear_EFD).2.2.symm⟩
-- Claim : $E \ne D$.
instance E_ne_D {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.E e.D := ⟨(ne_of_not_colinear not_colinear_EFD).2.1⟩

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends Setting1 Plane where
  not_colinear_BCA : ¬ colinear B C A := not_colinear_BCA
  not_colinear_EFD : ¬ colinear E F D := not_colinear_EFD
-- and that $BC \parallel EF$,
  BC_parallel_EF : (LIN B C) ∥ (LIN E F)
-- If $\angle BAC = - \angle EDF$,
  angle_BAC_eq_neg_angle_EDF : (∠ B A C) = - (∠ E D F)
-- and $AF = DC$,
  AF_eq_DC : (SEG A F).length = (SEG D C).length
-- Prove that $AB = DE$.

theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting2 Plane) : (SEG e.A e.B).length = (SEG e.D e.E).length := by
  have F_int_AC : e.F LiesInt (SEG e.A e.C) := by sorry
  have C_int_DF : e.C LiesInt (SEG e.D e.F) := by sorry
  have AC_eq_DF : (SEG e.A e.C).length = (SEG e.D e.F).length := by
    calc
    (SEG e.A e.C).length
    _= (SEG e.A e.F).length + (SEG e.F e.C).length := by
      apply length_eq_length_add_length
      apply Seg.lies_on_of_lies_int
      exact F_int_AC
    _= (SEG e.D e.C).length + (SEG e.C e.F).length := by congr 1; exact e.AF_eq_DC; exact length_of_rev_eq_length'
    _= (SEG e.D e.F).length := by
      symm; apply length_eq_length_add_length
      apply Seg.lies_on_of_lies_int
      exact C_int_DF
  have angle_BCA_eq_neg_angle_EFD : (∠ e.B e.C e.A) = - (∠ e.E e.F e.D) := by sorry
-- ``to be rewritten``
  have triangle_BCA_acongr_triangle_EFD : (TRI_nd e.B e.C e.A e.not_colinear_BCA) ≅ₐ (TRI_nd e.E e.F e.D e.not_colinear_EFD) := by sorry
  exact triangle_BCA_acongr_triangle_EFD.edge₂
end Problem_5

end EuclidGeom
