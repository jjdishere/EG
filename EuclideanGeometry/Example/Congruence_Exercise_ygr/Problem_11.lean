import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Linear.Order

noncomputable section

namespace EuclidGeom

namespace Problem_11

/-
Let $l$ be a directed line on the plane.
Let $B, E, C, F$ be four points on $l$ in this order.
Let $A, D$ be two points on the plane such that they lies on the same side of $l$.
If $AB = DF$, $AC = DE$ and $BE = CF$, prove that $\angle BAC = - \angle FDE$.
-/

structure Setting (Plane : Type _) [EuclideanPlane Plane] where
-- Let $l$ be a directed line on the plane
  l : DirLine Plane
-- Let $B, E, C, F$ be four points on $l$ in this order.
  B : Plane
  E : Plane
  C : Plane
  F : Plane
  B_on_l : B LiesOn l
  E_on_l : E LiesOn l
  C_on_l : C LiesOn l
  F_on_l : F LiesOn l
  B_lt_E_on_l : (⟨B, B_on_l⟩ : l.carrier.Elem) < ⟨E, E_on_l⟩
  E_lt_C_on_l : (⟨E, E_on_l⟩ : l.carrier.Elem) < ⟨C, C_on_l⟩
  C_lt_F_on_l : (⟨C, C_on_l⟩ : l.carrier.Elem) < ⟨F, F_on_l⟩
-- Let $A, D$ be two points on the plane,
  A : Plane
  D : Plane
-- such that they lies on different sides of $l$,
  A_D_IsOnSameSide_l : IsOnSameSide A D l
-- $AB = DF$,
  AB_eq_DF : (SEG A B).length = (SEG D F).length
-- $AC = DE$,
  AC_eq_DE : (SEG A C).length = (SEG D E).length
-- $BE = CF$.
  BE_eq_CF : (SEG B E).length = (SEG C F).length
lemma B_ne_C' {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : e.B ≠ e.C := by
  apply (DirLine.ne_iff_ne_as_line_elem e.B_on_l e.C_on_l).mpr; apply ne_of_lt;
  calc
  (⟨e.B, e.B_on_l⟩ : e.l.carrier.Elem)
  _< ⟨e.E, e.E_on_l⟩ := e.B_lt_E_on_l
  _< ⟨e.C, e.C_on_l⟩ := e.E_lt_C_on_l
instance B_ne_C {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : PtNe e.B e.C := ⟨B_ne_C'⟩
lemma E_ne_F' {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : e.E ≠ e.F := by
  apply (DirLine.ne_iff_ne_as_line_elem e.E_on_l e.F_on_l).mpr; apply ne_of_lt;
  calc
  (⟨e.E, e.E_on_l⟩ : e.l.carrier.Elem)
  _< ⟨e.C, e.C_on_l⟩ := e.E_lt_C_on_l
  _< ⟨e.F, e.F_on_l⟩ := e.C_lt_F_on_l
instance E_ne_F {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : PtNe e.E e.F := ⟨E_ne_F'⟩
lemma not_collinear_ACB {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : ¬ Collinear e.A e.C e.B := by sorry
lemma not_collinear_DEF {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : ¬ Collinear e.D e.E e.F := by sorry
instance B_ne_A {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : PtNe e.B e.A := ⟨(ne_of_not_collinear not_collinear_ACB).2.1.symm⟩
instance C_ne_A {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : PtNe e.C e.A := ⟨(ne_of_not_collinear not_collinear_ACB).2.2⟩
instance F_ne_D {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : PtNe e.F e.D := ⟨(ne_of_not_collinear not_collinear_DEF).2.1.symm⟩
instance E_ne_D {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : PtNe e.E e.D := ⟨(ne_of_not_collinear not_collinear_DEF).2.2⟩

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends Setting Plane where
  not_colinear_ACB : ¬ Collinear A C B := not_collinear_ACB
  not_colinear_DEF : ¬ Collinear D E F := not_collinear_DEF

-- Prove that $\angle BAC = - \angle FDE$.
theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting2 Plane) : (∠ e.B e.A e.C) = - (∠ e.F e.D e.E) := by
  have E_int_BC : e.E LiesInt (SEG e.B e.C) := by
    apply DirLine.lies_int_seg_of_lt_and_lt e.B_on_l e.E_on_l e.C_on_l
    exact e.B_lt_E_on_l; exact e.E_lt_C_on_l
  have C_int_EF : e.C LiesInt (SEG e.E e.F) := by
    apply DirLine.lies_int_seg_of_lt_and_lt e.E_on_l e.C_on_l e.F_on_l
    exact e.E_lt_C_on_l; exact e.C_lt_F_on_l
  have CB_eq_EF : (SEG e.C e.B).length = (SEG e.E e.F).length := by
    calc
    _= (SEG e.B e.C).length := by apply length_of_rev_eq_length'
    _= (SEG e.B e.E).length + (SEG e.E e.C).length := by
      apply length_eq_length_add_length
      apply Seg.lies_on_of_lies_int
      exact E_int_BC
    _= (SEG e.E e.C).length + (SEG e.C e.F).length := by simp only [e.BE_eq_CF]; ring
    _= _ := by
      symm;
      apply length_eq_length_add_length
      apply Seg.lies_on_of_lies_int
      exact C_int_EF
  have BA_eq_FD : (SEG e.B e.A).length = (SEG e.F e.D).length := by
    calc
    _= (SEG e.A e.B).length := by apply length_of_rev_eq_length'
    _= (SEG e.D e.F).length := e.AB_eq_DF
    _=_ := by apply length_of_rev_eq_length'
  have clockwise_ACB_eq_neg_clockwise_DEF : (TRI_nd e.A e.C e.B e.not_colinear_ACB).is_cclock = ¬(TRI_nd e.D e.E e.F e.not_colinear_DEF).is_cclock := by sorry
  have triangle_ACB_acongr_triangle_DEF : (TRI_nd e.A e.C e.B e.not_colinear_ACB) ≅ₐ (TRI_nd e.D e.E e.F e.not_colinear_DEF) := by
    apply TriangleND.acongr_of_SSS_of_ne_orientation
    · exact CB_eq_EF
    · exact BA_eq_FD
    · exact e.AC_eq_DE
    · exact clockwise_ACB_eq_neg_clockwise_DEF

end Problem_11

end EuclidGeom
