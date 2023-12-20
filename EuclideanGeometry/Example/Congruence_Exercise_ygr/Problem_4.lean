import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

namespace Congruence_Exercise_ygr

namespace Problem_4

structure Setting1  (Plane : Type _) [EuclideanPlane Plane] where
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  hnd₁ : ¬ colinear B C A
  hnd₂ : ¬ colinear B C D
  BD_eq_BC : (SEG B D).length = (SEG B C).length
lemma B_ne_C {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : e.B ≠ e.C := (ne_of_not_colinear e.hnd₁).2.2.symm
lemma D_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : e.D ≠ e.B := (ne_of_not_colinear e.hnd₂).2.1.symm
lemma A_ne_C {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : e.A ≠ e.C := (ne_of_not_colinear e.hnd₁).1

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends Setting1 Plane where

  BD_para_CA : (SEG_nd B D D_ne_B) ∥ (SEG_nd C A A_ne_C)
  A_side : IsOnLeftSide A (SEG_nd B C B_ne_C.symm)
  D_side : IsOnRightSide D (SEG_nd B C B_ne_C.symm)
  E : Plane
  E_int : E LiesInt (SEG_nd B C B_ne_C.symm)
  E_position : (SEG B E).length = (SEG A C).length

lemma E_ne_D {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane} : e.E ≠ e.D := by sorry
lemma A_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane} : e.A ≠ e.B := (ne_of_not_colinear e.hnd₁).2.1.symm
lemma B_ne_E {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane} : e.B ≠ e.E := by sorry
theorem Result {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane} : ∠ e.B e.D e.E D_ne_B.symm E_ne_D = -∠ e.C e.B e.A B_ne_C.symm A_ne_B := by
  have hnd₃ : ¬ colinear e.B e.E e.D := by sorry
  have hnd₁' : ¬ colinear e.C e.A e.B := by
    apply perm_colinear_trd_fst_snd.mt
    exact e.hnd₁
  have e₂ : (SEG e.D e.B).length = (SEG e.B e.C).length := by
    calc
      _=(SEG e.B e.D).length := by apply length_of_rev_eq_length'
      _=_ := e.BD_eq_BC
  have a₁ : ∠ e.E e.B e.D B_ne_E.symm D_ne_B = -∠ e.A e.C e.B A_ne_C B_ne_C := by
    have hAltint : IsAlternateIntAng (ANG e.D e.B e.E D_ne_B B_ne_E.symm) (ANG e.A e.C e.B A_ne_C B_ne_C) := by
      constructor
      · show (RAY e.B e.D D_ne_B).toDir = -(RAY e.C e.A A_ne_C).toDir
        --use neg_toDir_of_parallel_and_opposite_side
        sorry
      · show (RAY e.B e.E B_ne_E.symm).toDirLine = (RAY e.C e.B B_ne_C).toDirLine.reverse
        have coer₁ : (RAY e.B e.E B_ne_E.symm).toDirLine = (SEG_nd e.B e.E B_ne_E.symm).toDirLine := by
          symm
          apply SegND.toDirLine_eq_toray_toLine
        have coer₂ : (RAY e.C e.B B_ne_C).toDirLine.reverse = (SEG_nd e.C e.B B_ne_C).toDirLine.reverse := by
          have coer₂' : (RAY e.C e.B B_ne_C).toDirLine = (SEG_nd e.C e.B B_ne_C).toDirLine := by
            symm
            apply SegND.toDirLine_eq_toray_toLine
          congr
        have coer₃ : (SEG_nd e.C e.B B_ne_C).toDirLine.reverse = (SEG_nd e.B e.C B_ne_C.symm).toDirLine := by
          apply SegND.toDirLine_rev_eq_rev_toLine
        simp only[coer₁,coer₂,coer₃]
        apply eq_toDirLine_of_source_to_pt_lies_int (e.E_int)
    calc
      _=-∠ e.D e.B e.E D_ne_B B_ne_E.symm := by apply neg_value_of_rev_ang (B_ne_E.symm) (D_ne_B)
      _=-∠ e.A e.C e.B A_ne_C B_ne_C := by
        have neg : ∠ e.D e.B e.E D_ne_B B_ne_E.symm = ∠ e.A e.C e.B A_ne_C B_ne_C := eq_value_of_isalternateintang (hAltint)
        simp only [neg]
  have e₃ : (SEG e.B e.E).length = (SEG e.C e.A).length := by
    calc
      _=(SEG e.A e.C).length := by exact e.E_position
      _=_ := by simp only [length_of_rev_eq_length']
  have h : (TRI_nd e.B e.E e.D hnd₃) ≅ₐ (TRI_nd e.C e.A e.B hnd₁') := by
    apply TriangleND.acongr_of_SAS
    · exact e₂
    · exact a₁
    · exact e₃
  exact h.angle₃
end Problem_4
end Congruence_Exercise_ygr
