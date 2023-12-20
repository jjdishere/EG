import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

namespace Congruence_Exercise_ygr

namespace Problem_1
/-
$C, D$ lies in segment $BF$, $AB \parallel DE$, $AB = DF$, $BC = DE$.

Prove that $∠ BAC = ∠ EFD$.
-/
structure Setting1  (Plane : Type _) [EuclideanPlane Plane] where
  -- $C, D$ lies in segment $BF$, they lies on the same line $l$.
  B : Plane
  C : Plane
  D : Plane
  F : Plane
  B_ne_F : B ≠ F
  C_int : C LiesInt (SEG_nd B F B_ne_F.symm)
  D_int : D LiesInt (SEG_nd B F B_ne_F.symm)
  -- $A, E$ do not lie on $l$.
  A : Plane
  E : Plane
  ABC_nd : ¬colinear A B C
  EDF_nd : ¬colinear E D F
  -- need A and E be at the same side of l!!
  A_side : IsOnLeftSide A (SEG_nd B F B_ne_F.symm)
  E_side : IsOnLeftSide E (SEG_nd B F B_ne_F.symm)
  -- $AB = DF$
  h₁ : (SEG A B).length = (SEG D F).length
  -- $BC = DE$
  h₂ : (SEG B C).length = (SEG D E).length
lemma hnd₁ {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: ¬ colinear e.B e.A e.C := by
  apply flip_colinear_fst_snd.mt
  exact e.ABC_nd
lemma hnd₂ {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: ¬ colinear e.D e.F e.E := by
  apply perm_colinear_trd_fst_snd.mt
  exact e.EDF_nd
lemma A_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: e.A ≠ e.B := (ne_of_not_colinear hnd₁).2.2
lemma D_ne_E {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: e.D ≠ e.E := (ne_of_not_colinear hnd₂).2.1
lemma A_ne_C {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: e.A ≠ e.C := (ne_of_not_colinear hnd₁).1.symm
lemma E_ne_F {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: e.E ≠ e.F := (ne_of_not_colinear hnd₂).1
lemma D_ne_F {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: e.D ≠ e.F := (ne_of_not_colinear hnd₂).2.2.symm
lemma B_ne_C {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: e.B ≠ e.C := (ne_of_not_colinear hnd₁).2.1
lemma D_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: e.D ≠ e.B := (ne_vertex_of_lies_int_seg_nd e.D_int).1

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends Setting1 Plane where
  -- $AB ∥ DE$
  hpr : (SEG_nd B A A_ne_B) ∥ (SEG_nd D E D_ne_E.symm)

-- Prove that $∠ BAC = ∠ EFD$.
theorem Result {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane} : ∠ e.B e.A e.C A_ne_B.symm A_ne_C.symm = ∠ e.E e.F e.D E_ne_F D_ne_F := by
  /-
  $\angle ABC$ and $\angle EDF$ are corresponding angles,thus equal.
  In $\triangle BAC \congr_a \triangle DFE$.
  $\cdot CB = ED$
  $\cdot \angle ABC = -\angle FDE$
  $\cdot BA = DF$
  We have $\triangle BAC \congr_a \triangle DFE$.
  Thus $\angle CAB = -\angle EFD$
  By anti-symm we proven.
  -/
  -- $CB = BC = DE = ED$.
  have e₂ : (SEG e.C e.B).length = (SEG e.E e.D).length := by
    simp only [length_of_rev_eq_length', e.h₂, length_of_rev_eq_length']
  --$\angle ABC$ = -$\angle FDE$
  have a₁ : ∠ e.A e.B e.C (A_ne_B) (B_ne_C.symm) = -∠ e.F e.D e.E (D_ne_F.symm) (D_ne_E.symm) := by
    -- $\angle ABC$ and $\angle EDF$ are corresponding angles.
    have hCrsp : IsCorrespondingAng (ANG e.A e.B e.C A_ne_B B_ne_C.symm) (ANG e.E e.D e.F D_ne_E.symm D_ne_F.symm) := by
      constructor
      --same Dir for start ray and same DirLine for end ray
      · show (RAY e.B e.A A_ne_B).toDir = (RAY e.D e.E D_ne_E.symm).toDir
        --by $A,E$ are on the same side of line $B F$ and $AB \parallel DE$
        apply eq_toDir_of_parallel_and_same_side
        ·exact e.hpr
        ·show odist_sign e.A (SEG_nd e.B e.D D_ne_B) = odist_sign e.E (SEG_nd e.B e.D D_ne_B)
         unfold odist_sign
         have hA : odist e.A (SEG_nd e.B e.D D_ne_B) > 0 := by sorry
         have hE : odist e.E (SEG_nd e.B e.D D_ne_B) > 0 := by sorry
         simp [hA,hE]
        ·exact D_ne_B.symm
      · show (RAY e.B e.C B_ne_C.symm).toDirLine = (RAY e.D e.F D_ne_F.symm).toDirLine
        --by $B C D F$ colinear
        have line₁: (RAY e.B e.C B_ne_C.symm).toDirLine = (RAY e.B e.F e.B_ne_F.symm).toDirLine := by
          have coer₁₁ : (RAY e.B e.C B_ne_C.symm).toDirLine = (SEG_nd e.B e.C B_ne_C.symm).toDirLine := by
            symm
            apply SegND.toDirLine_eq_toRay_toDirLine
          have coer₁₂ : (RAY e.B e.F e.B_ne_F.symm).toDirLine = (SEG_nd e.B e.F e.B_ne_F.symm).toDirLine := by
            symm
            apply SegND.toDirLine_eq_toRay_toDirLine
          rw [coer₁₁ , coer₁₂]
          apply eq_toDirLine_of_source_to_pt_lies_int (e.C_int)
        have line₂: (RAY e.B e.F e.B_ne_F.symm).toDirLine = (RAY e.D e.F D_ne_F.symm).toDirLine := by
          symm
          have coer₂₁ : (RAY e.D e.F D_ne_F.symm).toDirLine = (SEG_nd e.D e.F D_ne_F.symm).toDirLine := by
            symm
            apply SegND.toDirLine_eq_toRay_toDirLine
          have coer₂₂ : (RAY e.B e.F e.B_ne_F.symm).toDirLine = (SEG_nd e.B e.F e.B_ne_F.symm).toDirLine := by
            symm
            apply SegND.toDirLine_eq_toRay_toDirLine
          rw [coer₂₂ , coer₂₁]
          apply eq_toDirLine_of_pt_lies_int_to_target (e.D_int)
        rw [line₁,line₂]
    -- Then $∠ ABC = ∠ EDF = -∠ FDE$.
    calc
      _ = ∠ e.E e.D e.F (D_ne_E.symm) (D_ne_F.symm) := eq_value_of_iscorrespondingang hCrsp --corresponding angle
      _ = _ := by apply neg_value_of_rev_ang (D_ne_E.symm) (D_ne_F.symm) --anti-symm
  --$BA = DF$
  have e₃ : (SEG e.B e.A).length = (SEG e.D e.F).length := by
    rw [length_of_rev_eq_length']
    exact e.h₁
  -- We have $\triangle BAC \congr_a \triangle DFE$.
  have h :  (TRI_nd e.B e.A e.C hnd₁) ≅ₐ (TRI_nd e.D e.F e.E hnd₂) := by
    apply TriangleND.acongr_of_SAS
    · exact e₂
    · exact a₁
    · exact e₃
  calc
    _ = - ∠ e.C e.A e.B A_ne_C.symm A_ne_B.symm := by apply neg_value_of_rev_ang
    _ = ∠ e.E e.F e.D E_ne_F D_ne_F := by
      have : ∠ e.C e.A e.B A_ne_C.symm A_ne_B.symm = - ∠ e.E e.F e.D E_ne_F D_ne_F := h.angle₂
      rw [this, neg_neg]
end Problem_1
end Congruence_Exercise_ygr
