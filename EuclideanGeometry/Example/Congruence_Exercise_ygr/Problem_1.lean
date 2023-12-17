import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Congruence_Exercise_ygr

namespace Problem_1
/-
$C, D$ lies in segment $BF$, $AB ∥ DE$, $AB = DF$, $BC = DE$.

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
lemma D_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: e.D ≠ e.B := sorry

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends Setting1 Plane where
  -- $AB ∥ DE$
  hpr : (SEG_nd B A A_ne_B) ∥ (SEG_nd D E D_ne_E.symm)

-- Prove that $∠ BAC = ∠ EFD$.
theorem Result {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane} : ∠ e.B e.A e.C A_ne_B.symm A_ne_C.symm = ∠ e.E e.F e.D E_ne_F D_ne_F := by
  -- $CB = BC = DE = ED$.
  have e₂ : (SEG e.C e.B).length = (SEG e.E e.D).length := by
    simp only [length_of_rev_eq_length', e.h₂, length_of_rev_eq_length']
  have a₁ : ∠ e.A e.B e.C (A_ne_B) (B_ne_C.symm) = -∠ e.F e.D e.E (D_ne_F.symm) (D_ne_E.symm) := by
    -- $∠ ABC$ and $∠ EDF$ are corresponding angles.
    have hCrsp : IsCorrespondingAng (ANG e.A e.B e.C A_ne_B B_ne_C.symm) (ANG e.E e.D e.F D_ne_E.symm D_ne_F.symm) := by
      constructor
      · show (RAY e.B e.A A_ne_B).toDir = (RAY e.D e.E D_ne_E.symm).toDir
        apply eq_toDir_of_parallel_and_same_side
        ·exact e.hpr
        ·show odist_sign e.A (SEG_nd e.B e.D D_ne_B) = odist_sign e.E (SEG_nd e.B e.D D_ne_B)
         sorry
        ·exact D_ne_B.symm
        --·exact A_ne_B
        --·exact D_ne_E.symm
      · show (RAY e.B e.C B_ne_C.symm).toDirLine = (RAY e.D e.F D_ne_F.symm).toDirLine
        have line₁: (RAY e.B e.C B_ne_C.symm).toDirLine = (RAY e.B e.F e.B_ne_F.symm).toDirLine := by
          symm
          sorry
        have line₂: (RAY e.B e.F e.B_ne_F.symm).toDirLine = (RAY e.D e.F D_ne_F.symm).toDirLine := by sorry
        rw [line₁,line₂]
    -- Then $∠ ABC = ∠ EDF = -∠ FDE$.
    calc
      _ = ∠ e.E e.D e.F (D_ne_E.symm) (D_ne_F.symm) := eq_value_of_iscorrespondingang hCrsp
      _ = _ := by apply neg_value_of_rev_ang (D_ne_E.symm) (D_ne_F.symm)
  have e₃ : (SEG e.B e.A).length = (SEG e.D e.F).length := by
    rw [length_of_rev_eq_length']
    exact e.h₁
  -- Use SAS to prove $▵ BAC ≅ ▵ DFE$.
  have h :  (TRI_nd e.B e.A e.C hnd₁) ≅ₐ (TRI_nd e.D e.F e.E hnd₂) := by
    apply TriangleND.acongr_of_SAS
    · exact e₂
    · exact a₁
    · exact e₃
  -- $∠ BAC = -∠ CAB = - -∠ EFD = ∠ EFD$.
  calc
    _ = - ∠ e.C e.A e.B A_ne_C.symm A_ne_B.symm := by apply neg_value_of_rev_ang
    _ = ∠ e.E e.F e.D E_ne_F D_ne_F := by
      have : ∠ e.C e.A e.B A_ne_C.symm A_ne_B.symm = - ∠ e.E e.F e.D E_ne_F D_ne_F := h.angle₂
      rw [this, neg_neg]
end Problem_1
end Congruence_Exercise_ygr
