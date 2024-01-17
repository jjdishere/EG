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
  B_ne_F : PtNe B F
  C_int : C LiesInt (SEG_nd B F)
  D_int : D LiesInt (SEG_nd B F)
  -- $A, E$ do not lie on $l$.
  A : Plane
  E : Plane
  ABC_nd : ¬collinear A B C
  EDF_nd : ¬collinear E D F
  -- need A and E be at the same side of l!!
  A_side : IsOnLeftSide A (SEG_nd B F)
  E_side : IsOnLeftSide E (SEG_nd B F)
  -- $AB = DF$
  h₁ : (SEG A B).length = (SEG D F).length
  -- $BC = DE$
  h₂ : (SEG B C).length = (SEG D E).length
attribute [instance] Setting1.B_ne_F
lemma hnd₁ {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: ¬ collinear e.B e.A e.C := by
  apply flip_collinear_fst_snd.mt
  exact e.ABC_nd
lemma hnd₂ {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: ¬ collinear e.D e.F e.E := by
  apply perm_collinear_trd_fst_snd.mt
  exact e.EDF_nd
instance A_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: PtNe e.A e.B := ⟨(ne_of_not_collinear hnd₁).2.2⟩
instance D_ne_E {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: PtNe e.D e.E := ⟨(ne_of_not_collinear hnd₂).2.1⟩
instance A_ne_C {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: PtNe e.A e.C := ⟨(ne_of_not_collinear hnd₁).1.symm⟩
instance E_ne_F {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: PtNe e.E e.F := ⟨(ne_of_not_collinear hnd₂).1⟩
instance D_ne_F {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: PtNe e.D e.F := ⟨(ne_of_not_collinear hnd₂).2.2.symm⟩
instance B_ne_C {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: PtNe e.B e.C := ⟨(ne_of_not_collinear hnd₁).2.1⟩
instance D_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: PtNe e.D e.B := ⟨(ne_vertex_of_lies_int_seg_nd e.D_int).1⟩

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends Setting1 Plane where
  -- $AB ∥ DE$
  hpr : (SEG_nd B A) ∥ (SEG_nd D E)

-- Prove that $∠ BAC = ∠ EFD$.
theorem Result {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane} : ∠ e.B e.A e.C = ∠ e.E e.F e.D := by
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
  have a₁ : ∠ e.A e.B e.C  = -∠ e.F e.D e.E := by
    -- $\angle ABC$ and $\angle EDF$ are corresponding angles.
    have hCrsp : IsCorrespondingAng (ANG e.A e.B e.C) (ANG e.E e.D e.F) := by
      constructor
      --same Dir for start ray and same DirLine for end ray
      · show (RAY e.B e.A).toDir = (RAY e.D e.E).toDir
        --by $A,E$ are on the same side of line $B F$ and $AB \parallel DE$
        apply eq_toDir_of_parallel_and_same_side
        ·exact e.hpr
        ·show IsOnSameSide e.A e.E (SEG_nd e.B e.D)
         have hA : odist e.A (SEG_nd e.B e.D) > 0 := by
          calc
            odist e.A (SEG_nd e.B e.D) = odist e.A (SEG_nd e.B e.D).toDirLine := by rfl
            _=odist e.A (SEG_nd e.B e.F).toDirLine := by
              have : (SEG_nd e.B e.D).toDirLine = (SEG_nd e.B e.F).toDirLine := by
                apply SegND.mk_source_pt_toDirLine_eq_of_lies_int (e.D_int)
              congr
            _=odist e.A (SEG_nd e.B e.F) := by rfl
            _>0 := by exact e.A_side
         have hE : odist e.E (SEG_nd e.B e.D) > 0 := by
          calc
            odist e.E (SEG_nd e.B e.D) = odist e.E (SEG_nd e.B e.D).toDirLine := by rfl
            _=odist e.E (SEG_nd e.B e.F).toDirLine := by
              have : (SEG_nd e.B e.D).toDirLine = (SEG_nd e.B e.F).toDirLine := by
                apply SegND.mk_source_pt_toDirLine_eq_of_lies_int (e.D_int)
              congr
            _=odist e.E (SEG_nd e.B e.F) := by rfl
            _>0 := by exact e.E_side
         have hA' : e.A LiesOnLeft (SEG_nd e.B e.D) := by exact hA
         have hE' : e.E LiesOnLeft (SEG_nd e.B e.D) := by exact hE
         unfold IsOnSameSide
         unfold IsOnSameSide'
         show e.A LiesOnLeft (SEG_nd e.B e.D) ∧ e.E LiesOnLeft (SEG_nd e.B e.D) ∨ e.A LiesOnRight (SEG_nd e.B e.D) ∧ e.E LiesOnRight (SEG_nd e.B e.D)
         simp only [hA', hE', and_self, true_or]
        ·exact D_ne_B.out.symm
      · show (RAY e.B e.C).toDirLine = (RAY e.D e.F).toDirLine
        calc
          _=(SEG_nd e.B e.F).toDirLine := by
            apply SegND.mk_source_pt_toDirLine_eq_of_lies_int (e.C_int)
          _=(SEG_nd e.D e.F).toDirLine := by
            symm
            apply SegND.mk_pt_target_toDirLine_eq_of_lies_int (e.D_int)
    -- Then $∠ ABC = ∠ EDF = -∠ FDE$.
    calc
      _ = ∠ e.E e.D e.F := eq_value_of_iscorrespondingang hCrsp --corresponding angle
      _ = _ := by apply neg_value_of_rev_ang --anti-symm
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
    _ = - ∠ e.C e.A e.B := by apply neg_value_of_rev_ang
    _ = ∠ e.E e.F e.D  := by
      have : ∠ e.C e.A e.B  = - ∠ e.E e.F e.D := h.angle₂
      rw [this, neg_neg]
end Problem_1
end Congruence_Exercise_ygr
