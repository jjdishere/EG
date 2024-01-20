import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

namespace Congruence_Exercise_ygr

namespace Problem_2
/-
Given $AB = DC$, $DB = AC$, $B,C$ is on the same side of line $AD$.
Prove that $∠B = ∠ C$.
-/
structure Setting1  (Plane : Type*) [EuclideanPlane Plane] where
  -- $AB = DC$, $DB = AC$.
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  h₁ : (SEG A B).length = (SEG D C).length
  h₂ : (SEG D B).length = (SEG A C).length
  -- nondegenerate
  hnd₁ : ¬ Collinear D B A
  hnd₂ : ¬ Collinear A C D
  D_ne_A : D ≠ A :=(ne_of_not_collinear hnd₁).2.1
  -- $B,C$ is on the same side of line $AD$.
  B_side : IsOnRightSide B (SEG_nd A D D_ne_A)
  C_side : IsOnRightSide C (SEG_nd A D D_ne_A)
lemma a_ne_b {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane}: e.A ≠ e.B := (ne_of_not_collinear e.hnd₁).1
lemma a_ne_c {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane}: e.A ≠ e.C := (ne_of_not_collinear e.hnd₂).2.2.symm
lemma b_ne_d {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane}: e.B ≠ e.D :=  (ne_of_not_collinear e.hnd₁).2.2
lemma c_ne_d {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane}: e.C ≠ e.D :=(ne_of_not_collinear e.hnd₂).1.symm
-- Prove that $∠B = ∠ C$.
theorem Result {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane}:  ∠ e.A e.B e.D a_ne_b b_ne_d.symm = -∠ e.D e.C e.A c_ne_d.symm a_ne_c := by
  -- Use SSS to prove that $\triangle DBA \congr \triangle ACD$ or $\triangle DBA \congr_a \triangle ACD$.
  have h : (TRI_nd e.D e.B e.A e.hnd₁) ≅ₐ (TRI_nd e.A e.C e.D e.hnd₂) := by
    apply TriangleND.acongr_of_SSS_of_ne_orientation
    · calc
        _ = (SEG e.A e.B).length := length_of_rev_eq_length'
        _ = (SEG e.D e.C).length := e.h₁
        _ = _ := length_of_rev_eq_length'
    · exact length_of_rev_eq_length'
    · exact e.h₂
    · have clock : ¬ (TRI_nd e.D e.B e.A e.hnd₁).is_cclock := by
        have : (IsOnLeftSide e.B (SEG_nd e.A e.D e.D_ne_A)) ↔ (TRI_nd e.D e.B e.A e.hnd₁).is_cclock := by
          simp [TriangleND.iscclock_iff_liesonleft₂]
          rfl
        apply this.not.mp
        unfold IsOnLeftSide
        have hb : odist e.B (SEG_nd e.A e.D e.D_ne_A) < 0 := by exact e.B_side
        linarith
      have cclock : (TRI_nd e.A e.C e.D e.hnd₂).is_cclock := by
        have : (IsOnLeftSide e.C (SEG_nd e.D e.A e.D_ne_A.symm)) ↔ (TRI_nd e.A e.C e.D e.hnd₂).is_cclock := by
          simp [TriangleND.iscclock_iff_liesonleft₂]
          rfl
        apply this.mp
        have rev : odist e.C (SEG_nd e.D e.A e.D_ne_A.symm) = - odist e.C (SEG_nd e.A e.D e.D_ne_A) := by
          have : (SEG_nd e.D e.A e.D_ne_A.symm) = (SEG_nd e.A e.D e.D_ne_A).reverse := by rfl
          simp only [this]
          apply odist_reverse_eq_neg_odist (df := (SEG_nd e.A e.D e.D_ne_A))
        unfold IsOnLeftSide
        simp only [rev, Left.neg_pos_iff, gt_iff_lt]
        exact e.C_side
      simp only [clock, cclock, not_true_eq_false]
  · exact h.angle₂



end Problem_2
end Congruence_Exercise_ygr
