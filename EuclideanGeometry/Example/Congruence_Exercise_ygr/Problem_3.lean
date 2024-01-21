import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

namespace Congruence_Exercise_ygr

namespace Problem_3

/-
In (convex) quadrilateral $A B D C$,$AB = AC$, $BD = CD$.
Prove that $\angle A B D = -\angle A C D$
-/
structure Setting  (Plane : Type*) [EuclideanPlane Plane] where
  --In (convex) quadrilateral $A B D C$,$AB = AC$, $BD = CD$.
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  cvx_ABDC : (QDR A B D C).IsConvex
  AB_eq_AC : (SEG A B).length = (SEG A C).length
  BD_eq_CD : (SEG B D).length = (SEG C D).length
  --$A \ne B$ and $D \ne B$ for $\angle A B D$
  A_ne_B : A ≠ B := (Quadrilateral_cvx.nd₁₂ (QDR_cvx A B D C cvx_ABDC)).symm
  D_ne_B : D ≠ B := (Quadrilateral_cvx.nd₂₃ (QDR_cvx A B D C cvx_ABDC))
  --$A \ne C$ and $D \ne B$ for $\angle A C D$
  A_ne_C : A ≠ C := (Quadrilateral_cvx.nd₁₄ (QDR_cvx A B D C cvx_ABDC)).symm
  D_ne_C : D ≠ C := (Quadrilateral_cvx.nd₃₄ (QDR_cvx A B D C cvx_ABDC)).symm
theorem Result {Plane : Type*} [EuclideanPlane Plane] (e : Setting Plane) : ∠  e.A e.B e.D (e.A_ne_B) (e.D_ne_B) = - ∠ e.A e.C e.D (e.A_ne_C) (e.D_ne_C):= by
  /-
  Because $AB = AC$ ,we have $\angle A B C = -\angle A C B$.
  Because $DB = DC$ ,we have $\angle D B C = -\angle D C B$
  $\angle A B D = \angle A B C - \angle D B C = \angle D C B - \angle A C B = --\angle A C D$
  -/
  have h₁ : ¬ Collinear e.A e.B e.C := by
    exact (Quadrilateral_cvx.not_collinear₁₂₄ (QDR_cvx e.A e.B e.D e.C e.cvx_ABDC))
  have h₂ : ¬ Collinear e.D e.B e.C := by
    have h₂' : ¬ Collinear e.B e.D e.C := by
      exact (Quadrilateral_cvx.not_collinear₂₃₄ (QDR_cvx e.A e.B e.D e.C e.cvx_ABDC))
    apply Collinear.perm₂₁₃.mt h₂'
  have C_ne_B : e.C ≠ e.B := by
    exact (Quadrilateral_cvx.nd₂₄ (QDR_cvx e.A e.B e.D e.C e.cvx_ABDC))
  --Because $AB = AC$ ,we have $\angle A B C = -\angle A C B$.
  have isoc_ABC_ang : ∠ e.C e.B e.A (C_ne_B) (e.A_ne_B) = ∠ e.A e.C e.B (e.A_ne_C) (C_ne_B.symm) := by
    have isoc_ABC : (▵ e.A e.B e.C).IsIsoceles := by
      unfold Triangle.IsIsoceles
      show (SEG e.C e.A).length = (SEG e.A e.B).length
      calc
        (SEG e.C e.A).length = (SEG e.A e.C).length := length_of_rev_eq_length'
        _= (SEG e.A e.B).length := e.AB_eq_AC.symm
    apply (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := ⟨▵ e.A e.B e.C, h₁⟩)).mp
    exact isoc_ABC
  --Because $DB = DC$ ,we have $\angle D B C = -\angle D C B$
  have isoc_DBC_ang : ∠ e.C e.B e.D (C_ne_B) (e.D_ne_B) = ∠ e.D e.C e.B (e.D_ne_C) (C_ne_B.symm) := by
    have isoc_DBC : (▵ e.D e.B e.C).IsIsoceles := by
      unfold Triangle.IsIsoceles
      show (SEG e.C e.D).length = (SEG e.D e.B).length
      calc
        (SEG e.C e.D).length = (SEG e.B e.D).length := e.BD_eq_CD.symm
        _= (SEG e.D e.B).length := length_of_rev_eq_length'
    apply (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := ⟨▵ e.D e.B e.C, h₂⟩)).mp
    exact isoc_DBC
  --$\angle A B D = \angle A B C - \angle D B C = \angle D C B - \angle A C B = --\angle A C D$
  have h : ∠  e.A e.B e.D (e.A_ne_B) (e.D_ne_B) = - ∠ e.A e.C e.D (e.A_ne_C) (e.D_ne_C) := by
    have triv₁ : (RAY e.B e.C C_ne_B) = (RAY e.B e.C C_ne_B) := by rfl
    have triv₂ : (RAY e.C e.B C_ne_B.symm) = (RAY e.C e.B C_ne_B.symm) := by rfl
    have h' : ∠ e.D e.B e.A (e.D_ne_B) (e.A_ne_B) = ∠ e.A e.C e.D (e.A_ne_C) (e.D_ne_C) := by
      calc
        _=∠ e.D e.B e.C (e.D_ne_B) (C_ne_B) + ∠ e.C e.B e.A (C_ne_B) (e.A_ne_B)  := by
          apply Angle.ang_eq_ang_add_ang_mod_pi_of_adj_ang (ANG  e.D e.B e.C (e.D_ne_B) (C_ne_B)) (ANG e.C e.B e.A (C_ne_B) (e.A_ne_B)) (triv₁)
        _=-∠ e.C e.B e.D (C_ne_B) (e.D_ne_B) + ∠ e.A e.C e.B (e.A_ne_C) (C_ne_B.symm):= by
          simp only [isoc_ABC_ang]
          simp only [neg_value_of_rev_ang (e.D_ne_B) (C_ne_B)]
        _=-∠ e.D e.C e.B (e.D_ne_C) (C_ne_B.symm) + ∠ e.A e.C e.B (e.A_ne_C) (C_ne_B.symm):= by
          simp only [isoc_DBC_ang]
        _=∠ e.A e.C e.B (e.A_ne_C) (C_ne_B.symm) + ∠ e.B e.C e.D (C_ne_B.symm) (e.D_ne_C) := by
          simp only[neg_value_of_rev_ang (e.D_ne_C) (C_ne_B.symm)]
          abel
        _=∠ e.A e.C e.D (e.A_ne_C) (e.D_ne_C) := by
          symm
          apply Angle.ang_eq_ang_add_ang_mod_pi_of_adj_ang (ANG  e.A e.C e.B (e.A_ne_C) (C_ne_B.symm)) (ANG e.B e.C e.D (C_ne_B.symm) (e.D_ne_C)) (triv₂)
    simp only [← h']
    simp only[neg_value_of_rev_ang (e.A_ne_B) (e.D_ne_B)]
  exact h
end Problem_3
end Congruence_Exercise_ygr
