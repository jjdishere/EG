import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Congruence_exercise_ygr_3

/-
In (convex) quadrilateral $A B D C$,$AB = AC$, $BD = CD$.
Prove that $\angle A B D = -\angle A C D$
-/
structure Setting  (Plane : Type _) [EuclideanPlane Plane] where
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
theorem Result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : ∠  e.A e.B e.D (e.A_ne_B) (e.D_ne_B) = - ∠ e.A e.C e.D (e.A_ne_C) (e.D_ne_C):= by
  /-
  Because $AB = AC$ ,we have $\angle A B C = -\angle A C B$.
  Because $DB = DC$ ,we have $\angle D B C = -\angle D C B$
  $\angle A B D = \angle A B C - \angle D B C = \angle D C B - \angle A C B = --\angle A C D$
  -/
  have h₁ : ¬ colinear e.A e.B e.C := by
    exact (Quadrilateral_cvx.not_colinear₁₂₄ (QDR_cvx e.A e.B e.D e.C e.cvx_ABDC))
  have h₂ : ¬ colinear e.A e.C e.D := by
    exact (Quadrilateral_cvx.not_colinear₁₄₃ (QDR_cvx e.A e.B e.D e.C e.cvx_ABDC))
  have C_ne_B : e.C ≠ e.B := by
    exact (Quadrilateral_cvx.nd₂₄ (QDR_cvx e.A e.B e.D e.C e.cvx_ABDC))
  --Because $AB = AC$ ,we have $\angle A B C = -\angle A C B$.
  have isoc_ABC_ang : ∠ e.A e.B e.C (e.A_ne_B) (C_ne_B) = -∠ e.A e.C e.B (e.A_ne_C) (C_ne_B.symm) := by sorry
  --Because $DB = DC$ ,we have $\angle D B C = -\angle D C B$
  have isoc_DBC_ang : ∠ e.D e.B e.C (e.D_ne_B) (C_ne_B) = -∠ e.D e.C e.B (e.D_ne_C) (C_ne_B.symm) := by sorry
  --$\angle A B D = \angle A B C - \angle D B C = \angle D C B - \angle A C B = --\angle A C D$
  have h : ∠  e.A e.B e.D (e.A_ne_B) (e.D_ne_B) = - ∠ e.A e.C e.D (e.A_ne_C) (e.D_ne_C) := by sorry
  exact h
end Congruence_exercise_ygr_3
