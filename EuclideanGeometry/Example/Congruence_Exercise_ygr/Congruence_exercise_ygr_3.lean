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
  hcvx : (QDR A B D C).IsConvex
  he1 : (SEG A B).length = (SEG A C).length
  he2 : (SEG B D).length = (SEG C D).length
  --$A \ne B$ and $D \ne B$ for $\angle A B D$
  A_ne_B : A ≠ B := sorry
  D_ne_B : D ≠ B := sorry
  --$A \ne C$ and $D \ne B$ for $\angle A C D$
  A_ne_C : A ≠ C := sorry
  D_ne_C : D ≠ C := sorry
theorem Result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : ∠  e.A e.B e.D (e.A_ne_B) (e.D_ne_B) = - ∠ e.A e.C e.D (e.A_ne_C) (e.D_ne_C):= by
  have h₁ : ¬ colinear e.A e.B e.C := by sorry
  have h₂ : ¬ colinear e.D e.B e.C := by sorry
  sorry
end Congruence_exercise_ygr_3
