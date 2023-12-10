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
  hcvx : (A B D C).IsConvex
  he1 : (SEG A B).length = (SEG A C).length
  he2 : (SEG B D).length = (SEG C D).length
  --$A \ne B$ and $D \ne B$ for $\angle A B D$
  A_ne_B : A ≠ B := sorry
  D_ne_B : D ≠ B := sorry
  --$A \ne C$ and $D \ne B$ for $\angle A C D$
  A_ne_C : A ≠ C := sorry
  D_ne_C : D ≠ C := sorry
theorem Result : ∠  A B D (A_ne_B) (D_ne_B) = -∠  A C D (A_ne_C) (D_ne_C):= by
have h₁ : ¬ colinear A B C := by sorry
have h₂ : ¬ colinear D B C := by sorry
sorry
end Congruence_exercise_ygr_3
