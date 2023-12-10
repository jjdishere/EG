import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Congruence_exercise_ygr_1

/-
In (convex) quadrilateral $A B D C$,$AB = AC$, $BD = CD$.
Prove that $\angle A B D = -\angle A C D$
-/
--In (convex) quadrilateral $A B D C$,$AB = AC$, $BD = CD$.
variable {A B C D : P} {hcvx : (A B D C).IsConvex} {he1 : (SEG A B).length = (SEG A C).length} {he2 : (SEG B D).length = (SEG C D).length}
--$A \ne B$ and $D \ne B$ for $\angle A B D$
lemma A_ne_B : A ≠ B := sorry
lemma D_ne_B : D ≠ B := sorry
--$A \ne C$ and $D \ne B$ for $\angle A C D$
lemma A_ne_C : A ≠ C := sorry
lemma D_ne_C : D ≠ C := sorry
theorem Congruence_exercise_ygr_1 : ∠  A B D (A_ne_B) (D_ne_B) = -∠  A C D (A_ne_C) (D_ne_C):= by
have h₁ : ¬ colinear A B C := by sorry
have h₂ : ¬ colinear D B C := by sorry
sorry
end Congruence_exercise_ygr_1
