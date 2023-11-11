import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Shan_Problem_1_9
/- In $\triangle ABC$, assume that $\angle CBA = 2\cdot \angle ACB$. Let $AD$ be the height and $AE$ the median.

Prove that $AB = 2\cdot DE$. -/

-- We have triangle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- We have $\angle CBA = 2\cdot \angle ACB$
variable {hang : ∠ C B A b_ne_c.symm a_ne_b = 2 * ∠ A C B c_ne_a.symm b_ne_c}
-- $AD$ is the height
variable {D : P} {hd : D = perp_foot A (LIN B C b_ne_c.symm)}
-- $AE$ is the median
variable {E : P} {he : E = (SEG B C).midpoint}

theorem Shan_Problem_1_9 : (SEG A B).length = 2 * (SEG D E).length := sorry

end Shan_Problem_1_9

namespace Shan_Problem_1_10
/- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$ and $\angle BAC = 3\pi /5$. Extend $AC$ to $E$ such that $AE = BC$. Let $D$ be the midpoint of $BE$.

Prove that $AD = DC$. -/

-- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : P} {hnd : ¬ colinear A B C} {hisoc : (▵ A B C).IsIsoceles}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- We have $\angle BAC = 3\pi /5$
variable {hang : ∠ B A C a_ne_b.symm c_ne_a = 3 * π / 5}
-- $E$ lies in the extension of $AC$ and $AE = BC$
variable {E : P} {he₁ : E LiesInt (SEG_nd A C c_ne_a).extension} {he₂ : (SEG A E).length = (SEG B C).length}
-- $D$ is the midpoint of $BE$
variable {D : P} {hd : D = (SEG B E).midpoint}

theorem Shan_Problem_1_10 : (SEG A D).length = (SEG D C).length := sorry

end Shan_Problem_1_10
