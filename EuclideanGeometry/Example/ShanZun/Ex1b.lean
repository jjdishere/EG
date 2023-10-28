import EuclideanGeometry.Foundation.Index


noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Shan_Problem_1_5
/- In $\triangle ABC$, let $AD$ be the median.  Let $E$ be a point on $AD$ such that $BE = AC$. The line $BE$ intersects $AC$ at $F$.

Prove that $AF = EF$. -/

-- We have triangle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- $D$ is the midpoint of $BC$
variable {D : P} {hd : D = (SEG B C).midpoint}
-- $E$ is a point on $AD$
variable {E : P} {he : E LiesOn (SEG A D)}
-- We have $BE = AC$
variable (hedg : (SEG B E).length = (SEG A C).length)
-- Claim: $B \ne E$
lemma b_ne_e : B ≠ E := sorry
-- The line $BE$ intersects $AC$ at $F$
variable {F : P} {hf : is_inx F (LIN B E b_ne_e.symm) (SEG A C)}

theorem Shan_Problem_1_5 : (SEG A F).length = (SEG E F).length := sorry


end Shan_Problem_1_5

namespace Shan_Problem_1_6
/- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.

Prove that For any point $D$ on the base $BC$,
the sum of the the distance of $D$ to $AB$ and to $AC$ is independent of $D$. -/

-- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : P} {hnd : ¬ colinear A B C} {hisoc : (▵ A B C).IsIsoceles}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- For any $D$, let $htsum(D)$ be the sum of the the distance of $D$ to $AB$ and to $AC$
def htsum (D : P) : ℝ := dist_pt_line D (LIN A B a_ne_b.symm) + dist_pt_line D (LIN A C c_ne_a)
-- $D₁, D₂$ are arbitary points on segment $BC$
variable {D₁ D₂ : P} {hd₁ : D₁ LiesInt (SEG B C)} {hd₂ : D₂ LiesInt (SEG B C)}

theorem Shan_Problem_1_6 : htsum (A := A) (B := B) (C := C) D₁ = htsum (A := A) (B := B) (C := C) D₂ := sorry


end Shan_Problem_1_6
