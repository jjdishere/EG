import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Shan_Problem_1_7
/- In $\triangle ABC$, $\angle ACB = \pi /2$. Let $D$ be the midpoint of $AB$.

Prove that $CD = AB / 2$. -/

-- We have triangle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- We have $\angle ACB = \pi /2$
variable {h : ∠ A C B c_ne_a.symm b_ne_c = π / 2}
-- $D$ is the midpoint of $AB$
variable {D : P} {hd : D = (SEG A B).midpoint}

theorem Shan_Problem_1_7 : (SEG C D).length = (SEG A B).length / 2 := sorry

end Shan_Problem_1_7

namespace Shan_Problem_1_8
/- In $\triangle ABC$, let $BD$ and $CE$ be the heights,
with foots $D$ and $E$, respectively. Let $F$ and $G$ be the midpoint of $BC$ and $DE$,
respectively.

Prove that $FG \perp DE$. -/

-- We have triangle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- $BD$ and $CE$ are the heights, with foots $D$ and $E$, respectively
variable {D E : P} {hd : D = perp_foot B (LIN A C c_ne_a)} {he : E = perp_foot C (LIN A B a_ne_b.symm)}
-- $F$ and $G$ are the midpoint of $BC$ and $DE$, respectively
variable {F G : P} {hf : F = (SEG B C).midpoint} {hg : G = (SEG D E).midpoint}
-- Claim: $G \ne F$ and $E \ne D$
lemma g_ne_f : G ≠ F := sorry
lemma e_ne_d : E ≠ D := sorry

theorem Shan_Problem_1_8 : LinearObj.seg_nd (SEG_nd F G g_ne_f) ⟂ (SEG_nd D E e_ne_d) := sorry

end Shan_Problem_1_8
