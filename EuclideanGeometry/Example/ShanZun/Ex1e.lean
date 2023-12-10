import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Shan_Problem_2_13
/- In $\triangle ABC$. Let $D$ be the midpoint of segment $BC$,
the perpendicular line passing through $D$ of the bisector of $\angle BAC$ intersects $AB,AC$ at $E,F$ respectively.
Prove that $BE=CF=\frac{1}{2}|AB-AC|$.  -/

-- We have triagngle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- $D$ is the midpoint of $BC$
variable {D : P} {hd : D = (SEG B C).midpoint}
-- the perpendicular line passing through $D$ of the bisector of $\angle BAC$ intersects $AB,AC$ at $E,F$ respectively.
-- Introduce two points colinear and the orthogonality. The colinear condition is not helpful.
variable {E F : P} {l : Line P} {hl : l = perp_line D (ANG B A C a_ne_b.symm c_ne_a).AngBis.toLine} {he : is_inx E (LIN A B a_ne_b.symm) l} {hf : is_inx F (LIN A C c_ne_a) l}

-- Theorem : $BE=CF=\frac{1}{2}|AB-AC|$
theorem Shan_Problem_2_13 : (SEG B E).length=|((SEG A B).length-(SEG A C).length)|/2 ∧ (SEG C F).length = |((SEG A B).length-(SEG A C).length)|/2 := sorry

end Shan_Problem_2_13

namespace Shan_Problem_2_18
/- In $\triangle ABC$, $AC < BC$. Let $CD$ be the height,
 $CE$ be the bisector of $\angle ACB$ and $CF$ be the median.
Prove that $E$ liesInt $DF$ -/

-- We have triagngle $\triangle ABC$ such that $AC < BC$
variable {A B C : P} {hnd : ¬ colinear A B C} {hedge : (SEG A C).length < (SEG B C).length}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- $CD$ is height of $\triangle ABC$
variable {D : P} {hd : D = perp_foot A (LIN B C b_ne_c.symm)}
-- $CE$ is the angle bisector of $\angle ACB$
variable {E : P} {he : is_inx E (ANG A C B c_ne_a.symm b_ne_c).AngBis (SEG B C)}
-- $CF$ is median of $\triangle ABC$
variable {F : P} {hf : F = (SEG B C).midpoint}

theorem Shan_Problem_2_18 : E LiesInt (SEG D F) := sorry

end Shan_Problem_2_18

namespace Shan_Problem_2_18'
/- In $\triangle ABC$, $AC < BC$. Let $CD$ be the height,
 $CE$ be the bisector of $\angle ACB$ and $CF$ be the median.
If $\angle ACB = 90^{circ}$, prove that $CE$ is the bisector of $\angle FCD$.  -/

-- We have triagngle $\triangle ABC$ such that $AC < BC$
variable {A B C : P} {hnd : ¬ colinear A B C} {hedge : (SEG A C).length < (SEG B C).length}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- $CD$ is height of $\triangle ABC$
variable {D : P} {hd : D = perp_foot A (LIN B C b_ne_c.symm)}
-- $CE$ is the angle bisector of $\angle ACB$
variable {E : P} {he : is_inx E (ANG A C B c_ne_a.symm b_ne_c).AngBis (SEG B C)}
-- $CF$ is median of $\triangle ABC$
variable {F : P} {hf : F = (SEG B C).midpoint}
-- We have $\angle ACB = 90^{circ}$
variable {hright : ∠ A C B c_ne_a.symm b_ne_c = ↑ (π / 2)}
-- Claim: $D \ne C$, $E \ne C$ and $F \ne C$
lemma d_ne_c : D ≠ C := sorry
lemma e_ne_c : E ≠ C := sorry
lemma f_ne_c : F ≠ C := sorry

-- Theorem : $CE$ is the bisector of $\angle FCD$
theorem Shan_Problem_2_18' : ∠ F C E f_ne_c e_ne_c = ∠ E C D e_ne_c d_ne_c := sorry

end Shan_Problem_2_18'
