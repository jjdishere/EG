import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace AOPS_Problem_5_14
/- Let $\triangle ABC$ be a right triangle with $\angle BAC = 90^{\circ}$, $AX$ is height.

Prove that AX^2 = BX \codt CX. -/

-- In right triangle $\triangle PQR$, $\angle QPR = 90^{\circ}$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
variable {hright : ∠ B A C a_ne_b.symm c_ne_a = ↑ (π / 2)}
-- $AX$ is height of $\triangle ABC$
variable {X : P} {hx : X = perp_foot A (LIN B C b_ne_c.symm)}

-- Theorem : AX^2 = BX \codt CX
theorem AOPS_Problem_5_14 : (SEG A X).length * (SEG A X).length = (SEG B X).length * (SEG C X).length := sorry

end AOPS_Problem_5_14

namespace AOPS_Problem_5_16
/- In $\triangle ABC$, $AC \ne BC$, $Q$ lies in the angle bisector of $\angle$ such that $AQ \perp CQ$,
$M$ is the midpoint of $AB$
Prove that $MQ \parallel BC$ -/

-- We have triangle $\triangle ABC$ with $AC \ne BC$
variable {A B C : P} {hnd : ¬ colinear A B C} {hne : (SEG A C).length ≠ (SEG B C).length}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- $Q$ lies in the angle bisector of $\angle$
variable {Q : P} {hq₁ : Q LiesInt (ANG A C B c_ne_a.symm b_ne_c).AngBis}
-- Claim: $Q \ne A$ and $Q \ne C$
lemma q_ne_a : Q ≠ A := sorry
lemma q_ne_c : Q ≠ C := sorry
-- We have $AQ \perp CQ$
variable {hq₂ : (SEG_nd A Q q_ne_a) ⟂ (SEG_nd C Q q_ne_c)}
-- $M$ is the midpoint of $AB$
variable {M : P} {hm : M = (SEG A B).midpoint}
-- Claim : $Q \ne M$
lemma q_ne_m : Q ≠ M := sorry

theorem AOPS_Problem_5_16 : (SEG_nd M Q q_ne_m) ∥ (SEG_nd B C b_ne_c.symm) := sorry

end AOPS_Problem_5_16

end EuclidGeom
