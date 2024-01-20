import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

namespace AOPS_Problem_5_7
/- Let $\triangle ABC$ be a triangle, and let $D$, $E$ be two points in the interior of $AB$ and $AC$ respectively such that $DE\parallel BC$ . $X$ lies inside $AB$ and $Y$ lies on the ray $XE$ so that $AY\parallel XC$

Prove that $\frac{EY}{EX}=\frac{AD}{DB} -/

--Triangle A B C
variable {A B C : P} {hnd : ¬ Collinear A B C}
lemma b_ne_a : B ≠ A := sorry
lemma c_ne_a : C ≠ A := sorry
lemma c_ne_b : C ≠ B := sorry

--D lies in AB and E lies in AE
variable {D E : P} {hd : D LiesInt SEG_nd A B b_ne_a} {he : E LiesInt (SEG_nd A C c_ne_a)}

lemma e_ne_d : D ≠ E := sorry
--DE parallels to BC
variable {hde: (LIN D E e_ne_d) ∥ (LIN B C c_ne_b)}
--X lies in AB
variable{X : P} {hx : X LiesInt (SEG_nd A B b_ne_a)}
--X is not E,C
lemma x_ne_c : X ≠ C := sorry
lemma x_ne_e : X ≠ E := sorry
--Y is not A
variable {Y : P} {hy₁ : Y LiesOn (LIN X E x_ne_e.symm)}
lemma y_ne_a : Y ≠ A := sorry
--Y lies in XE, AY parallels to XC
variable  {hy₂ : (LIN A Y y_ne_a)∥(LIN X C x_ne_c.symm)}

theorem AOPS_Problem_5_7 : (SEG E Y).length/(SEG E X).length = (SEG A D).length/(SEG D B).length := sorry
end AOPS_Problem_5_7


namespace AOPS_Exercise_5_2_3
/- Let $WXYZ$ be a square. $M$ is the midpoint of $YZ$, $A$ lies on $WZ$ and $B$ lies on $XY$, if $AB\perp MX$, prove that
\begin{enumerate}[(a)]
\item $WZ\para XY$
\item $AZ=YB$
\item $XB=XA$
\item $\triangle AZM\sim\triangle MYX$
\item $AZ=XY/4$
\end{enumerate}.
 -/
--Need the definition of square.

end AOPS_Exercise_5_2_3


namespace AOPS_Exercise_5_3_2
/- \triangle ABC$, $E$ lies on the extension of $CA$ while $F$ lies on the extension of $BA$, $I$ lies on the extension of $CE$ and $J$ lies on the extension of $BF$. Assume that $AC=AE=EI$, $AB=AF=FJ$.

Prove that $IJ\prar BC$-/
--It is simpler to use vectors but I think we should avoid vectors.

--Nontrivial triangle A B C
variable {A B C : P} {hnd : ¬ Collinear A B C}
lemma b_ne_a : B ≠ A := sorry
lemma c_ne_a : C ≠ A := sorry
lemma c_ne_b : C ≠ B := sorry
--E lies on the extension of CA and F lies on the extension of BA
variable {E F : P} {he₁ : E LiesInt (SEG_nd C A c_ne_a).extension} {hf₁ : F LiesInt (SEG_nd B A b_ne_a).extension}
lemma e_ne_c : E ≠ C := sorry
lemma f_ne_b : F ≠ B := sorry
--I lies on the extension of CE and J lies on the extension of BF
variable {I J : P} {hi₁ : I LiesInt (SEG_nd C E e_ne_c).extension} {hj₁ : J LiesInt (SEG_nd B F f_ne_b).extension}
-- $AC=AE=EI$, $AB=AF=FJ$
variable {he₂ : (SEG A C).length = (SEG A E).length} {hf₂ : (SEG A B).length = (SEG A F).length} {hi₂ : (SEG A C).length = (SEG E I).length} {hj₂ : (SEG A B).length = (SEG F J).length}
lemma j_ne_i : J ≠ I := sorry
theorem AOPS_Exercise_5_3_2 : LIN I J j_ne_i ∥ LIN B C c_ne_b := sorry
end AOPS_Exercise_5_3_2

namespace AOPS_Problem_5_14
/- Let $\triangle ABC$ be a right triangle with $\angle BAC = 90^{\circ}$, $AX$ is height.

Prove that AX^2 = BX \codt CX. -/

-- In right triangle $\triangle PQR$, $\angle QPR = 90^{\circ}$
variable {A B C : P} {hnd : ¬ Collinear A B C}
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
variable {A B C : P} {hnd : ¬ Collinear A B C} {hne : (SEG A C).length ≠ (SEG B C).length}
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
