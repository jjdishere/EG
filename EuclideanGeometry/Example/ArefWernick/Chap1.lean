import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Aref-Wernick book: Problems and Solutions in Euclidean Geometry Chapter 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Aref_Wernick_Problem_1_1
/- In $\triangle ABC$, let $D$ and $E$ be any points on $AB$ and $AC$. The bisectors of the angle $\angle ABE$ and $\angle ACD$ meet at $F$.

Prove that $\angle BDC + \angle BEC = 2 \cdot \angle BFC$. -/




end Aref_Wernick_Problem_1_1




namespace Aref_Wernick_Problem_1_2
/- In $\triangle$, $\angle CAB = \pi /2$ and $AB > AC$. Let $D$ be the midpoint of $BC$ and let the perpendicular to hypotenuse $BC$ at $D$ meet the bisector of the right
angle $\angle CAB$ at $E$.

Prove that $AD = DE$ and that $\angle DAE = (\angle BCA - \angle ABC) / 2$. -/

end Aref_Wernick_Problem_1_2
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $A \ne C$ and $B \ne C$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- $D$ is the midpoint of $BC$
variable {D : P} {hd : D = (SEG B C).midpoint}
-- $l$ is the perpendicular to hypotenuse $BC$ at $D$
-- variable {l : }



end EuclidGeom
