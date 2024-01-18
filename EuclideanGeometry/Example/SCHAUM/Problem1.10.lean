import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type*} [EuclideanPlane Plane]

namespace SCHAUM_Problem_1_10
/-
Let $ABCD$ be a parallelogram. Let $P$ be the foot of the perpendicular from $A$ to the line $CD$,and let $Q$ be the foot of the perpendicular from $C$ to the line $AB$.

Prove that $APCQ$ is a rectangle.
-/

-- Let $ABCD$ be a parallelogram.
variable {A B C D : Plane} {hprg : Quadrilateral.IsParallelogram (QDR A B C D)}
-- Let $P$ be the foot of the perpendicular from $A$ to the line $CD$.
lemma d_ne_C : D ≠ C := sorry
variable {P : Plane} {hppf : P = perp_foot A (LIN C D d_ne_C)}
-- Let $Q$ be the foor of the perpendicular from $C$ to the line $AB$.
lemma B_ne_a : B ≠ A := sorry
variable {Q : Plane} {hqpf : Q = perp_foot C (LIN A B B_ne_a)}
-- State the main goal.
-------- theorem SCHAUM_Problem_1_10 : Quadrilateral.IsRectangle (QDR A P C Q) := by sorry

end SCHAUM_Problem_1_10
