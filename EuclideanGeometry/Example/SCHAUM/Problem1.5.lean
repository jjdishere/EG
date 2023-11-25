import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace Problem1_5_

/-
Let $ABCD$ be a parallelogram, and let $P$, $Q$, $R$, $S$ be points on the segments $AB$, $BC$, $CD$, $DA$, respectively,
such that $AP = CR$ and $AS = CQ$.

Prove that $PQRS$ is a parallelogram.
-/

--Let $ABCD$ be a parallelogram
variable {A B C D : Plane} {hprg : Quadrilateral.IsParallelogram (QDR A B C D)}
--let $P$ be point on the segment $AB$
variable {P : Plane} {P_on_seg : P LiesInt (SEG A B)}
--let $Q$ be point on the segment $BC$
variable {Q : Plane} {Q_on_seg : Q LiesInt (SEG B C)}
--let $R$ be point on the segment $CD$
variable {R : Plane} {R_on_seg : R LiesInt (SEG C D)}
--let $S$ be point on the segment $DA$
variable {S : Plane} {S_on_seg : S LiesInt (SEG D A)}
--such that $AP = CR$
variable {P_R_position : (SEG A P).length = (SEG C R).length}
--such that $AS = CQ$
variable {S_Q_position : (SEG A S).length = (SEG C Q).length}
--Prove that $PQRS$ is a parallelogram
theorem Problem1_5_ : Quadrilateral.IsParallelogram (QDR P Q R S) := by
  have pq_eq_sr : (SEG P Q).length = (SEG R S).length := by sorry
  have qr_eq_sp : (SEG Q R).length = (SEG S P).length := by sorry
  sorry
end Problem1_5_
