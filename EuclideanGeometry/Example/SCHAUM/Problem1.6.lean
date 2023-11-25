import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace Problem1_6_

/-
Let $ABCD$ be a parallelogram, and let $P$, $Q$ be points on the segments $AB$ and $CD$ such that $AP = CQ$.

Prove that $PB = QD$.
-/

--Let $ABCD$ be a parallelogram
variable {A B C D : Plane} {hprg : Quadrilateral.IsParallelogram (QDR A B C D)}
--Let $P$ be point on the segment $AB$
variable {P : Plane} {P_on_seg : P LiesInt (SEG A B)}
--Let $Q$ be point on the segment $CD$
variable {Q : Plane} {Q_on_seg : Q LiesInt (SEG C D)}
--such that $AP = CQ$
variable {P_Q_position : (SEG A P).length = (SEG C Q).length}
--Prove that $PB = QD$
theorem Problem1_6_ : (SEG P B).length = (SEG Q D).length := by
  have ab_eq_cd : (SEG A B).length = (SEG C D).length := eq_length_of_is_prg_variant hprg
  calc
  (SEG P B).length
  _= ((SEG A P).length + (SEG P B).length) - (SEG A P).length := by ring
  _= (SEG A B).length -  (SEG A P).length := by
    congr; symm
    apply length_eq_length_add_length
    apply Seg.lies_on_of_lies_int
    exact P_on_seg
  _= (SEG C D).length - (SEG C Q).length := by
    rw [P_Q_position, ab_eq_cd]
  _= ((SEG C Q).length + (SEG Q D).length) - (SEG C Q).length := by
    congr;
    apply length_eq_length_add_length
    apply Seg.lies_on_of_lies_int
    exact Q_on_seg
  _= (SEG Q D).length := by ring
end Problem1_6_
