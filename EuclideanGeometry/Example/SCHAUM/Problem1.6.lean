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
variable {A B C D : Plane} {hprgnd : (QDR A B C D) IsPRG_nd}
--Let $P$ be point on the segment $AB$
variable {P : Plane} {P_int_AB : P LiesInt (SEG A B)}
--Let $Q$ be point on the segment $CD$
variable {Q : Plane} {Q_int_CD : Q LiesInt (SEG C D)}
--such that $AP = CQ$
variable {AP_eq_CQ : (SEG A P).length = (SEG C Q).length}
--Prove that $PB = QD$
theorem Problem1_6_ : (SEG P B).length = (SEG Q D).length := by
/-
In the parallelogram $ABCD$ we have $AB = CD$.
Therefore, $PB = AB - AP = CD - CQ = QD$.
-/
  -- We have $AB = CD$ because $ABCD$ is a parallelogram
  have AB_eq_CD : (SEG A B).length = (SEG C D).length := eq_length_of_is_prg_nd_variant hprgnd
  calc
  (SEG P B).length
  -- $PB = (AP + PB) - AP$,
  _= ((SEG A P).length + (SEG P B).length) - (SEG A P).length := by ring
  -- $AP + PB = AB$ because $P$ lies on $AB$,
  _= (SEG A B).length -  (SEG A P).length := by
    congr; symm
    apply length_eq_length_add_length
    apply Seg.lies_on_of_lies_int
    exact P_int_AB
  -- $AB - AP = CD - CQ$ since $AB = CD$ and $AP = CQ$,
  _= (SEG C D).length - (SEG C Q).length := by
    rw [AP_eq_CQ, AB_eq_CD]
  -- $CD - CQ = (CQ + QD) - CQ$ because $Q$ lies on $CD$,
  _= ((SEG C Q).length + (SEG Q D).length) - (SEG C Q).length := by
    congr;
    apply length_eq_length_add_length
    apply Seg.lies_on_of_lies_int
    exact Q_int_CD
  -- $(CQ + QD) - CQ = QD$.
  _= (SEG Q D).length := by ring
end Problem1_6_
