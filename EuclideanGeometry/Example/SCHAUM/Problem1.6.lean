import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

namespace Schaum

namespace Problem1_6

/-
Let $ABCD$ be a parallelogram, and let $P$, $Q$ be points on the segments $AB$ and $CD$ such that $AP = CQ$.

Prove that $PB = QD$.
-/
structure Setting (Plane : Type*) [EuclideanPlane Plane] where
--Let $ABCD$ be a parallelogram
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  hprgnd : (QDR A B C D) IsPRG_nd
--Let $P$ be point on the segment $AB$
  P : Plane
  P_int_AB : P LiesInt (SEG A B)
--Let $Q$ be point on the segment $CD$
  Q : Plane
  Q_int_CD : Q LiesInt (SEG C D)
--such that $AP = CQ$
  AP_eq_CQ : (SEG A P).length = (SEG C Q).length
--Prove that $PB = QD$
theorem result {Plane : Type*} [EuclideanPlane Plane] (e : Setting Plane) : (SEG e.P e.B).length = (SEG e.Q e.D).length := by
/-
In the parallelogram $ABCD$ we have $AB = CD$.
Therefore, $PB = AB - AP = CD - CQ = QD$.
-/
  -- We have $AB = CD$ because $ABCD$ is a parallelogram
  have AB_eq_CD : (SEG e.A e.B).length = (SEG e.C e.D).length := eq_length_of_is_prg_nd_variant e.hprgnd
  calc
  (SEG e.P e.B).length
  -- $PB = (AP + PB) - AP$,
  _= ((SEG e.A e.P).length + (SEG e.P e.B).length) - (SEG e.A e.P).length := by ring
  -- $AP + PB = AB$ because $P$ lies on $AB$,
  _= (SEG e.A e.B).length -  (SEG e.A e.P).length := by
    congr; symm
    apply length_eq_length_add_length
    apply Seg.lies_on_of_lies_int
    exact e.P_int_AB
  -- $AB - AP = CD - CQ$ since $AB = CD$ and $AP = CQ$,
  _= (SEG e.C e.D).length - (SEG e.C e.Q).length := by
    simp only [e.AP_eq_CQ, AB_eq_CD]
  -- $CD - CQ = (CQ + QD) - CQ$ because $Q$ lies on $CD$,
  _= ((SEG e.C e.Q).length + (SEG e.Q e.D).length) - (SEG e.C e.Q).length := by
    congr;
    apply length_eq_length_add_length
    apply Seg.lies_on_of_lies_int
    exact e.Q_int_CD
  -- $(CQ + QD) - CQ = QD$.
  _= (SEG e.Q e.D).length := by ring
end Problem1_6
end Schaum
end EuclidGeom
