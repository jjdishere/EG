import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace Problem1_9_

/-
Let $\triangle ABC$ be an isoceles triangle in which $AB = AC$. Let $E$ be a point on the extension of $BA$.

Prove that the line through $A$ parallel to $BC$ bisects $\angle EAC$.
-/

-- Let $\triangle ABC$ be an isoceles triangle in which $AB = AC$
variable {A B C : Plane} {hnd : ¬ colinear A B C} {hisoc : (▵ A B C).IsIsoceles}
-- Claim $B \ne A$
lemma B_ne_A : B ≠ A := (ne_of_not_colinear hnd).2.2
-- denote the extension of $BA$ as $BA_ext$
variable {BA_ext : Ray Plane} {hlba : BA_ext = (SEG_nd B A B_ne_A.symm).extension}
-- Let $E$ be a point on the extension of $BA$
variable {E : Plane} {E_int_ext : E LiesInt BA_ext}
-- Claim $C \ne B$
lemma C_ne_B : C ≠ B := (ne_of_not_colinear hnd).1
-- Claim $E \ne A$
lemma E_ne_A : E ≠ A := by sorry
-- Claim $C \ne A$
lemma C_ne_A : C ≠ A := (ne_of_not_colinear hnd).2.1.symm
--Prove that the line through $A$ parallel to $BC$ bisects $\angle EAC$
--which is equivalent to the line through $A$ parallel to $BC$ is the angle bisector of $\angle EAC$
--denote the angle $\angle EAC$ as $angle_eac$
variable {angle_eac : Angle Plane} {heac : angle_eac = Angle.mk_pt_pt_pt E A C E_ne_A C_ne_A}
--denote the angle bisector of $\angle EAC$ as $l_bis$
variable {l_bis : Ray Plane} {hleac : l_bis = Angle.AngBis angle_eac}
-- denote segment $BC$ as $BC$
variable {BC : Seg_nd Plane} {hbc : BC = SEG_nd B C C_ne_B}
-- denote the ray from $A$ which has the same direction as $BC$ as $l_a$
variable {l_a : Ray Plane} {hla : l_a = Ray.mk A (BC.toDir)}
--Prove that $l_a = l_bis$
theorem Problem1_9_ : l_a =  l_bis := by sorry
--ang_bis is temporarily not available to use in proofs
--So we attempt to prove the following version:

-- Let $X$ be a point on $l_a$
variable {X : Plane} {X_int_la : X LiesInt l_a}
-- Claim : $X \ne A$
lemma X_ne_A : X ≠ A := by sorry
-- Prove that $\angle EAX = \angle XAC$
theorem Problem1_9_variant : ∠ E A X E_ne_A X_ne_A = ∠ X A C X_ne_A (C_ne_A (hnd:=hnd)) := by
/-
As $AX$ is has the same direction as $BC$ and that $E$ is on the extension of $BA$, we know that $\angle EAX = \angle ABC$.
In isoceles triangle $ABC$, $\angle ABC = - \angle ACB$.
As $AX$ has the opposite direction of $CB$ and $AC$ has the opposite direction of $CA$, we have $\angle ACB = - \angel XAC$
Therefore, $\angle EAX = \angle ABC = - \angle ACB = \angle XAC$.
-/
  have C_ne_B : C ≠ B := by sorry
  calc
  ∠ E A X E_ne_A X_ne_A
  _= ∠ A B C ((B_ne_A (hnd:=hnd)).symm) C_ne_B := by sorry
  _= - ∠ A C B (C_ne_A (hnd:=hnd)).symm C_ne_B.symm := by sorry
  _= ∠ X A C X_ne_A (C_ne_A (hnd:=hnd)) := by sorry
end Problem1_9_
