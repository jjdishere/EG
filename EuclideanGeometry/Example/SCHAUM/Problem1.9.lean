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
-- denote $BA_ext$ as the extension of $BA$
variable {BA_ext : Ray Plane} {hlba : BA_ext = (SEG_nd B A B_ne_A.symm).extension}
-- Let $E$ be a point on the extension of $BA$
variable {E : Plane} {E_int_ext : E LiesInt BA_ext}
-- Claim $C \ne B$
lemma C_ne_B : C ≠ B := (ne_of_not_colinear hnd).1
-- Claim $E \ne A$
lemma E_ne_A : E ≠ A := by sorry
-- Claim $C \ne A$
lemma C_ne_A : C ≠ A := (ne_of_not_colinear hnd).2.1.symm
/-
--Prove that the line through $A$ parallel to $BC$ bisects $\angle EAC$
--which is equivalent to the line through $A$ parallel to $BC$ is the angle bisector of $\angle EAC$
--let $seg_nd_nc$ be the non-degenerate segment between $B$ and $C$
--denote the angle $\angle EAC$ as $angle_eac$
variable {angle_eac : Angle Plane} {heac : angle_eac = Angle.mk_pt_pt_pt E A C e_ne_a c_ne_a}
variable {l_bis_eac : Line Plane} {hleac : l_bis_eac = Angle.AngBisLine angle_eac}
theorem Problem1_9_ : l_a_para_bc =  l_bis_eac := by sorry
--ang_bis is temporarily not available to use in proofs
So we attempt to prove the following version:
-/
-- denote $BC$ as segment $BC$
variable {BC : Seg_nd Plane} {hbc : BC = SEG_nd B C C_ne_B}
-- denote $l_a$ as the line passing through $A$ which is parallel to $BC$
variable {l_a : Line Plane} {hla : l_a = Line.mk_pt_proj A (BC.toProj)}
-- Let $X$ be a point on $l_a$
variable {X : Plane} {X_on_la : X LiesOn l_a} {X_ne_A : X ≠ A}
theorem Problem1_9_variant : ∠ E A X E_ne_A X_ne_A = ∠ X A C X_ne_A (C_ne_A (hnd:=hnd)) := by
  have C_ne_B : C ≠ B := by sorry
  calc
  ∠ E A X E_ne_A X_ne_A
  _= ∠ A B C ((B_ne_A (hnd:=hnd)).symm) C_ne_B := by sorry
  _= - ∠ A C B (C_ne_A (hnd:=hnd)).symm C_ne_B.symm := by sorry
  _= ∠ X A C X_ne_A (C_ne_A (hnd:=hnd)) := by sorry
end Problem1_9_
