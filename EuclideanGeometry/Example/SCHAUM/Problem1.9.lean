import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace Problem1_9_

/-
Let $\triangle ABC$ be an isoceles triangle in which $AB = AC$. Let $E$ be a point on the extension of $BA$.

Prove that the line through $A$ parallel to $BC$ bisects $\angle EAC$.
-/

--Let $\triangle ABC$ be an isoceles triangle in which $AB = AC$
variable {A B C : Plane} {hnd : ¬ colinear A B C} {hisoc : (▵ A B C).IsIsoceles}
--Claim $B \ne A$
lemma b_ne_a : B ≠ A := (ne_of_not_colinear hnd).2.2
--Let $E$ be a point on the extension of $BA$
variable {l_ba_ext : Ray Plane} {hlba : l_ba_ext = (SEG_nd B A b_ne_a.symm).extension}
variable {E : Plane} {E_on_ext : E LiesInt l_ba_ext}
--Claim $C \ne B$
lemma c_ne_b : C ≠ B := (ne_of_not_colinear hnd).1
--Claim $E \ne A$
lemma e_ne_a : E ≠ A := by sorry
--Claim $C \ne A$
lemma c_ne_a : C ≠ A := (ne_of_not_colinear hnd).2.1.symm
--Prove that the line through $A$ parallel to $BC$ bisects $\angle EAC$
--which is equivalent to the line through $A$ parallel to $BC$ is the angle bisector of $\angle EAC$
--let $seg_nd_nc$ be the non-degenerate segment between $B$ and $C$
variable {seg_nd_bc : Seg_nd Plane} {hbc : seg_nd_bc = SEG_nd B C c_ne_b}
--denote the angle $\angle EAC$ as $angle_eac$
variable {angle_eac : Angle Plane} {heac : angle_eac = Angle.mk_pt_pt_pt E A C e_ne_a c_ne_a}
variable {l_a_para_bc : Line Plane} {hlabc : l_a_para_bc = Line.mk_pt_proj A (seg_nd_bc.toProj)}
variable {l_bis_eac : Line Plane} {hleac : l_bis_eac = Angle.AngBisLine angle_eac}
theorem Problem1_9_ : l_a_para_bc =  l_bis_eac := by sorry
--ang_bis is temporarily not available to use in proofs
end Problem1_9_
