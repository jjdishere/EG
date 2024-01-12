import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace Problem1_4_
/-Let $B$ $D$ be points on segment $AF$,such that $AD =BF$.Let $C$ be a point.
Let $E$ be a point on the opposite side of $AF$ to $C$, such that EF ∥ AC and ED ∥ BC

Prove that $BC =DE$ and $AC =EF$.
-/

variable {A F : Plane} {A_ne_f : A ≠ F}
--Let $B$ be a point on $AB$.
variable {B : Plane} {B_on_seg: B LiesInt (SEG A F)}
--Let $D$ be a point on $AC$
variable {D : Plane} {D_on_seg: D LiesInt (SEG A F)}
--Let $C$ be a point.
variable {C : Plane} {C_off_lin: ¬ colinear A F C} --Implied by opposite side.
--Let $E$ be a point on the opposite side of $AF$ to $C$, such that EF ∥ AC and ED ∥ BC.
variable {E : Plane} {E_off_lin: ¬ colinear A F E} --Implied by opposite side.
-- Claim:$C \ne A$ , $C \ne B$.
lemma c_ne_a : C ≠ A := (ne_of_not_colinear C_off_lin).2.1.symm
lemma c_ne_B : C ≠ B :=by
  by_contra h
  rw [h] at C_off_lin
  let S := SEG A F
  have a_on_s : A LiesOn S := by sorry
  have b_on_s : B LiesOn S := by sorry
  have f_on_s : F LiesOn S := by sorry
  absurd C_off_lin
  apply Seg.colinear_of_lies_on a_on_s f_on_s b_on_s

--Claim:$E \ne D$ , $E \ne F$.
lemma e_ne_d : E ≠ D :=by
  by_contra h
  rw [h] at E_off_lin
  let S := SEG A F
  have a_on_s : A LiesOn S := by sorry
  have d_on_s : D LiesOn S := by sorry
  have f_on_s : F LiesOn S := by sorry
  absurd E_off_lin
  apply Seg.colinear_of_lies_on a_on_s f_on_s d_on_s
lemma e_ne_f : E ≠ F := (ne_of_not_colinear E_off_lin).1
--such that EF ∥ AC and ED ∥ BC.
variable {EF_AC_para: (SegND E F e_ne_f)∥(SegND A C c_ne_a.symm)}
variable {ED_BC_para: (SegND E D e_ne_d)∥(SegND B C c_ne_B.symm)}
--(Opposite side is already implied by the known, also the theorem about sides of a line is not complete)

--Prove that $BC =DE$ and $AC =EF$.
theorem Problem1_4_ : (SEG B C).length = (SEG D E).length ∧ (SEG A C).length = (SEG E F).length :=by
sorry
end Problem1_4_
