import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type*} [EuclideanPlane Plane]

namespace Problem1_4_
/-Let $B$ $D$ be points on segment $AF$, such that $AD = BF$. Let $C$ be a point.
Let $E$ be a point on the opposite side of $AF$ to $C$, such that EF ∥ AC and ED ∥ BC

Prove that $BC = DE$ and $AC = EF$.
-/

variable {A F : Plane} {A_ne_f : A ≠ F}
--Let $B$ be a point on $AB$.
variable {B : Plane} {B_on_seg: B LiesInt (SEG A F)}
--Let $D$ be a point on $AC$
variable {D : Plane} {D_on_seg: D LiesInt (SEG A F)}
-- $AD = BF$.
variable {seg_eq : (SEG A D).length = (SEG B F).length}
--Let $C$ be a point.
variable {C : Plane} {C_off_lin: ¬ Collinear A F C} --Implied by opposite side.
--Let $E$ be a point on the opposite side of $AF$ to $C$, such that EF ∥ AC and ED ∥ BC.
variable {E : Plane} {E_off_lin: ¬ Collinear A F E} --Implied by opposite side.
-- Claim:$C \ne A$ , $C \ne B$, $C, A, B$ is not collinear, $E, F, D$ is not collinear.
lemma cabnd : ¬ Collinear C A B := by sorry
lemma efdnd : ¬ Collinear E F D := by sorry
lemma c_ne_a : C ≠ A := (ne_of_not_collinear C_off_lin).2.1.symm
lemma c_ne_B : C ≠ B :=by
  by_contra h
  rw [h] at C_off_lin
  let S := SEG A F
  have a_on_s : A LiesOn S := by sorry
  have b_on_s : B LiesOn S := by sorry
  have f_on_s : F LiesOn S := by sorry
  absurd C_off_lin
  apply Seg.collinear_of_lies_on a_on_s f_on_s b_on_s

--Claim:$E \ne D$ , $E \ne F$.
lemma e_ne_d : E ≠ D := by sorry
lemma e_ne_f : E ≠ F := (ne_of_not_collinear E_off_lin).1
--such that EF ∥ AC and ED ∥ BC.
variable {EF_AC_para: (SegND E F e_ne_f)∥(SegND A C c_ne_a.symm)}
variable {ED_BC_para: (SegND E D e_ne_d)∥(SegND B C c_ne_B.symm)}
--(Opposite side is already implied by the known, also the theorem about sides of a line is not complete)

--Prove that $BC = DE$ and $AC = EF$.
theorem Problem1_4_ : (SEG B C).length = (SEG D E).length ∧ (SEG A C).length = (SEG E F).length := by
-- Claim : $B \ne A$, $D \ne F$, $E \ne F$.
  have b_ne_a : B ≠ A := by sorry
  have d_ne_f : D ≠ F := by sorry
  have e_ne_f : E ≠ F := by sorry
-- We have $\angle B A C = \angle D F E$ and $\angle C B A = \angle E D F$ because alternate interior angles are equal.
  have ang2 : ∠ B A C b_ne_a (c_ne_a (C_off_lin := C_off_lin)) = ∠ D F E d_ne_f e_ne_f := by
    have alt : IsAlternateIntAng (ANG C A B (c_ne_a (C_off_lin := C_off_lin)) b_ne_a) (ANG E F D e_ne_f d_ne_f) := by
      constructor
      · sorry
      · sorry
    have : ∠ C A B (c_ne_a (C_off_lin := C_off_lin)) b_ne_a = ∠ E F D e_ne_f d_ne_f := eq_value_of_isalternateintang alt
    calc
      _ = - ∠ C A B (c_ne_a (C_off_lin := C_off_lin)) b_ne_a := by apply neg_value_of_rev_ang
      _ = - ∠ E F D e_ne_f d_ne_f := by rw [this]
      _ = ∠ D F E d_ne_f e_ne_f := (neg_value_of_rev_ang d_ne_f e_ne_f).symm
  have ang3 : ∠ C B A c_ne_b b_ne_a.symm = ∠ E D F e_ne_d d_ne_f.symm := by
    have alt : IsAlternateIntAng (ANG C B A c_ne_b b_ne_a.symm) (ANG E D F e_ne_d d_ne_f.symm) := by sorry
    exact eq_value_of_isalternateintang alt
-- We have $AB = FD$ because $AD = AF - BF = AF - BD = BF$.
  have seg1 : (SEG A B).length = (SEG F D).length := by
    calc
      _ = (SEG A F).length - (SEG B F).length := by
        apply eq_sub_of_add_eq
        symm
        apply length_eq_length_add_length B_on_seg
      _ = (SEG A F).length - (SEG A D).length := by rw [seg_eq]
      _ = (SEG D F).length := (eq_sub_of_add_eq' (length_eq_length_add_length (D_on_seg)).symm).symm
      _ = (SEG F D).length := length_of_rev_eq_length'
-- Then $\triangle CAB ≅ \triangle EFD$ by SAS.
  have hcong : Triangle_nd.IsCongr (TRI_nd C A B cabnd) (TRI_nd E F D efdnd) := by
    apply Triangle_nd.congr_of_ASA
    · exact ang2
    · exact seg1
    · exact ang3
-- The main goal can then be proved by the congruence.
  constructor
  · exact hcong.edge₂
  · calc
      _ = (SEG C A).length := length_of_rev_eq_length'
      _ = (SEG E F).length := hcong.edge₃
end Problem1_4_
