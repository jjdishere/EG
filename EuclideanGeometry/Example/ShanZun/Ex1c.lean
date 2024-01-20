import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

namespace Shan_Problem_1_7
/- In $\triangle ABC$, $\angle ACB = \pi /2$. Let $D$ be the midpoint of $AB$.

Prove that $CD = AB / 2$. -/

variable {A B C: P} {hnd : ¬ Collinear A B C}
-- Claim: $A \ne B$ and $A \ne C$ and $B \ne C$.
-- This is because vertices of nondegenerate triangles are distinct.
lemma B_ne_a : B ≠ A := (ne_of_not_collinear hnd).2.2
lemma c_ne_a : C ≠ A := (ne_of_not_collinear hnd).2.1.symm
lemma B_ne_C : B ≠ C := (ne_of_not_collinear hnd).1.symm
--∠ A C B = π/2
variable {hrt : (ANG A C B c_ne_a.symm B_ne_C).IsRightAngle}
-- D is the midpoint of segment AB
variable {D : P} {hd : D = (SEG A B).midpoint}
lemma d_ne_a: D ≠ A := by
  rw[hd]
  apply (SegND.midpt_lies_int (SegND := SegND A B (b_ne_a).symm)).2.1
  use C
  by_contra h
  have : Collinear A B C :=by
    apply Collinear.perm₂₁₃ h
  trivial
--Introduce the midpoint E of AC
variable {E : P} {he : E=  (SEG A C).midpoint}
lemma e_ne_a: E ≠ A := by
  rw[he]
  apply (SegND.midpt_lies_int (SegND := SegND A C c_ne_a)).2.1
  use B
  exact hnd
lemma e_ne_C: E ≠ C := by
  rw[he]
  apply (SegND.midpt_lies_int (SegND := SegND A C c_ne_a)).2.2
  use B
  exact hnd
--midpoint lies on the segment
lemma adb_collinear : Collinear A D B := by
  apply collinear_of_vec_eq_smul_vec'
  use 2
  simp only [hd,Seg.midpoint,one_div, seg_toVec_eq_vec, vec_of_pt_vadd_pt_eq_vec,smul_smul]
  norm_num
lemma aec_collinear : Collinear A E C := by
  apply collinear_of_vec_eq_smul_vec'
  use 2
  simp only [he,Seg.midpoint,one_div, seg_toVec_eq_vec, vec_of_pt_vadd_pt_eq_vec,smul_smul]
  norm_num

lemma midpt_half_length : (SEG A D).length = (SEG A B).length/2:=by
  rw[length_eq_length_add_length (seg:= SEG A B) (A := D),← dist_target_eq_dist_source_of_eq_midpt,half_add_self]
  exact hd
  rw[hd]
  exact Seg.midpt_lies_on

lemma ad_ratio : (SEG A D).length / (SEG A B).length = 2⁻¹ := by
  apply div_eq_of_eq_mul
  apply (length_ne_zero_iff_nd.mpr (B_ne_a)).symm
  use C
  exact hnd
  rw[length_eq_length_add_length (seg := (SEG A B)) (A := D),← dist_target_eq_dist_source_of_eq_midpt]
  simp only [Seg.source,←mul_two,mul_comm,←mul_assoc,ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel, one_mul]
  exact hd
  rw[hd]
  apply Seg.midpt_lies_on
lemma ae_ratio : (SEG A E).length / (SEG A C).length = 2⁻¹ :=by
  apply div_eq_of_eq_mul
  apply (length_ne_zero_iff_nd.mpr (c_ne_a)).symm
  use B
  exact hnd
  rw[length_eq_length_add_length (seg := SEG A C) (A := E),← dist_target_eq_dist_source_of_eq_midpt]
  simp only [Seg.source,←mul_two,mul_comm,←mul_assoc,ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel, one_mul]
  exact he
  rw[he]
  apply Seg.midpt_lies_on

lemma hnd': ¬ Collinear A D E := by
  intro h'
  have : Collinear A B E := by
    apply collinear_of_collinear_collinear_ne adb_collinear h' d_ne_a
    exact hd
    use B
    use C
    exact hnd
    exact hd
  have neghnd : Collinear A B C := by
    apply collinear_of_collinear_collinear_ne (Collinear.perm₁₃₂ this) aec_collinear e_ne_a
    exact he
    use B
    use C
    exact hnd
    exact he
  apply hnd neghnd
lemma hnd'' : ¬ Collinear C D E := by
  intro h
  have : Collinear C D A := by
    apply Collinear.perm₁₃₂
    apply collinear_of_collinear_collinear_ne
    apply (Collinear.perm₁₃₂ (Collinear.perm₂₁₃ (Collinear.perm₁₃₂ aec_collinear)))
    use E
    exact he
    apply Collinear.perm₁₃₂ h
    apply e_ne_C
    apply hnd
    exact he
  have : Collinear A B C := by
    apply collinear_of_collinear_collinear_ne
    apply adb_collinear
    apply hd
    apply (Collinear.perm₁₃₂ (Collinear.perm₂₁₃ (Collinear.perm₁₃₂ this)))
    apply d_ne_a
    apply hnd
    exact hd
  apply hnd this
lemma ade_sim_abc: TRI_nd A D E (@hnd' P _ A B C hnd D hd E he) ∼ TRI_nd A B C hnd := by
  let tri_nd_ADE := TRI_nd A D E (@hnd' P _ A B C hnd D hd E he)
  let tri_nd_ABC := TRI_nd A B C hnd
  apply sim_of_SAS
  simp only [TriangleND.edge₂,TriangleND.edge₃, Triangle.edge₂,Triangle.edge₃]
  have tr13: tri_nd_ADE.1.point₃=E:= rfl
  have tr23: tri_nd_ABC.1.point₃ =C:= rfl
  have tr11: tri_nd_ADE.1.point₁=A:= rfl
  have tr21: tri_nd_ABC.1.point₁ =A:= rfl
  have tr12: tri_nd_ADE.1.point₂=D:= rfl
  have tr22: tri_nd_ABC.1.point₂ =B := rfl
  rw [tr13, tr12, tr11, tr23, tr22, tr21, ← Seg.length_of_rev_eq_length, ← (SEG C A).length_of_rev_eq_length]
  simp only [Seg.reverse]
  rw[ae_ratio,ad_ratio]
  use C
  exact hnd
  exact hd
  use B
  exact hnd
  exact he
--rays equal, respectively
  congr 1
  apply Angle.ext
  have h₀:(TRI_nd A D E (@hnd' P _ A B C hnd D hd E he)).angle₁.1=(SegND A D (@d_ne_a P _ A B C hnd D hd)).toRay := rfl
  rw[h₀]
  have h₁:(TRI_nd A B C hnd).angle₁.1=(SegND A B (@b_ne_a P _ A B C hnd)).toRay:=rfl
  rw[h₁]
  apply @Ray.source_int_toRay_eq_ray P _ (SegND A B (@b_ne_a P _ A B C hnd)).toRay
  apply SegND.lies_int_toRay_of_lies_int
  apply (Seg.lies_int_iff).mpr
  constructor
  exact (@b_ne_a P _ A B C hnd)
  use 1/2
  norm_num
  simp only [Seg.toVec,hd]
  apply Seg.vec_source_midpt
  have h₂:(TRI_nd A D E (@hnd' P _ A B C hnd D hd E he)).angle₁.2=(SegND A E (@e_ne_a P _ A B C hnd E he)).toRay := rfl
  rw[h₂]
  have h₃:(TRI_nd A B C hnd).angle₁.2=(SegND A C (@c_ne_a P _ A B C hnd)).toRay:=rfl
  rw[h₃]
  apply @Ray.source_int_toRay_eq_ray P _ (SegND A C (@c_ne_a P _ A B C hnd)).toRay
  apply SegND.lies_int_toRay_of_lies_int
  apply (Seg.lies_int_iff).mpr
  constructor
  exact (@c_ne_a P _ A B C hnd)
  use 1/2
  norm_num
  simp only [Seg.toVec,he]
  apply Seg.vec_source_midpt

lemma ade_acongr_cde : (TRI_nd A D E (@hnd' P _ A B C hnd D hd E he)) ≅ₐ (TRI_nd C D E (@hnd'' P _ A B C hnd D hd E he)) := sorry
  --need to define the value of right angle
  --by_SAS (acongr)

lemma cd : (TRI C D E).edge₃.length = (SEG C D).length:=by
  simp only [Triangle.edge₃]
lemma ad : (TRI A D E).edge₃.length = (SEG A D).length:=by
  simp only [Triangle.edge₃]
lemma ad_eq_cd: (SEG A D).length = (SEG C D).length  := by
    rw[← cd,←ad]
    apply ade_acongr_cde.edge₃
    trivial
    use E
    use B
    unfold Seg.source Triangle.edge₃
    simp only
    exact hnd
    unfold Seg.target Seg.source Triangle.edge₃
    simp only
    exact hd
    unfold Seg.source Triangle.edge₃
    simp only
    exact he

-- Theorem : $CD = AB / 2$
theorem Shan_Problem_1_7 : (SEG C D).length = (SEG A B).length/2 := by
  rw[←ad_eq_cd]
  apply midpt_half_length
  exact hd
  use B
  apply hnd
  apply hd
  use E
  exact he
end Shan_Problem_1_7

namespace Shan_Problem_1_8
/- In $\triangle ABC$, let $BD$ and $CE$ be the heights, with foots $D$ and $E$, respectively. Let $F$ and $G$ be the midpoint of $BC$ and $DE$, respectively.

Prove that $FG \perp DE$. -/
variable {A B C : P} {hnd : ¬ Collinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma A_ne_B : A ≠ B := sorry
lemma B_ne_C : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
--introduce the perps
variable {D : P} {hd : D = perp_foot B (LIN A C c_ne_a)}
variable {E : P} {he : E = perp_foot C (LIN A B A_ne_B.symm)}
variable {F G: P} {hf : F = (SEG B C).midpoint} {hg : G = (SEG D E).midpoint}
lemma e_ne_d: E ≠ D := sorry
lemma g_ne_f: G ≠ F := sorry
--Failed to use the notation ⟂

-- Theorem : $FG \perp DE$
theorem Shan_Problem_1_8 : (SegND F G g_ne_f) ⟂ (SegND D E e_ne_d) := sorry

end Shan_Problem_1_8
