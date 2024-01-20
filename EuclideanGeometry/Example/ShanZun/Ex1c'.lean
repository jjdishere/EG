import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom
namespace ShanZun

namespace Shan_Problem_1_7

/- In $\triangle ABC$, $\angle ACB = \pi /2$. Let $D$ be the midpoint of $AB$.

Prove that $CD = AB / 2$. -/

structure Setting (Plane : Type*) [EuclideanPlane Plane] where
  -- Let $\triangle ABC$ be a nontrivial triangle in which $\angle ACB= \pi/2$.
  A : Plane
  B : Plane
  C : Plane
  not_collinear_ABC : ¬ Collinear A B C
  -- Claim :$C \ne A$
  C_ne_A : C ≠ A :=
    -- This is because vertices $A, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.1.symm
  -- Claim $B \ne C$
  B_ne_C : B ≠ C :=
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).1.symm
  B_ne_A : B ≠ A :=
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.2
  --Let $D$ be the midpoint of $AB$
  hrt: (ANG A C B C_ne_A.symm B_ne_C).IsRightAngle
  D : Plane
  hD : D = (SEG A B).midpoint

theorem result {Plane : Type*} [EuclideanPlane Plane] (e : Setting Plane) : (SEG e.C e.D).length = (SEG e.A e.B).length/2 := by
  have D_ne_A: e.D ≠ e.A := by
    rw[e.hD]
    apply (SegND.midpt_lies_int (seg_nd := SEG_nd e.A e.B (e.B_ne_A))).2.1
  --Introduce the midpoint E of AC
  let E : Plane := (SEG e.A e.C).midpoint
  have hE: E = (SEG e.A e.C).midpoint := rfl

  --Claim: $E\neq A$
  have E_ne_A : E ≠ e.A := by
    rw[hE]
    apply (SegND.midpt_lies_int (seg_nd := SEG_nd e.A e.C e.C_ne_A)).2.1
  --Claim: $E\neq C$
  have E_ne_C: E ≠ e.C := by
    rw[hE]
    apply (SegND.midpt_lies_int (seg_nd := SEG_nd e.A e.C e.C_ne_A)).2.2
  --midpoint lies on the segment
  have adb_collinear : Collinear e.A e.D e.B := by
    apply collinear_of_vec_eq_smul_vec'
    use 2
    simp only [e.hD,Seg.midpoint,one_div, seg_toVec_eq_vec, vec_of_pt_vadd_pt_eq_vec,smul_smul]
    norm_num
  have aec_collinear : Collinear e.A E e.C := by
    apply collinear_of_vec_eq_smul_vec'
    use 2
    simp only [hE,Seg.midpoint,one_div, seg_toVec_eq_vec, vec_of_pt_vadd_pt_eq_vec,smul_smul]
    norm_num
  have midpt_half_length : (SEG e.A e.D).length = (SEG e.A e.B).length/2:=by
    rw[length_eq_length_add_length (seg:= SEG e.A e.B) (A := e.D),← dist_target_eq_dist_source_of_eq_midpt,half_add_self]
    exact e.hD
    rw[e.hD]
    exact Seg.midpt_lies_on

  have ad_ratio : (SEG e.A e.D).length / (SEG e.A e.B).length = 2⁻¹ := by
    apply div_eq_of_eq_mul
    symm
    apply length_ne_zero_iff_nd.mpr
    exact e.B_ne_A
    rw[length_eq_length_add_length (seg := (SEG e.A e.B)) (A := e.D),← dist_target_eq_dist_source_of_eq_midpt]
    simp only [Seg.source,←mul_two,mul_comm,←mul_assoc,ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel, one_mul]
    exact e.hD
    rw[e.hD]
    apply Seg.midpt_lies_on
  have ae_ratio : (SEG e.A E).length / (SEG e.A e.C).length = 2⁻¹ :=by
    apply div_eq_of_eq_mul
    symm
    apply length_ne_zero_iff_nd.mpr
    exact e.C_ne_A
    rw[length_eq_length_add_length (seg := SEG e.A e.C) (A := E),← dist_target_eq_dist_source_of_eq_midpt]
    simp only [Seg.source,←mul_two,mul_comm,←mul_assoc,ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel, one_mul]
    exact hE
    rw[hE]
    apply Seg.midpt_lies_on
  have not_collinear_ADE: ¬ Collinear e.A e.D E := by
    intro h'
    have : Collinear e.A e.B E := by
      apply collinear_of_collinear_collinear_ne adb_collinear h' D_ne_A
    have neghnd : Collinear e.A e.B e.C := by
      apply collinear_of_collinear_collinear_ne (Collinear.perm₁₃₂ this) aec_collinear E_ne_A
    exact e.not_collinear_ABC neghnd
  have not_collinear_CDE : ¬ Collinear e.C e.D E := by
    intro h
    have : Collinear e.C e.D e.A := by
      apply Collinear.perm₁₃₂
      apply collinear_of_collinear_collinear_ne
      apply (Collinear.perm₁₃₂ (Collinear.perm₂₁₃ (Collinear.perm₁₃₂ aec_collinear)))
      apply Collinear.perm₁₃₂ h
      apply E_ne_C
    have : Collinear e.A e.B e.C := by
      apply collinear_of_collinear_collinear_ne
      apply adb_collinear
      -- apply e.hD
      apply (Collinear.perm₁₃₂ (Collinear.perm₂₁₃ (Collinear.perm₁₃₂ this)))
      apply D_ne_A
    apply e.not_collinear_ABC this

  have ADE_sim_ABC: TRI_nd e.A e.D E not_collinear_ADE ∼ TRI_nd e.A e.B e.C e.not_collinear_ABC := by
    let tri_nd_ADE := TRI_nd e.A e.D E not_collinear_ADE
    let tri_nd_ABC := TRI_nd e.A e.B e.C e.not_collinear_ABC
    apply sim_of_SAS
    simp only [TriangleND.edge₂,TriangleND.edge₃, Triangle.edge₂,Triangle.edge₃]
    have tr13: tri_nd_ADE.1.point₃=E:= rfl
    have tr23: tri_nd_ABC.1.point₃ = e.C:= rfl
    have tr11: tri_nd_ADE.1.point₁= e.A:= rfl
    have tr21: tri_nd_ABC.1.point₁ = e.A:= rfl
    have tr12: tri_nd_ADE.1.point₂= e.D := rfl
    have tr22: tri_nd_ABC.1.point₂ = e.B := rfl
    rw [tr13, tr12, tr11, tr23, tr22, tr21, ← Seg.length_of_rev_eq_length, ← (SEG e.C e.A).length_of_rev_eq_length]
    simp only [Seg.reverse]
    rw[ae_ratio,ad_ratio]
  --rays equal, respectively
    congr 1
    apply Angle.ext
    have h₀ :(TRI_nd e.A e.D E not_collinear_ADE).angle₁.1=(SEG_nd e.A e.D (D_ne_A)).toRay := rfl
    rw[h₀]
    have h₁:(TRI_nd e.A e.B e.C e.not_collinear_ABC).angle₁.1=(SEG_nd e.A e.B (e.B_ne_A)).toRay:=rfl
    rw[h₁]
    apply @Ray.source_int_toRay_eq_ray Plane _ (SEG_nd e.A e.B (e.B_ne_A)).toRay
    apply SegND.lies_int_toRay_of_lies_int
    apply (Seg.lies_int_iff).mpr
    constructor
    exact e.B_ne_A
    use 1/2
    norm_num
    simp only [Seg.toVec,e.hD]
    apply Seg.vec_source_midpt
    have h₂:(TRI_nd e.A e.D E (not_collinear_ADE)).angle₁.2=(SEG_nd e.A E (E_ne_A)).toRay := rfl
    rw[h₂]
    have h₃:(TRI_nd e.A e.B e.C e.not_collinear_ABC).angle₁.2=(SEG_nd e.A e.C (e.C_ne_A)).toRay:=rfl
    rw[h₃]
    apply @Ray.source_int_toRay_eq_ray Plane _ (SEG_nd e.A e.C (e.C_ne_A)).toRay
    apply SegND.lies_int_toRay_of_lies_int
    apply (Seg.lies_int_iff).mpr
    constructor
    exact e.C_ne_A
    use 1/2
    norm_num
    simp only [Seg.toVec,hE]
    apply Seg.vec_source_midpt

  have ade_acongr_cde : (TRI_nd e.A e.D E (not_collinear_ADE)) ≅ₐ (TRI_nd e.C e.D E (not_collinear_CDE)) := sorry
    --need to define the value of right angle
    --by_SAS (acongr)

  have cd : (TRI e.C e.D E).edge₃.length = (SEG e.C e.D).length:=by
    simp only [Triangle.edge₃]
  have ad : (TRI e.A e.D E).edge₃.length = (SEG e.A e.D).length:=by
    simp only [Triangle.edge₃]
  have ad_eq_cd: (SEG e.A e.D).length = (SEG e.C e.D).length  := by
    rw[← cd,←ad]
    apply ade_acongr_cde.edge₃
-- Theorem : $CD = AB / 2$
  rw[←ad_eq_cd]
  apply midpt_half_length

end Shan_Problem_1_7


namespace Shan_Problem_1_8

/- In $\triangle ABC$, let $BD$ and $CE$ be the heights, with foots $D$ and $E$, respectively. Let $F$ and $G$ be the midpoint of $BC$ and $DE$, respectively.

Prove that $FG \perp DE$. -/

structure Setting (Plane : Type*) [EuclideanPlane Plane] where
  -- Let $\triangle ABC$ be a nontrivial triangle in which $\angle ACB= \pi/2$.
  A : Plane
  B : Plane
  C : Plane
  not_collinear_ABC : ¬ Collinear A B C
  -- Claim :$C \ne A$
  C_ne_A : C ≠ A :=
    -- This is because vertices $A, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.1.symm
  -- Claim $B \ne C$
  B_ne_C : B ≠ C :=
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).1.symm
  B_ne_A : B ≠ A :=
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.2
  --Let $D$ be the perpendicular foot from $B$ to $AC$
  D : Plane
  hD : D = perp_foot B (LIN A C C_ne_A)
  --Let $E$ be the perpendicular foot from $C$ to $AB$
  E : Plane
  hE : E = perp_foot C (LIN A B B_ne_A)
  --$F$ is the midpoint of $BC$
  F : Plane
  hF : F = (SEG B C).midpoint
  --$G$ is the midpoint of $DE$
  G : Plane
  hG : G = (SEG D E).midpoint
  G_ne_F : G ≠ F := sorry
  E_ne_D : E ≠ D := sorry

-- Theorem : $FG \perp DE$
theorem result {Plane : Type*} [EuclideanPlane Plane] (e : Setting Plane) :(SEG_nd e.F e.G e.G_ne_F) ⟂ (SEG_nd e.D e.E e.E_ne_D) := sorry

end Shan_Problem_1_8

end ShanZun
end EuclidGeom
