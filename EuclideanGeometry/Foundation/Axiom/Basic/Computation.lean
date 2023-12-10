import EuclideanGeometry.Foundation.Axiom.Basic.Vector

-- Our aim is to prove the Cosine value of the angle of two Vec_nd-s, their norm and inner product satisfy THE EQUALITY. We will use this to prove the Cosine theorem of Triangle, which is in the file Trigonometric

noncomputable section

namespace EuclidGeom
open scoped Real

section Cosine_theorem_for_VecND

theorem cos_angle_of_dir_dir_eq_inner (d₁ d₂ : Dir) : (d₂ -ᵥ d₁).cos = ⟪d₁.unitVec, d₂.unitVec⟫_ℝ := by
  sorry

theorem norm_mul_norm_mul_cos_angle_eq_inner_of_VecND (v₁ v₂ : VecND) : ‖v₁‖ * ‖v₂‖ * (VecND.angle v₁ v₂).cos = ⟪v₁.1, v₂.1⟫_ℝ := by
  have h : ⟪v₁.1, v₂.1⟫_ℝ = ⟪‖v₁‖ • v₁.toDir.unitVec, ‖v₂‖ • v₂.toDir.unitVec⟫_ℝ := by simp
  rw [h]
  rw [inner_smul_left, inner_smul_right, ← cos_angle_of_dir_dir_eq_inner, mul_assoc]
  rfl

theorem perp_iff_angle_eq_pi_div_two_or_angle_eq_neg_pi_div_two (d₁ d₂ : Dir) :
    d₁.toProj = d₂.toProj.perp ↔ d₁ = (↑(π / 2) : AngValue) +ᵥ d₂ ∨ d₁ = (↑(-π / 2) : AngValue) +ᵥ d₂ := by
  apply Dir.toProj_eq_toProj_iff.trans
  rw [id_eq, Dir.rotate_eq_vadd]
  apply or_congr Iff.rfl
  rw [← Dir.pi_vadd, vadd_vadd]
  apply iff_of_eq
  congr
  norm_cast
  rw [AngValue.eq_iff_two_pi_dvd_sub]
  use 1
  ring

end Cosine_theorem_for_VecND

section Linear_Algebra

theorem det_eq_sin_mul_norm_mul_norm' (u v : Dir) : Vec.det u.unitVec v.unitVec = (v -ᵥ u).sin := by
  sorry
  /-
  rw [det_eq_im_of_quotient]
  unfold Dir.AngDiff
  rw [sin_arg_of_dir_eq_fst]
  rfl-/

theorem det_eq_sin_mul_norm_mul_norm (u v : VecND): Vec.det u.1 v.1 = (VecND.angle u v).sin * ‖u‖ * ‖v‖ := by
  sorry
  /-
  let nu := u.toDir
  let nv := v.toDir
  let unorm := u.norm
  let vnorm := v.norm
  have hu : u.1 = u.norm • nu.1 := by simp only [ne_eq, Vec_nd.norm_smul_todir_eq_self]
  have hv : v.1 = v.norm • nv.1 := by simp only [ne_eq, Vec_nd.norm_smul_todir_eq_self]
  rw [hu, hv, det_smul_left_eq_mul_det, det_smul_right_eq_mul_det]
  have unorm_nonneg : 0 ≤ unorm := Vec.norm_nonnegative u
  have vnorm_nonneg : 0 ≤ vnorm := Vec.norm_nonnegative v
  rw [Vec.norm_smul_eq_mul_norm (unorm_nonneg), Vec.norm_smul_eq_mul_norm (vnorm_nonneg)]
  have : det nu.1 nv.1 = sin (Vec_nd.angle u v) * Vec.norm nu.1 *Vec.norm nv.1 := by
    rw[Dir.norm_of_dir_tovec_eq_one, Dir.norm_of_dir_tovec_eq_one, mul_one, mul_one, det_eq_sin_mul_norm_mul_norm']
    unfold Vec_nd.angle
    rfl
  rw[this]
  ring
  -/

end Linear_Algebra

end EuclidGeom
