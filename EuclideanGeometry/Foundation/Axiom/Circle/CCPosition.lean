import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

section CC

namespace Circle

protected def IsSeparated (ω₁ : Circle P) (ω₂ : Circle P) : Prop := dist ω₁.center ω₂.center > ω₁.radius + ω₂.radius

protected def IsIntersected (ω₁ : Circle P) (ω₂ : Circle P) : Prop := (dist ω₁.center ω₂.center < ω₁.radius + ω₂.radius) ∧ (dist ω₁.center ω₂.center > abs (ω₂.radius - ω₁.radius))

protected def IsCircumscribed (ω₁ : Circle P) (ω₂ : Circle P) : Prop := dist ω₁.center ω₂.center = ω₁.radius + ω₂.radius

/- put the smaller circle first -/
protected def IsIncluded (ω₁ : Circle P) (ω₂ : Circle P) : Prop := dist ω₁.center ω₂.center < ω₂.radius - ω₁.radius

/- put the smaller circle first -/
protected def IsInscribed (ω₁ : Circle P) (ω₂ : Circle P) : Prop := (dist ω₁.center ω₂.center = ω₂.radius - ω₁.radius) ∧ (ω₁.center ≠ ω₂.center)

end Circle

scoped infix : 50 "Separate" => Circle.IsSeparated
scoped infix : 50 "Intersect" => Circle.IsIntersected
scoped infix : 50 "Circumscribe" => Circle.IsCircumscribed
scoped infix : 50 "IncludeIn" => Circle.IsIncluded
scoped infix : 50 "InscribeIn" => Circle.IsInscribed

namespace Circle

theorem CC_separated_symm (ω₁ : Circle P) (ω₂ : Circle P) : ω₁ Separate ω₂ ↔ ω₂ Separate ω₁ := by
  have : dist ω₁.center ω₂.center = dist ω₂.center ω₁.center := dist_comm _ _
  constructor
  · unfold Circle.IsSeparated
    intro h
    rw [← this, add_comm]
    exact h
  unfold Circle.IsSeparated
  intro h
  rw [this, add_comm]
  exact h

theorem CC_separated_pt_outside_second_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ Separate ω₂) (h₂ : A LiesOn ω₁) : A LiesOut ω₂ := by
  have : dist ω₂.center A + dist ω₁.center A ≥ dist ω₁.center ω₂.center := by
    rw [add_comm]
    apply dist_triangle_right
  have hh₁ : dist ω₁.center A = ω₁.radius := by
    have : Circle.IsOn A ω₁ := h₂
    unfold Circle.IsOn at this
    exact this
  have hh₂ : dist ω₁.center ω₂.center > ω₁.radius + ω₂.radius := by
    unfold Circle.IsSeparated at h₁
    exact h₁
  have : dist ω₂.center A > ω₂.radius := by linarith
  unfold Circle.IsOutside
  exact this

theorem CC_separated_pt_outside_first_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ Separate ω₂) (h₂ : A LiesOn ω₂) : A LiesOut ω₁ := CC_separated_pt_outside_second_circle ((CC_separated_symm ω₁ ω₂).mp h₁) h₂


lemma CC_Circumscribe_centers_distinct {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Circumscribe ω₂) : ω₁.center ≠ ω₂.center := by
  have r₁pos : ω₁.radius > 0 := ω₁.rad_pos
  have r₂pos : ω₂.radius > 0 := ω₂.rad_pos
  have : dist ω₁.center ω₂.center > 0 := by
    calc
      _ = ω₁.radius + ω₂.radius := h
      _ > 0 := by linarith
  apply dist_pos.mp this

def CC_Circumscribe_Point {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Circumscribe ω₂) : P := (ω₁.radius • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.unitVec) +ᵥ ω₁.center

theorem CC_circumscribe_point_lieson_circles {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Circumscribe ω₂) : ((CC_Circumscribe_Point h) LiesOn ω₁) ∧ ((CC_Circumscribe_Point h) LiesOn ω₂) := by
  constructor
  · have : dist ω₁.center (CC_Circumscribe_Point h) = ω₁.radius := by
      calc
        _ = ‖(CC_Circumscribe_Point h) -ᵥ ω₁.center‖ := by
          rw [dist_comm, NormedAddTorsor.dist_eq_norm']
        _ = ‖ω₁.radius • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.unitVec‖ := by
          unfold CC_Circumscribe_Point
          simp
        _ = ‖ω₁.radius • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.unitVec‖ := rfl
        _ = ω₁.radius := by
          rw [norm_smul, Dir.norm_unitVec, mul_one, Real.norm_of_nonneg ω₁.rad_pos.le]
    show Circle.IsOn (CC_Circumscribe_Point h) ω₁
    exact this
  have : dist ω₂.center (CC_Circumscribe_Point h) = ω₂.radius := by
    calc
      _ = ‖VEC (CC_Circumscribe_Point h) ω₂.center‖ := by rw [NormedAddTorsor.dist_eq_norm']; rfl
      _ = ‖VEC ω₁.center ω₂.center - VEC ω₁.center (CC_Circumscribe_Point h)‖ := by rw [vec_sub_vec]
      _ = ‖VEC ω₁.center ω₂.center - ω₁.radius • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.unitVec‖ := by
        unfold CC_Circumscribe_Point Vec.mkPtPt
        rw [vadd_vsub]
      _ = ‖(VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).1 - ω₁.radius • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.unitVec‖ := rfl
      _ = ‖(‖VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm‖ - ω₁.radius) • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.unitVec‖ := by
        rw [sub_smul, VecND.norm_smul_toDir_unitVec]
      _ = ‖(dist ω₁.center ω₂.center - ω₁.radius) • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.unitVec‖ := by
        rw [dist_comm, NormedAddTorsor.dist_eq_norm']
        rfl
      _ = ‖ω₂.radius • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.unitVec‖ := by
        rw [h, add_comm, add_sub_cancel]
      _ = ω₂.radius := by
          rw [norm_smul, Dir.norm_unitVec, mul_one, Real.norm_of_nonneg ω₂.rad_pos.le]
  show Circle.IsOn (CC_Circumscribe_Point h) ω₂
  exact this

theorem CC_circumscribe_point_centers_colinear {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Circumscribe ω₂) : colinear ω₁.center (CC_Circumscribe_Point h) ω₂.center := by
  have : VEC ω₁.center (CC_Circumscribe_Point h) = (ω₁.radius * ‖VEC ω₁.center ω₂.center‖⁻¹) • (VEC ω₁.center ω₂.center) := by
    calc
      _ = ω₁.radius • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.unitVec := by
        unfold CC_Circumscribe_Point
        simp
      _ = ω₁.radius • (‖VEC ω₁.center ω₂.center‖⁻¹ • (VEC ω₁.center ω₂.center)) := rfl
      _ = (ω₁.radius * ‖VEC ω₁.center ω₂.center‖⁻¹) • (VEC ω₁.center ω₂.center) := by apply smul_smul
  apply flip_colinear_snd_trd (colinear_of_vec_eq_smul_vec this)


theorem CC_inscribed_pt_inside_second_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ InscribeIn ω₂) (h₂ : A LiesOn ω₁) : A LiesIn ω₂ := by
  have : dist ω₂.center A ≤ ω₂.radius := by
    calc
      _ ≤ dist ω₁.center ω₂.center + dist ω₁.center A := by apply dist_triangle_left
      _ = (ω₂.radius - ω₁.radius) + ω₁.radius := by rw [h₁.1, h₂]
      _ = ω₂.radius := by linarith
  exact this

def CC_Inscribe_Point {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ InscribeIn ω₂) : P := (ω₁.radius • (VEC_nd ω₂.center ω₁.center h.2).toDir.unitVec) +ᵥ ω₁.center

theorem CC_inscribe_point_lieson_circles {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ InscribeIn ω₂) : ((CC_Inscribe_Point h) LiesOn ω₁) ∧ ((CC_Inscribe_Point h) LiesOn ω₂) := by
  constructor
  · have : dist ω₁.center (CC_Inscribe_Point h) = ω₁.radius := by
      calc
        _ = ‖(CC_Inscribe_Point h) -ᵥ ω₁.center‖ := by rw [dist_comm, NormedAddTorsor.dist_eq_norm']
        _ = norm (ω₁.radius • (VEC_nd ω₂.center ω₁.center h.2).toDir.unitVec) := by
          unfold CC_Inscribe_Point
          simp
        _ = ‖ω₁.radius • (VEC_nd ω₂.center ω₁.center h.2).toDir.unitVec‖ := rfl
        _ = ω₁.radius := by
          rw [norm_smul, Dir.norm_unitVec, mul_one, Real.norm_of_nonneg ω₁.rad_pos.le]
    show Circle.IsOn (CC_Inscribe_Point h) ω₁
    exact this
  have : dist ω₂.center (CC_Inscribe_Point h) = ω₂.radius := by
    calc
      _ = ‖VEC (CC_Inscribe_Point h) ω₂.center‖ := by
        rw [NormedAddTorsor.dist_eq_norm']; rfl
      _ = ‖VEC ω₁.center ω₂.center - VEC ω₁.center (CC_Inscribe_Point h)‖ := by rw [vec_sub_vec]
      _ = ‖VEC ω₁.center ω₂.center - ω₁.radius • (VEC_nd ω₂.center ω₁.center h.2).toDir.unitVec‖ := by
        unfold CC_Inscribe_Point Vec.mkPtPt
        rw [vadd_vsub]
      _ = ‖(VEC_nd ω₁.center ω₂.center h.2.symm).1 - ω₁.radius • (VEC_nd ω₂.center ω₁.center h.2).toDir.unitVec‖ := rfl
      _ = ‖(VEC_nd ω₁.center ω₂.center h.2.symm).1 + ω₁.radius • (VEC_nd ω₁.center ω₂.center h.2.symm).toDir.unitVec‖ := by
        unfold Dir.unitVec Dir.unitVecND VecND.toDir VecND.mkPtPt
        simp
        rw [sub_eq_add_neg, ← smul_neg, ← smul_neg]
        congr 4
        · simp [← VecND.norm_coe] -- note: there should be a simp lemma `VecND.norm_mk`
        · rw [neg_vec]
      _ = ‖(‖VEC_nd ω₁.center ω₂.center h.2.symm‖ + ω₁.radius) • (VEC_nd ω₁.center ω₂.center h.2.symm).toDir.unitVec‖ := by
        rw [add_smul, VecND.norm_smul_toDir_unitVec]
      _ = ‖(dist ω₁.center ω₂.center + ω₁.radius) • (VEC_nd ω₁.center ω₂.center h.2.symm).toDir.unitVec‖ := by
        congr
        apply Eq.trans _ (dist_comm _ _) -- note: why cannot rw?
        apply Eq.trans _ (NormedAddTorsor.dist_eq_norm' _ _).symm
        rfl
      _ = ‖ω₂.radius • (VEC_nd ω₁.center ω₂.center h.2.symm).toDir.unitVec‖ := by
        congr; rw [h.1]; linarith
      _ = ω₂.radius := by
          rw [norm_smul, Dir.norm_unitVec, mul_one, Real.norm_of_nonneg ω₂.rad_pos.le] -- note: 我不知道这行出现多少次了，不要复制粘贴，写点lemma
  show Circle.IsOn (CC_Inscribe_Point h) ω₂
  exact this

theorem CC_inscribe_point_centers_colinear {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ InscribeIn ω₂) : colinear ω₁.center ω₂.center (CC_Inscribe_Point h) := by
  have : VEC ω₁.center (CC_Inscribe_Point h) = (- ω₁.radius * ‖(VEC ω₁.center ω₂.center)‖⁻¹) • VEC ω₁.center ω₂.center := by
    calc
      _ = ω₁.radius • (VEC_nd ω₂.center ω₁.center h.2).toDir.unitVec := by
        unfold CC_Inscribe_Point
        simp
      _ = ω₁.radius • (- (VEC_nd ω₁.center ω₂.center h.2.symm).toDir.unitVec) := by
        -- note: 为什么没有 neg_vecND
        trans ω₁.radius • (-VEC_nd ω₁.center ω₂.center h.2.symm).toDir.unitVec
        · unfold VecND.mkPtPt Vec.mkPtPt
          congr
          rw [← neg_eq_iff_eq_neg, neg_vsub_eq_vsub_rev]
        · simp
      _ = - ω₁.radius • (VEC_nd ω₁.center ω₂.center h.2.symm).toDir.unitVec := by
        rw [smul_neg, neg_smul]
      _ = (- ω₁.radius) • ‖VEC ω₁.center ω₂.center‖⁻¹ • VEC ω₁.center ω₂.center := rfl
      _ = (- ω₁.radius * ‖VEC ω₁.center ω₂.center‖⁻¹) • VEC ω₁.center ω₂.center := by apply smul_smul
  apply colinear_of_vec_eq_smul_vec this


theorem CC_included_pt_isint_second_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ IncludeIn ω₂) (h₂ : A LiesOn ω₁) : Circle.IsInt A ω₂ := by
  have : dist ω₂.center A < ω₂.radius := by
    calc
      _ ≤ dist ω₁.center ω₂.center + dist ω₁.center A := by apply dist_triangle_left
      _ = dist ω₁.center ω₂.center + ω₁.radius := by rw [h₂]
      _ < (ω₂.radius - ω₁.radius) + ω₁.radius := by apply add_lt_add_right h₁
      _ = ω₂.radius := by linarith
  exact this

theorem CC_included_pt_outside_first_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ IncludeIn ω₂) (h₂ : A LiesOn ω₂) : A LiesOut ω₁ := by
  have : dist ω₁.center A + dist ω₁.center ω₂.center ≥ dist ω₂.center A := by
    rw [dist_comm ω₂.center A]
    apply dist_triangle_left
  have : dist ω₁.center ω₂.center < ω₂.radius - ω₁.radius := h₁
  have : dist ω₁.center A > ω₁.radius := by
    calc
      _ ≥ dist ω₂.center A - dist ω₁.center ω₂.center := by linarith
      _ = ω₂.radius - dist ω₁.center ω₂.center := by rw [h₂]
      _ > ω₂.radius - (ω₂.radius - ω₁.radius) := by linarith
      _ = ω₁.radius := by linarith
  exact this


lemma CC_intersected_centers_distinct {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : ω₁.center ≠ ω₂.center := by
  apply dist_pos.mp
  have : dist ω₁.center ω₂.center > abs (ω₂.radius - ω₁.radius) := h.2
  have : abs (ω₂.radius - ω₁.radius) ≥ 0 := by apply abs_nonneg
  linarith

@[ext]
structure CCInxpts (P : Type _) [EuclideanPlane P] where
  left : P
  right : P

/- the following dist has a direction, depending on (VEC O₁ O₂) -/
def radical_axis_dist_to_the_first (ω₁ : Circle P) (ω₂ : Circle P) : ℝ := (ω₁.radius ^ 2 + (dist ω₁.center ω₂.center) ^ 2 - ω₂.radius ^ 2) / (2 * (dist ω₁.center ω₂.center))

lemma radical_axis_dist_lt_radius {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : abs (radical_axis_dist_to_the_first ω₁ ω₂) < ω₁.radius := by
  have dpos : 0 < dist ω₁.center ω₂.center := by apply dist_pos.mpr (CC_intersected_centers_distinct h)
  by_cases h₁ : radical_axis_dist_to_the_first ω₁ ω₂ > 0
  · rw [abs_of_pos h₁]
    unfold radical_axis_dist_to_the_first
    apply (div_lt_iff' _).mpr
    apply sub_lt_iff_lt_add'.mpr
    apply sub_lt_iff_lt_add.mp
    rw [mul_right_comm, ← sub_sq']
    apply sq_lt_sq'
    have : dist ω₁.center ω₂.center < ω₁.radius + ω₂.radius := h.1
    linarith
    apply sub_lt_iff_lt_add'.mpr
    apply sub_lt_iff_lt_add.mp
    calc
      _ ≤ abs (ω₁.radius - ω₂.radius) := by apply le_abs_self
      _ = abs (ω₂.radius - ω₁.radius) := by rw [← abs_neg, neg_sub]
      _ < dist ω₁.center ω₂.center := h.2
    linarith
  push_neg at h₁
  rw [abs_of_nonpos h₁]
  unfold radical_axis_dist_to_the_first
  rw [← neg_div, neg_sub]
  apply (div_lt_iff' _).mpr
  apply sub_lt_iff_lt_add'.mpr
  rw [mul_right_comm, ← add_sq']
  apply sq_lt_sq.mpr
  rw [abs_of_pos ω₂.rad_pos, abs_of_pos]
  apply sub_lt_iff_lt_add'.mp
  calc
    _ ≤ abs (ω₂.radius - ω₁.radius) := by apply le_abs_self
    _ < dist ω₁.center ω₂.center := h.2
  apply add_pos ω₁.rad_pos dpos
  linarith

def CC_Intersected_pts {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : CCInxpts P where
  left := sorry --(Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2)) • (Complex.I * (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec) +ᵥ ((radical_axis_dist_to_the_first ω₁ ω₂) • (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec +ᵥ ω₁.center)
  right := sorry --(- Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2)) • (Complex.I * (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec) +ᵥ ((radical_axis_dist_to_the_first ω₁ ω₂) • (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec +ᵥ ω₁.center)

theorem CC_inx_pts_distinct {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : (CC_Intersected_pts h).left ≠ (CC_Intersected_pts h).right := by
  sorry
  /-
  apply (ne_iff_vec_ne_zero _ _).mpr
  unfold Vec.mkPtPt CC_Intersected_pts
  simp
  intro hh
  rcases hh with h₁ | h₂ | h₃
  · apply (Real.sqrt_eq_zero').mp at h₁
    contrapose! h₁
    have : (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2 < ω₁.radius ^ 2 := by
      apply sq_lt_sq.mpr
      rw [abs_of_pos ω₁.rad_pos]
      exact radical_axis_dist_lt_radius h
    linarith
  · have : Complex.I ≠ 0 := Complex.I_ne_zero
    tauto
  contrapose! h₃
  apply Dir.toVec_ne_zero-/

theorem CC_inx_pts_lieson_circles {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : ((CC_Intersected_pts h).left LiesOn ω₁) ∧ ((CC_Intersected_pts h).left LiesOn ω₂) ∧ ((CC_Intersected_pts h).right LiesOn ω₁) ∧ ((CC_Intersected_pts h).right LiesOn ω₂) := by
  sorry
  /-
  have hd : Complex.abs ((VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec) = 1 := by apply Dir.norm_of_dir_toVec_eq_one
  have dpos : 0 < dist ω₁.center ω₂.center := by apply dist_pos.mpr (CC_intersected_centers_distinct h)
  have hlt : (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2 < ω₁.radius ^ 2 := by
    apply sq_lt_sq.mpr
    rw [abs_of_pos ω₁.rad_pos]
    exact radical_axis_dist_lt_radius h
  have heq : ω₂.center -ᵥ ω₁.center = (dist ω₁.center ω₂.center) * (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec := by
    have : (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec = (Vec.norm (VEC ω₁.center ω₂.center))⁻¹ * (VEC ω₁.center ω₂.center) := rfl
    calc
      _ = VEC ω₁.center ω₂.center := rfl
      _ = (Vec.norm (VEC ω₁.center ω₂.center)) * (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec := by
        rw [this, ← mul_assoc, Complex.ofReal_inv, mul_inv_cancel, one_mul]
        apply Complex.ofReal_ne_zero.mpr
        show ‖VEC ω₁.center ω₂.center‖ ≠ 0
        apply norm_ne_zero_iff.mpr
        apply (ne_iff_vec_ne_zero _ _).mp (CC_intersected_centers_distinct h).symm
      _ = (dist ω₁.center ω₂.center) * (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec := by
        congr
        rw [dist_comm, NormedAddTorsor.dist_eq_norm']
        rfl
  constructor
  · show dist ω₁.center (CC_Intersected_pts h).left = ω₁.radius
    apply (sq_eq_sq _ _).mp
    rw [NormedAddTorsor.dist_eq_norm']
    unfold CC_Intersected_pts
    simp
    rw [vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub, vsub_self, sub_sub, zero_sub, AbsoluteValue.map_neg Complex.abs _, ← mul_assoc, ← add_mul, AbsoluteValue.map_mul Complex.abs, hd, mul_one, Complex.sq_abs, Complex.normSq_add_mul_I, Real.sq_sqrt]
    linarith
    linarith
    apply dist_nonneg
    apply le_iff_lt_or_eq.mpr
    left; exact ω₁.rad_pos
  constructor
  · show dist ω₂.center (CC_Intersected_pts h).left = ω₂.radius
    apply (sq_eq_sq _ _).mp
    rw [NormedAddTorsor.dist_eq_norm']
    unfold CC_Intersected_pts
    simp
    rw [vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub, sub_sub, ← mul_assoc, ← add_mul, heq, ← sub_mul, AbsoluteValue.map_mul Complex.abs, hd, mul_one, ← neg_sub, AbsoluteValue.map_neg Complex.abs, ← sub_add_eq_add_sub, Complex.sq_abs, ← Complex.ofReal_sub, Complex.normSq_add_mul_I, Real.sq_sqrt, sub_sq]
    calc
      _ = (dist ω₁.center ω₂.center) ^ 2 + (ω₁.radius) ^ 2 - 2 * (radical_axis_dist_to_the_first ω₁ ω₂) * (dist ω₁.center ω₂.center) := by ring
      _ = ω₂.radius ^ 2 := by
        rw [mul_right_comm]
        unfold radical_axis_dist_to_the_first
        rw [mul_div_cancel']
        ring
        apply mul_ne_zero
        norm_num; linarith
    linarith
    apply dist_nonneg
    apply le_iff_lt_or_eq.mpr
    left; exact ω₂.rad_pos
  constructor
  · show dist ω₁.center (CC_Intersected_pts h).right = ω₁.radius
    apply (sq_eq_sq _ _).mp
    rw [NormedAddTorsor.dist_eq_norm']
    unfold CC_Intersected_pts
    simp
    rw [vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub, vsub_self, sub_neg_eq_add, zero_sub, ← mul_assoc, neg_mul_eq_neg_mul, ← add_mul, AbsoluteValue.map_mul Complex.abs, hd, mul_one, Complex.sq_abs, ← Complex.ofReal_neg, Complex.normSq_add_mul_I, Real.sq_sqrt]
    linarith
    linarith
    apply dist_nonneg
    apply le_iff_lt_or_eq.mpr
    left; exact ω₁.rad_pos
  show dist ω₂.center (CC_Intersected_pts h).right = ω₂.radius
  apply (sq_eq_sq _ _).mp
  rw [NormedAddTorsor.dist_eq_norm']
  unfold CC_Intersected_pts
  simp
  rw [vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub, sub_neg_eq_add, sub_add, ← mul_assoc, ← sub_mul, heq, ← sub_mul, AbsoluteValue.map_mul Complex.abs, hd, mul_one, ← sub_add, Complex.sq_abs, ← Complex.ofReal_sub, Complex.normSq_add_mul_I, Real.sq_sqrt, sub_sq]
  calc
    _ = (dist ω₁.center ω₂.center) ^ 2 + (ω₁.radius) ^ 2 - 2 * (radical_axis_dist_to_the_first ω₁ ω₂) * (dist ω₁.center ω₂.center) := by ring
    _ = ω₂.radius ^ 2 := by
      rw [mul_right_comm]
      unfold radical_axis_dist_to_the_first
      rw [mul_div_cancel']
      ring
      apply mul_ne_zero
      norm_num; linarith
  linarith
  apply dist_nonneg
  apply le_iff_lt_or_eq.mpr
  left; exact ω₂.rad_pos
  -/

theorem CC_inx_pts_line_perp_center_line {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : (LIN (CC_Intersected_pts h).left (CC_Intersected_pts h).right (CC_inx_pts_distinct h).symm) ⟂ (LIN ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm) := by
  sorry
  /-
  show (LIN (CC_Intersected_pts h).left (CC_Intersected_pts h).right (CC_inx_pts_distinct h).symm).toProj = Dir.I.toProj * (LIN ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toProj
  have hd : Complex.abs ((VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec) = 1 := by apply Dir.norm_of_dir_toVec_eq_one
  have hn : Vec.norm (VEC (CC_Intersected_pts h).left (CC_Intersected_pts h).right) = 2 * (Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2)) := by
    unfold Vec.mk_pt_pt CC_Intersected_pts
    simp only
    rw [vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, vsub_self, add_zero_sub]
    simp only [neg_smul, Complex.real_smul, ← mul_assoc, neg_sub_left, ← two_mul,
      neg_Vec_norm_eq_Vec_norm, Nat.cast_ofNat]
    unfold Vec.norm
    simp only [map_mul, Complex.abs_ofNat, Complex.abs_ofReal, Complex.abs_I, mul_one, hd]
    congr
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  have : (VEC_nd (CC_Intersected_pts h).left (CC_Intersected_pts h).right (CC_inx_pts_distinct h).symm).toDir.unitVec = (- (Dir.I * (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir)).1 := by
    calc
      _ = (Vec.norm (VEC (CC_Intersected_pts h).left (CC_Intersected_pts h).right))⁻¹ • (VEC (CC_Intersected_pts h).left (CC_Intersected_pts h).right) := rfl
      _ = (- (Vec.norm (VEC (CC_Intersected_pts h).left (CC_Intersected_pts h).right))⁻¹ * (2 * Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2))) • (Complex.I * (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec) := by
        unfold CC_Intersected_pts Vec.mk_pt_pt
        simp
        rw [neg_sub_left, ← two_mul]
        ring
      _ = - (Dir.I * (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir).1 := by
        rw [hn, neg_mul, inv_mul_cancel, neg_one_smul]
        rfl
        rw [← hn]
        show ‖VEC (CC_Intersected_pts h).left (CC_Intersected_pts h).right‖ ≠ 0
        apply norm_ne_zero_iff.mpr
        apply (ne_iff_vec_ne_zero _ _).mp (CC_inx_pts_distinct h).symm
  have hdir: (VEC_nd (CC_Intersected_pts h).left (CC_Intersected_pts h).right (CC_inx_pts_distinct h).symm).toDir = - (Dir.I * (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir) := by
    ext; rw [this]; rw [this]
  calc
    _ = (VEC_nd (CC_Intersected_pts h).left (CC_Intersected_pts h).right (CC_inx_pts_distinct h).symm).toDir.toProj := rfl
    _ = (Dir.I * (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir).toProj := by
      apply (Dir.toProj_eq_toProj_iff _ _).mpr
      right; exact hdir
  -/


/- different circles have at most two intersections -/
lemma CC_inx_pt_not_lieson_center_line {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h : ω₁ Intersect ω₂) (h₁ : A LiesOn ω₁) (h₂ : A LiesOn ω₂) : ¬(A LiesOn (LIN ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm)) := sorry

theorem CC_inx_pt_liesonleft_center_ray_eq_leftinxpt {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h : ω₁ Intersect ω₂) (h₁ : A LiesOn ω₁) (h₂ : A LiesOn ω₂) (h₃ : A LiesOnLeft (RAY ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm)) : A = (CC_Intersected_pts h).left := sorry

theorem CC_inx_pt_liesonright_center_ray_eq_rightinxpt {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h : ω₁ Intersect ω₂) (h₁ : A LiesOn ω₁) (h₂ : A LiesOn ω₂) (h₃ : A LiesOnRight (RAY ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm)) : A = (CC_Intersected_pts h).right := sorry

end Circle

end CC

end EuclidGeom
