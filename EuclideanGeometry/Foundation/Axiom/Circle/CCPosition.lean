import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence_trash

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

scoped infix : 50 " Separate " => Circle.IsSeparated
scoped infix : 50 " Intersect " => Circle.IsIntersected
scoped infix : 50 " Circumscribe " => Circle.IsCircumscribed
scoped infix : 50 " IncludeIn " => Circle.IsIncluded
scoped infix : 50 " InscribeIn " => Circle.IsInscribed

namespace Circle

theorem CC_separated_symm (ω₁ : Circle P) (ω₂ : Circle P) : ω₁ Separate ω₂ ↔ ω₂ Separate ω₁ := by
  unfold Circle.IsSeparated
  rw [dist_comm, add_comm]

theorem CC_separated_pt_outside_second_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ Separate ω₂) (h₂ : A LiesOn ω₁) : A LiesOut ω₂ := by
  have : dist ω₂.center A + dist ω₁.center A ≥ dist ω₁.center ω₂.center := by
    rw [add_comm]
    apply dist_triangle_right
  have hh₁ : dist ω₁.center A = ω₁.radius := h₂
  have hh₂ : dist ω₁.center ω₂.center > ω₁.radius + ω₂.radius := h₁
  have : dist ω₂.center A > ω₂.radius := by linarith
  exact this

theorem CC_separated_pt_outside_first_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ Separate ω₂) (h₂ : A LiesOn ω₂) : A LiesOut ω₁ := CC_separated_pt_outside_second_circle ((CC_separated_symm ω₁ ω₂).mp h₁) h₂


lemma CC_Circumscribe_centers_distinct {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Circumscribe ω₂) : ω₁.center ≠ ω₂.center := by
  have : dist ω₁.center ω₂.center > 0 := by
    calc
      _ = ω₁.radius + ω₂.radius := h
      _ > 0 := by apply add_pos ω₁.rad_pos ω₂.rad_pos
  apply dist_pos.mp this

def CC_Circumscribe_Point {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Circumscribe ω₂) : P := (ω₁.radius • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.unitVec) +ᵥ ω₁.center

theorem CC_circumscribe_point_lieson_circles {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Circumscribe ω₂) : ((CC_Circumscribe_Point h) LiesOn ω₁) ∧ ((CC_Circumscribe_Point h) LiesOn ω₂) := by
  haveI : PtNe ω₁.center ω₂.center := ⟨CC_Circumscribe_centers_distinct h⟩
  constructor
  · have : dist ω₁.center (CC_Circumscribe_Point h) = ω₁.radius := by
      calc
        _ = ‖ω₁.radius • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by
          unfold CC_Circumscribe_Point
          simp
        _ = ω₁.radius := by
          rw [norm_smul, Dir.norm_unitVec, mul_one, Real.norm_of_nonneg ω₁.rad_pos.le]
    exact this
  have : dist ω₂.center (CC_Circumscribe_Point h) = ω₂.radius := by
    calc
      _ = ‖VEC (CC_Circumscribe_Point h) ω₂.center‖ := by rw [NormedAddTorsor.dist_eq_norm']; rfl
      _ = ‖VEC ω₁.center ω₂.center - VEC ω₁.center (CC_Circumscribe_Point h)‖ := by rw [vec_sub_vec]
      _ = ‖VEC ω₁.center ω₂.center - ω₁.radius • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by
        unfold CC_Circumscribe_Point Vec.mkPtPt
        rw [vadd_vsub]
      _ = ‖(VEC_nd ω₁.center ω₂.center).1 - ω₁.radius • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := rfl
      _ = ‖(‖VEC_nd ω₁.center ω₂.center‖ - ω₁.radius) • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by
        rw [sub_smul, VecND.norm_smul_toDir_unitVec]
      _ = ‖(dist ω₁.center ω₂.center - ω₁.radius) • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by
        rw [dist_comm, NormedAddTorsor.dist_eq_norm']
        rfl
      _ = ‖ω₂.radius • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by
        rw [h, add_comm, add_sub_cancel]
      _ = ω₂.radius := by
          rw [norm_smul, Dir.norm_unitVec, mul_one, Real.norm_of_nonneg ω₂.rad_pos.le]
  exact this

theorem CC_circumscribe_point_centers_colinear {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Circumscribe ω₂) : colinear ω₁.center (CC_Circumscribe_Point h) ω₂.center := by
  haveI : PtNe ω₁.center ω₂.center := ⟨CC_Circumscribe_centers_distinct h⟩
  have : VEC ω₁.center (CC_Circumscribe_Point h) = (ω₁.radius * ‖VEC ω₁.center ω₂.center‖⁻¹) • (VEC ω₁.center ω₂.center) := by
    calc
      _ = ω₁.radius • (VEC_nd ω₁.center ω₂.center).toDir.unitVec := by
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
  haveI : PtNe ω₁.center ω₂.center := ⟨h.2⟩
  constructor
  · have : dist ω₁.center (CC_Inscribe_Point h) = ω₁.radius := by
      calc
        _ = ‖ω₁.radius • (VEC_nd ω₂.center ω₁.center).toDir.unitVec‖ := by
          unfold CC_Inscribe_Point
          simp
        _ = ω₁.radius := by
          rw [norm_smul, Dir.norm_unitVec, mul_one, Real.norm_of_nonneg ω₁.rad_pos.le]
    exact this
  have : dist ω₂.center (CC_Inscribe_Point h) = ω₂.radius := by
    calc
      _ = ‖VEC (CC_Inscribe_Point h) ω₂.center‖ := by
        rw [NormedAddTorsor.dist_eq_norm']; rfl
      _ = ‖VEC ω₁.center ω₂.center - VEC ω₁.center (CC_Inscribe_Point h)‖ := by rw [vec_sub_vec]
      _ = ‖VEC ω₁.center ω₂.center - ω₁.radius • (VEC_nd ω₂.center ω₁.center).toDir.unitVec‖ := by
        unfold CC_Inscribe_Point Vec.mkPtPt
        rw [vadd_vsub]
      _ = ‖(VEC_nd ω₁.center ω₂.center).1 - ω₁.radius • (VEC_nd ω₂.center ω₁.center).toDir.unitVec‖ := rfl
      _ = ‖(VEC_nd ω₁.center ω₂.center).1 + ω₁.radius • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by
        have : VEC_nd ω₁.center ω₂.center = - VEC_nd ω₂.center ω₁.center := by
          ext; simp only [ne_eq, RayVector.coe_neg, VecND.coe_mkPtPt]
          rw [neg_vec]
        have : (VEC_nd ω₁.center ω₂.center).toDir.unitVec = - (VEC_nd ω₂.center ω₁.center).toDir.unitVec := by rw [this]; simp
        rw [this, smul_neg, sub_eq_add_neg]
      _ = ‖(‖VEC_nd ω₁.center ω₂.center‖ + ω₁.radius) • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by
        rw [add_smul, VecND.norm_smul_toDir_unitVec]
      _ = ‖(dist ω₁.center ω₂.center + ω₁.radius) • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by
        congr
        rw [dist_comm]
        apply Eq.trans _ (NormedAddTorsor.dist_eq_norm' _ _).symm -- `This should be a lemma in simp`
        rfl
      _ = ‖ω₂.radius • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by
        congr; rw [h.1]; linarith
      _ = ω₂.radius := by
          rw [norm_smul, Dir.norm_unitVec, mul_one, Real.norm_of_nonneg ω₂.rad_pos.le] -- note: 我不知道这行出现多少次了，不要复制粘贴，写点lemma
  show Circle.IsOn (CC_Inscribe_Point h) ω₂
  exact this

theorem CC_inscribe_point_centers_colinear {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ InscribeIn ω₂) : colinear ω₁.center ω₂.center (CC_Inscribe_Point h) := by
  haveI : PtNe ω₁.center ω₂.center := ⟨h.2⟩
  have : VEC ω₁.center (CC_Inscribe_Point h) = (- ω₁.radius * ‖(VEC ω₁.center ω₂.center)‖⁻¹) • VEC ω₁.center ω₂.center := by
    calc
      _ = ω₁.radius • (VEC_nd ω₂.center ω₁.center).toDir.unitVec := by
        unfold CC_Inscribe_Point
        simp
      _ = ω₁.radius • (- (VEC_nd ω₁.center ω₂.center).toDir.unitVec) := by
        -- note: 为什么没有 neg_vecND
        trans ω₁.radius • (-VEC_nd ω₁.center ω₂.center).toDir.unitVec
        · unfold VecND.mkPtPt Vec.mkPtPt
          congr
          rw [← neg_eq_iff_eq_neg, neg_vsub_eq_vsub_rev]
        · simp
      _ = - ω₁.radius • (VEC_nd ω₁.center ω₂.center).toDir.unitVec := by
        rw [smul_neg, neg_smul]
      _ = (- ω₁.radius) • ‖VEC ω₁.center ω₂.center‖⁻¹ • VEC ω₁.center ω₂.center := rfl
      _ = (- ω₁.radius * ‖VEC ω₁.center ω₂.center‖⁻¹) • VEC ω₁.center ω₂.center := by apply smul_smul
  apply colinear_of_vec_eq_smul_vec this


theorem CC_included_pt_isint_second_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ IncludeIn ω₂) (h₂ : A LiesOn ω₁) : A LiesInt ω₂ := by
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
  left := (Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2) * Complex.I + (radical_axis_dist_to_the_first ω₁ ω₂)) • (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.unitVec +ᵥ ω₁.center
  right := (- Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2) * Complex.I + (radical_axis_dist_to_the_first ω₁ ω₂)) • (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.unitVec +ᵥ ω₁.center

theorem CC_inx_pts_distinct {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : (CC_Intersected_pts h).left ≠ (CC_Intersected_pts h).right := by
  apply (ne_iff_vec_ne_zero _ _).mpr
  unfold Vec.mkPtPt CC_Intersected_pts
  simp only [neg_mul, vadd_vsub_vadd_cancel_right, ne_eq, ← sub_smul]
  simp only [add_sub_add_right_eq_sub, sub_neg_eq_add, smul_eq_zero, add_self_eq_zero, mul_eq_zero,
    Complex.ofReal_eq_zero, Complex.I_ne_zero, or_false, VecND.ne_zero]
  push_neg
  apply Real.sqrt_ne_zero'.mpr
  have hlt : (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2 < ω₁.radius ^ 2 := by
    apply sq_lt_sq.mpr
    rw [abs_of_pos ω₁.rad_pos]
    exact radical_axis_dist_lt_radius h
  linarith

theorem CC_inx_pts_lieson_circles {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : ((CC_Intersected_pts h).left LiesOn ω₁) ∧ ((CC_Intersected_pts h).left LiesOn ω₂) ∧ ((CC_Intersected_pts h).right LiesOn ω₁) ∧ ((CC_Intersected_pts h).right LiesOn ω₂) := by
  haveI : PtNe ω₁.center ω₂.center := ⟨CC_intersected_centers_distinct h⟩
  have hlt : (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2 < ω₁.radius ^ 2 := by
    apply sq_lt_sq.mpr
    rw [abs_of_pos ω₁.rad_pos]
    exact radical_axis_dist_lt_radius h
  have heq : ω₂.center -ᵥ ω₁.center = (dist ω₁.center ω₂.center) • (VEC_nd ω₁.center ω₂.center).toDir.unitVec := by
    calc
      _ = VEC ω₁.center ω₂.center := rfl
      _ = ‖VEC_nd ω₁.center ω₂.center‖ • (VEC_nd ω₁.center ω₂.center).toDir.unitVec := by simp only [VecND.norm_smul_toDir_unitVec,
        ne_eq, VecND.coe_mkPtPt]
      _ = (dist ω₁.center ω₂.center) • (VEC_nd ω₁.center ω₂.center).toDir.unitVec := by
        rw [dist_comm, NormedAddTorsor.dist_eq_norm']
        rfl
  constructor
  · show dist ω₁.center (CC_Intersected_pts h).left = ω₁.radius
    calc
      _ = ‖(Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2) * Complex.I + (radical_axis_dist_to_the_first ω₁ ω₂)) • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by
        unfold CC_Intersected_pts
        simp
      _ = ‖Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2) * Complex.I + (radical_axis_dist_to_the_first ω₁ ω₂)‖ := by
        rw [norm_smul, Dir.norm_unitVec, mul_one]
      _ = Real.sqrt (Complex.normSq (Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2) * Complex.I + (radical_axis_dist_to_the_first ω₁ ω₂))) := rfl
      _ = Real.sqrt (ω₁.radius ^ 2) := by
        rw [add_comm, Complex.normSq_add_mul_I, Real.sq_sqrt (by linarith)]
        simp
      _ = ω₁.radius := Real.sqrt_sq (by linarith [ω₁.rad_pos])
  constructor
  · show dist ω₂.center (CC_Intersected_pts h).left = ω₂.radius
    calc
      _ = ‖(dist ω₁.center ω₂.center) • (VEC_nd ω₁.center ω₂.center).toDir.unitVec - (Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2) * Complex.I + (radical_axis_dist_to_the_first ω₁ ω₂)) • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by
        unfold CC_Intersected_pts
        simp
        rw [NormedAddTorsor.dist_eq_norm', vsub_vadd_eq_vsub_sub, heq]
      _ = ‖(dist ω₁.center ω₂.center - (Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2) * Complex.I + (radical_axis_dist_to_the_first ω₁ ω₂))) • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by rw [sub_smul]; simp
      _ = ‖dist ω₁.center ω₂.center - radical_axis_dist_to_the_first ω₁ ω₂ + (- Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2)) * Complex.I‖ := by
        rw [norm_smul, Dir.norm_unitVec, mul_one]
        ring_nf
      _ = Real.sqrt (Complex.normSq (dist ω₁.center ω₂.center - radical_axis_dist_to_the_first ω₁ ω₂ + (- Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2)) * Complex.I)) := rfl
      _ = Real.sqrt ((dist ω₁.center ω₂.center - radical_axis_dist_to_the_first ω₁ ω₂) ^ 2 + (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2)) := by
        rw [← Complex.ofReal_sub, ← Complex.ofReal_neg, Complex.normSq_add_mul_I, neg_sq, Real.sq_sqrt (by linarith)]
      _ = ω₂.radius := by
        unfold radical_axis_dist_to_the_first
        rw [sub_sq, mul_div_cancel']
        ring_nf
        apply Real.sqrt_sq (by linarith [ω₂.rad_pos])
        apply mul_ne_zero (by norm_num) (dist_ne_zero.mpr (CC_intersected_centers_distinct h))
  constructor
  · show dist ω₁.center (CC_Intersected_pts h).right = ω₁.radius
    calc
      _ = ‖(- Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2) * Complex.I + (radical_axis_dist_to_the_first ω₁ ω₂)) • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by
        unfold CC_Intersected_pts
        simp
      _ = ‖- Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2) * Complex.I + (radical_axis_dist_to_the_first ω₁ ω₂)‖ := by
        rw [norm_smul, Dir.norm_unitVec, mul_one]
      _ = Real.sqrt (Complex.normSq (- Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2) * Complex.I + (radical_axis_dist_to_the_first ω₁ ω₂))) := rfl
      _ = Real.sqrt (ω₁.radius ^ 2) := by
        rw [add_comm, ← Complex.ofReal_neg, Complex.normSq_add_mul_I, neg_sq, Real.sq_sqrt (by linarith)]
        simp
      _ = ω₁.radius := Real.sqrt_sq (by linarith [ω₁.rad_pos])
  show dist ω₂.center (CC_Intersected_pts h).right = ω₂.radius
  calc
    _ = ‖(dist ω₁.center ω₂.center) • (VEC_nd ω₁.center ω₂.center).toDir.unitVec - (- Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2) * Complex.I + (radical_axis_dist_to_the_first ω₁ ω₂)) • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by
      unfold CC_Intersected_pts
      simp
      rw [NormedAddTorsor.dist_eq_norm', vsub_vadd_eq_vsub_sub, heq]
    _ = ‖(dist ω₁.center ω₂.center - (- Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2) * Complex.I + (radical_axis_dist_to_the_first ω₁ ω₂))) • (VEC_nd ω₁.center ω₂.center).toDir.unitVec‖ := by rw [sub_smul]; simp
    _ = ‖dist ω₁.center ω₂.center - radical_axis_dist_to_the_first ω₁ ω₂ + (Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2)) * Complex.I‖ := by
      rw [norm_smul, Dir.norm_unitVec, mul_one]
      ring_nf
    _ = Real.sqrt (Complex.normSq (dist ω₁.center ω₂.center - radical_axis_dist_to_the_first ω₁ ω₂ + (Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2)) * Complex.I)) := rfl
    _ = Real.sqrt ((dist ω₁.center ω₂.center - radical_axis_dist_to_the_first ω₁ ω₂) ^ 2 + (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first ω₁ ω₂) ^ 2)) := by
      rw [← Complex.ofReal_sub, Complex.normSq_add_mul_I, Real.sq_sqrt (by linarith)]
    _ = ω₂.radius := by
      unfold radical_axis_dist_to_the_first
      rw [sub_sq, mul_div_cancel']
      ring_nf
      apply Real.sqrt_sq (by linarith [ω₂.rad_pos])
      apply mul_ne_zero (by norm_num) (dist_ne_zero.mpr (CC_intersected_centers_distinct h))

lemma CC_inx_pts_not_colinear {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : (¬ colinear (CC_Intersected_pts h).left ω₁.center ω₂.center) ∧ (¬ colinear (CC_Intersected_pts h).right ω₁.center ω₂.center) := by
  constructor
  · intro hc
    set tri : Triangle P := ▵ (CC_Intersected_pts h).left ω₁.center ω₂.center with tri_def
    have : colinear tri.1 tri.2 tri.3 := hc
    rw [Triangle.edge_sum_eq_edge_iff_colinear] at this
    rcases this with heq | (heq | heq)
    · rw [tri_def] at heq
      have heq : dist ω₁.center ω₂.center + dist ω₂.center (CC_Intersected_pts h).left = dist (CC_Intersected_pts h).left ω₁.center := heq
      have hgt : dist ω₁.center ω₂.center > dist ω₁.center ω₂.center := by
        calc
          _ > abs (ω₂.radius - ω₁.radius) := h.2
          _ = abs (dist ω₂.center (CC_Intersected_pts h).left - dist (CC_Intersected_pts h).left ω₁.center) := by rw [← (CC_inx_pts_lieson_circles h).1, dist_comm, (CC_inx_pts_lieson_circles h).2.1]
          _ = dist ω₁.center ω₂.center := by
            rw [← heq]
            ring_nf
            rw [abs_neg, abs_of_nonneg dist_nonneg]
      linarith
    · rw [tri_def] at heq
      have heq : dist ω₂.center (CC_Intersected_pts h).left + dist (CC_Intersected_pts h).left ω₁.center = dist ω₁.center ω₂.center := heq
      have hlt : dist ω₁.center ω₂.center < dist ω₁.center ω₂.center := by
        calc
          _ < ω₁.radius + ω₂.radius := h.1
          _ = dist (CC_Intersected_pts h).left ω₁.center + dist ω₂.center (CC_Intersected_pts h).left := by rw [← (CC_inx_pts_lieson_circles h).1, dist_comm, (CC_inx_pts_lieson_circles h).2.1]
          _ = dist ω₁.center ω₂.center := by rw [← heq]; ring
      linarith
    rw [tri_def] at heq
    have heq : dist (CC_Intersected_pts h).left ω₁.center + dist ω₁.center ω₂.center = dist ω₂.center (CC_Intersected_pts h).left := heq
    have hgt : dist ω₁.center ω₂.center > dist ω₁.center ω₂.center := by
      calc
        _ > abs (ω₂.radius - ω₁.radius) := h.2
        _ = abs (dist ω₂.center (CC_Intersected_pts h).left - dist (CC_Intersected_pts h).left ω₁.center) := by rw [← (CC_inx_pts_lieson_circles h).1, dist_comm, (CC_inx_pts_lieson_circles h).2.1]
        _ = dist ω₁.center ω₂.center := by
          rw [← heq]
          ring_nf
          rw [abs_of_nonneg dist_nonneg]
    linarith
  intro hc
  set tri : Triangle P := ▵ (CC_Intersected_pts h).right ω₁.center ω₂.center with tri_def
  have : colinear tri.1 tri.2 tri.3 := hc
  rw [Triangle.edge_sum_eq_edge_iff_colinear] at this
  rcases this with heq | (heq | heq)
  · rw [tri_def] at heq
    have heq : dist ω₁.center ω₂.center + dist ω₂.center (CC_Intersected_pts h).right = dist (CC_Intersected_pts h).right ω₁.center := heq
    have hgt : dist ω₁.center ω₂.center > dist ω₁.center ω₂.center := by
      calc
        _ > abs (ω₂.radius - ω₁.radius) := h.2
        _ = abs (dist ω₂.center (CC_Intersected_pts h).right - dist (CC_Intersected_pts h).right ω₁.center) := by rw [← (CC_inx_pts_lieson_circles h).2.2.1, dist_comm, (CC_inx_pts_lieson_circles h).2.2.2]
        _ = dist ω₁.center ω₂.center := by
          rw [← heq]
          ring_nf
          rw [abs_neg, abs_of_nonneg dist_nonneg]
    linarith
  · rw [tri_def] at heq
    have heq : dist ω₂.center (CC_Intersected_pts h).right + dist (CC_Intersected_pts h).right ω₁.center = dist ω₁.center ω₂.center := heq
    have hlt : dist ω₁.center ω₂.center < dist ω₁.center ω₂.center := by
      calc
        _ < ω₁.radius + ω₂.radius := h.1
        _ = dist (CC_Intersected_pts h).right ω₁.center + dist ω₂.center (CC_Intersected_pts h).right := by rw [← (CC_inx_pts_lieson_circles h).2.2.1, dist_comm, (CC_inx_pts_lieson_circles h).2.2.2]
        _ = dist ω₁.center ω₂.center := by rw [← heq]; ring
    linarith
  rw [tri_def] at heq
  have heq : dist (CC_Intersected_pts h).right ω₁.center + dist ω₁.center ω₂.center = dist ω₂.center (CC_Intersected_pts h).right := heq
  have hgt : dist ω₁.center ω₂.center > dist ω₁.center ω₂.center := by
    calc
      _ > abs (ω₂.radius - ω₁.radius) := h.2
      _ = abs (dist ω₂.center (CC_Intersected_pts h).right - dist (CC_Intersected_pts h).right ω₁.center) := by rw [← (CC_inx_pts_lieson_circles h).2.2.1, dist_comm, (CC_inx_pts_lieson_circles h).2.2.2]
      _ = dist ω₁.center ω₂.center := by
        rw [← heq]
        ring_nf
        rw [abs_of_nonneg dist_nonneg]
  linarith

theorem CC_inx_pts_tri_acongr {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : (▵ ω₁.center ω₂.center (CC_Intersected_pts h).left) ≅ₐ (▵ ω₁.center ω₂.center (CC_Intersected_pts h).right) := by
  haveI : PtNe ω₁.center ω₂.center := ⟨CC_intersected_centers_distinct h⟩
  have he₁ : (▵ ω₁.center ω₂.center (CC_Intersected_pts h).left).edge₁.length = (▵ ω₁.center ω₂.center (CC_Intersected_pts h).right).edge₁.length := by
    show (SEG ω₂.center (CC_Intersected_pts h).left).length = (SEG ω₂.center (CC_Intersected_pts h).right).length
    simp
    rw [(CC_inx_pts_lieson_circles h).2.1, (CC_inx_pts_lieson_circles h).2.2.2]
  have he₂ : (▵ ω₁.center ω₂.center (CC_Intersected_pts h).left).edge₂.length = (▵ ω₁.center ω₂.center (CC_Intersected_pts h).right).edge₂.length := by
    show (SEG (CC_Intersected_pts h).left ω₁.center).length = (SEG (CC_Intersected_pts h).right ω₁.center).length
    simp
    rw [dist_comm, (CC_inx_pts_lieson_circles h).1, dist_comm, (CC_inx_pts_lieson_circles h).2.2.1]
  have he₃ : (▵ ω₁.center ω₂.center (CC_Intersected_pts h).left).edge₃.length = (▵ ω₁.center ω₂.center (CC_Intersected_pts h).right).edge₃.length := rfl
  rcases Triangle.congr_or_acongr_of_SSS he₁ he₂ he₃ with hc | hac
  · exfalso
    have heq : (CC_Intersected_pts h).left = (CC_Intersected_pts h).right := by
      apply Triangle.IsCongr.unique_of_eq_eq hc (by rfl) (by rfl)
    apply CC_inx_pts_distinct h heq
  exact hac

theorem CC_inx_pts_line_perp_center_line {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : (LIN (CC_Intersected_pts h).left (CC_Intersected_pts h).right (CC_inx_pts_distinct h).symm) ⟂ (LIN ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm) := by
  haveI : PtNe (CC_Intersected_pts h).left (CC_Intersected_pts h).right := ⟨CC_inx_pts_distinct h⟩
  haveI : PtNe ω₁.center ω₂.center := ⟨CC_intersected_centers_distinct h⟩
  show (LIN (CC_Intersected_pts h).left (CC_Intersected_pts h).right).toProj = (LIN ω₁.center ω₂.center).toProj.perp
  sorry
  /-
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
theorem CC_inx_pts_uniqueness {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h : ω₁ Intersect ω₂) (h₁ : A LiesOn ω₁) (h₂ : A LiesOn ω₂) : (A = (CC_Intersected_pts h).left) ∨ (A = (CC_Intersected_pts h).right) := by
  haveI : PtNe ω₁.center ω₂.center := ⟨CC_intersected_centers_distinct h⟩
  have hac : (▵ ω₁.center ω₂.center (CC_Intersected_pts h).left) ≅ₐ (▵ ω₁.center ω₂.center (CC_Intersected_pts h).right) := CC_inx_pts_tri_acongr h
  have he₁ : (▵ ω₁.center ω₂.center (CC_Intersected_pts h).left).edge₁.length = (▵ ω₁.center ω₂.center A).edge₁.length := by
    show (SEG ω₂.center (CC_Intersected_pts h).left).length = (SEG ω₂.center A).length
    simp
    rw [(CC_inx_pts_lieson_circles h).2.1, h₂]
  have he₂ : (▵ ω₁.center ω₂.center (CC_Intersected_pts h).left).edge₂.length = (▵ ω₁.center ω₂.center A).edge₂.length := by
    show (SEG (CC_Intersected_pts h).left ω₁.center).length = (SEG A ω₁.center).length
    simp
    rw [dist_comm, (CC_inx_pts_lieson_circles h).1, dist_comm, h₁]
  have he₃ : (▵ ω₁.center ω₂.center (CC_Intersected_pts h).left).edge₃.length = (▵ ω₁.center ω₂.center A).edge₃.length := rfl
  rcases Triangle.congr_or_acongr_of_SSS he₁ he₂ he₃ with hc | hc
  · left; symm
    apply Triangle.IsCongr.unique_of_eq_eq hc (by rfl) (by rfl)
  right
  have : (▵ ω₁.center ω₂.center A) ≅ (▵ ω₁.center ω₂.center (CC_Intersected_pts h).right) := Triangle.congr_of_acongr_acongr hc.symm hac
  apply Triangle.IsCongr.unique_of_eq_eq this (by rfl) (by rfl)

end Circle

end CC

end EuclidGeom
