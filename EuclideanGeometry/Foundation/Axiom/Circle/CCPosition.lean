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

def CC_Circumscribe_Point {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Circumscribe ω₂) : P := (ω₁.radius • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.1) +ᵥ ω₁.center

theorem CC_circumscribe_point_lieson_circles {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Circumscribe ω₂) : ((CC_Circumscribe_Point h) LiesOn ω₁) ∧ ((CC_Circumscribe_Point h) LiesOn ω₂) := by
  constructor
  · have : dist ω₁.center (CC_Circumscribe_Point h) = ω₁.radius := by
      calc
        _ = dist (CC_Circumscribe_Point h) ω₁.center := by apply dist_comm
        _ = ‖(CC_Circumscribe_Point h) -ᵥ ω₁.center‖ := by apply NormedAddTorsor.dist_eq_norm'
        _ = norm (ω₁.radius • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.1) := by
          unfold CC_Circumscribe_Point
          simp
        _ = Vec.norm (ω₁.radius • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.1) := rfl
        _ = ω₁.radius := by
          rw [Vec.norm_smul_eq_mul_norm, Dir.norm_of_dir_tovec_eq_one, mul_one]
          apply le_iff_lt_or_eq.mpr
          left; exact ω₁.rad_pos
    show Circle.IsOn (CC_Circumscribe_Point h) ω₁
    exact this
  have h' : dist ω₁.center ω₂.center = ω₁.radius + ω₂.radius := by exact h
  have : dist ω₂.center (CC_Circumscribe_Point h) = ω₂.radius := by
    calc
      _ = ‖ω₂.center -ᵥ (CC_Circumscribe_Point h)‖ := by apply NormedAddTorsor.dist_eq_norm'
      _ = Vec.norm (VEC (CC_Circumscribe_Point h) ω₂.center) := rfl
      _ = Vec.norm (VEC ω₁.center ω₂.center - VEC ω₁.center (CC_Circumscribe_Point h)) := by rw [vec_sub_vec]
      _ = Vec.norm (VEC ω₁.center ω₂.center - ω₁.radius • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.1) := by
        unfold CC_Circumscribe_Point Vec.mk_pt_pt
        rw [vadd_vsub]
      _ = Vec.norm ((VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).1 - ω₁.radius • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.1) := rfl
      _ = Vec.norm ((Vec_nd.norm (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm) - ω₁.radius) • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.1) := by
        rw [sub_smul, Vec_nd.self_eq_norm_smul_todir]
      _ = Vec.norm ((dist ω₁.center ω₂.center - ω₁.radius) • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.1) := by
        rw [dist_comm, NormedAddTorsor.dist_eq_norm']
        rfl
      _ = Vec.norm (ω₂.radius • (VEC_nd ω₁.center ω₂.center (CC_Circumscribe_centers_distinct h).symm).toDir.1) := by
        rw [h', add_comm, add_sub_cancel]
      _ = ω₂.radius := by
          rw [Vec.norm_smul_eq_mul_norm, Dir.norm_of_dir_tovec_eq_one, mul_one]
          apply le_iff_lt_or_eq.mpr
          left; exact ω₂.rad_pos
  show Circle.IsOn (CC_Circumscribe_Point h) ω₂
  exact this

theorem CC_circumscribe_point_lieson_center_seg {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Circumscribe ω₂) : (CC_Circumscribe_Point h) LiesOn (SEG ω₁.center ω₂.center) := sorry


theorem CC_inscribed_pt_inside_second_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ InscribeIn ω₂) (h₂ : A LiesOn ω₁) : A LiesIn ω₂ := sorry

def CC_Inscribe_Point {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ InscribeIn ω₂) : P := (ω₁.radius • (VEC_nd ω₂.center ω₁.center h.2).toDir.1) +ᵥ ω₁.center

theorem CC_inscribe_point_lieson_circles {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ InscribeIn ω₂) : ((CC_Inscribe_Point h) LiesOn ω₁) ∧ ((CC_Inscribe_Point h) LiesOn ω₂) := sorry

theorem CC_inscribe_point_lieson_center_ray {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ InscribeIn ω₂) : (CC_Inscribe_Point h) LiesOn (RAY ω₂.center ω₁.center h.2) := sorry


theorem CC_included_pt_isint_second_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ IncludeIn ω₂) (h₂ : A LiesOn ω₁) : Circle.IsInt A ω₂ := sorry

theorem CC_included_pt_outside_first_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ IncludeIn ω₂) (h₂ : A LiesOn ω₂) : A LiesOut ω₁ := sorry


theorem CC_inxwith_iff_intersected_or_circumscribed_or_inscribed {ω₁ : Circle P} {ω₂ : Circle P} : ω₁ InxWith ω₂ ↔ (ω₁ Intersect ω₂) ∨ (ω₁ Circumscribe ω₂) ∨ (ω₁ InscribeIn ω₂) ∨ (ω₂ InscribeIn ω₁) := sorry


lemma CC_intersected_centers_distinct {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : ω₁.center ≠ ω₂.center := sorry

@[ext]
structure CCInxpts (P : Type _) [EuclideanPlane P] where
  left : P
  right : P

def radical_axis_dist_to_the_first {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : ℝ := (ω₁.radius ^ 2 + (dist ω₁.center ω₂.center) ^ 2 - ω₂.radius ^ 2) / (2 * (dist ω₁.center ω₂.center))

lemma radical_axis_dist_lt_radius {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : (radical_axis_dist_to_the_first h) < ω₁.radius := sorry

def CC_Intersected_pts {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : CCInxpts P where
  left := (Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first h) ^ 2)) • (Complex.I * (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec) +ᵥ ((radical_axis_dist_to_the_first h) • (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec +ᵥ ω₁.center)
  right := (- Real.sqrt (ω₁.radius ^ 2 - (radical_axis_dist_to_the_first h) ^ 2)) • (Complex.I * (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec) +ᵥ ((radical_axis_dist_to_the_first h) • (VEC_nd ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm).toDir.toVec +ᵥ ω₁.center)

theorem CC_inx_pts_distinct {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : (CC_Intersected_pts h).left ≠ (CC_Intersected_pts h).right := by
  apply (ne_iff_vec_ne_zero _ _).mpr
  unfold Vec.mk_pt_pt CC_Intersected_pts
  simp
  intro hh
  rcases hh with h₁ | h₂ | h₃
  · sorry
  · have : Complex.I ≠ 0 := Complex.I_ne_zero
    tauto
  sorry

theorem CC_inx_pts_lieson_circles {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : ((CC_Intersected_pts h).left LiesOn ω₁) ∧ ((CC_Intersected_pts h).left LiesOn ω₂) ∧ ((CC_Intersected_pts h).right LiesOn ω₁) ∧ ((CC_Intersected_pts h).right LiesOn ω₂) := sorry

theorem CC_inx_pts_line_perp_center_line {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : (LIN (CC_Intersected_pts h).left (CC_Intersected_pts h).right (CC_inx_pts_distinct h).symm) ⟂ (LIN ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm) := sorry

/- different circles have at most two intersections -/
lemma CC_inx_pt_not_lieson_center_line {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h : ω₁ Intersect ω₂) (h₁ : A LiesOn ω₁) (h₂ : A LiesOn ω₂) : ¬(A LiesOn (LIN ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm)) := sorry

theorem CC_inx_pt_liesonleft_center_ray_eq_leftinxpt {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h : ω₁ Intersect ω₂) (h₁ : A LiesOn ω₁) (h₂ : A LiesOn ω₂) (h₃ : A LiesOnLeft (RAY ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm)) : A = (CC_Intersected_pts h).left := sorry

theorem CC_inx_pt_liesonright_center_ray_eq_rightinxpt {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h : ω₁ Intersect ω₂) (h₁ : A LiesOn ω₁) (h₂ : A LiesOn ω₂) (h₃ : A LiesOnRight (RAY ω₁.center ω₂.center (CC_intersected_centers_distinct h).symm)) : A = (CC_Intersected_pts h).right := sorry

end Circle

end CC

end EuclidGeom
