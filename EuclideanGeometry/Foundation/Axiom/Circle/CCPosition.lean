import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

section CC

namespace Circle

protected def IsSeparated (ω₁ : Circle P) (ω₂ : Circle P) : Prop := (SEG ω₁.center ω₂.center).length > ω₁.radius + ω₂.radius

protected def IsIntersected (ω₁ : Circle P) (ω₂ : Circle P) : Prop := ((SEG ω₁.center ω₂.center).length < ω₁.radius + ω₂.radius) ∧ ((SEG ω₁.center ω₂.center).length > abs (ω₂.radius - ω₁.radius))

protected def IsCircumscribed (ω₁ : Circle P) (ω₂ : Circle P) : Prop := (SEG ω₁.center ω₂.center).length = ω₁.radius + ω₂.radius

/- put the smaller circle first -/
protected def IsIncluded (ω₁ : Circle P) (ω₂ : Circle P) : Prop := (SEG ω₁.center ω₂.center).length < ω₂.radius - ω₁.radius

/- put the smaller circle first -/
protected def IsInscribed (ω₁ : Circle P) (ω₂ : Circle P) : Prop := ((SEG ω₁.center ω₂.center).length = ω₂.radius - ω₁.radius) ∧ (ω₁.center ≠ ω₂.center)

end Circle

scoped infix : 50 "Separate" => Circle.IsSeparated
scoped infix : 50 "Intersect" => Circle.IsIntersected
scoped infix : 50 "Circumscribe" => Circle.IsCircumscribed
scoped infix : 50 "IncludeIn" => Circle.IsIncluded
scoped infix : 50 "InscribeIn" => Circle.IsInscribed

namespace Circle

theorem CC_separated_pt_outside_second_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ Separate ω₂) (h₂ : A LiesOn ω₁) : A LiesOut ω₂ := sorry

theorem CC_separated_pt_outside_first_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ Separate ω₂) (h₂ : A LiesOn ω₂) : A LiesOut ω₁ := sorry


def CC_Circumscribe_Point {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Circumscribe ω₂) : P := sorry

theorem CC_circumscribe_point_lieson_circles {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Circumscribe ω₂) : ((CC_Circumscribe_Point h) LiesOn ω₁) ∧ ((CC_Circumscribe_Point h) LiesOn ω₂) := sorry

theorem CC_circumscribe_point_lieson_center_seg {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Circumscribe ω₂) : (CC_Circumscribe_Point h) LiesOn (SEG ω₁.center ω₂.center) := sorry


theorem CC_inscribed_pt_inside_second_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ InscribeIn ω₂) (h₂ : A LiesOn ω₁) : A LiesIn ω₂ := sorry

def CC_Inscribe_Point {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ InscribeIn ω₂) : P := sorry

theorem CC_inscribe_point_lieson_circles {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ InscribeIn ω₂) : ((CC_Inscribe_Point h) LiesOn ω₁) ∧ ((CC_Inscribe_Point h) LiesOn ω₂) := sorry

theorem CC_inscribe_point_lieson_center_ray {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ InscribeIn ω₂) : (CC_Inscribe_Point h) LiesOn (RAY ω₂.center ω₁.center h.2) := sorry


theorem CC_included_pt_isint_second_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ IncludeIn ω₂) (h₂ : A LiesOn ω₁) : Circle.IsInt A ω₂ := sorry

theorem CC_included_pt_outside_first_circle {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h₁ : ω₁ IncludeIn ω₂) (h₂ : A LiesOn ω₂) : A LiesOut ω₁ := sorry


@[ext]
structure CCInxpts (P : Type _) [EuclideanPlane P] where
  left : P
  right : P

def CC_Intersected_pts {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : CCInxpts P where
  left := sorry
  right := sorry

theorem CC_inx_pts_distinct {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : (CC_Intersected_pts h).left ≠ (CC_Intersected_pts h).right := sorry

theorem CC_inx_pts_lieson_circles {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : ((CC_Intersected_pts h).left LiesOn ω₁) ∧ ((CC_Intersected_pts h).left LiesOn ω₂) ∧ ((CC_Intersected_pts h).right LiesOn ω₁) ∧ ((CC_Intersected_pts h).right LiesOn ω₂) := sorry

lemma CC_intersected_centers_ne {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : ω₁.center ≠ ω₂.center := sorry

theorem CC_inx_pts_line_perp_center_line {ω₁ : Circle P} {ω₂ : Circle P} (h : ω₁ Intersect ω₂) : (LIN (CC_Intersected_pts h).left (CC_Intersected_pts h).right (CC_inx_pts_distinct h).symm) ⟂ (LIN ω₁.center ω₂.center (CC_intersected_centers_ne h).symm) := sorry

/- different circles have at most two intersections -/
lemma CC_inx_pt_not_lieson_center_line {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h : ω₁ Intersect ω₂) (h₁ : A LiesOn ω₁) (h₂ : A LiesOn ω₂) : ¬(A LiesOn (LIN ω₁.center ω₂.center (CC_intersected_centers_ne h).symm)) := sorry

theorem CC_inx_pt_liesonleft_center_ray_eq_leftinxpt {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h : ω₁ Intersect ω₂) (h₁ : A LiesOn ω₁) (h₂ : A LiesOn ω₂) (h₃ : A LiesOnLeft (RAY ω₁.center ω₂.center (CC_intersected_centers_ne h).symm)) : A = (CC_Intersected_pts h).left := sorry

theorem CC_inx_pt_liesonright_center_ray_eq_rightinxpt {ω₁ : Circle P} {ω₂ : Circle P} {A : P} (h : ω₁ Intersect ω₂) (h₁ : A LiesOn ω₁) (h₂ : A LiesOn ω₂) (h₃ : A LiesOnRight (RAY ω₁.center ω₂.center (CC_intersected_centers_ne h).symm)) : A = (CC_Intersected_pts h).right := sorry

end Circle

end CC

end EuclidGeom
