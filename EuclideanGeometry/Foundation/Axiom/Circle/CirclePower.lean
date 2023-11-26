import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Circle.CCPosition
import EuclideanGeometry.Foundation.Axiom.Circle.LCPosition

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Circle

-- Define the power of a point P relative to a circle ω with center O and radius r to be OP ^ 2 - r ^ 2
def power (ω : Circle P) (p : P) : ℝ := dist ω.center p ^ 2 - ω.radius ^ 2

theorem inside_circle_iff_power_npos (p : P) (ω : Circle P) : p LiesIn ω ↔ ω.power p ≤  0 := sorry

theorem interior_of_circle_iff_power_neg (p : P) (ω : Circle P) : p LiesInt ω ↔ ω.power p < 0 := sorry

theorem lies_on_circle_iff_power_zero (p : P) (ω : Circle P) : p LiesOn ω ↔ ω.power p = 0 := sorry

theorem outside_circle_iff_power_pos (p : P) (ω : Circle P) : p LiesOut ω ↔ 0 < ω.power p  := sorry

end Circle

section tangent

namespace Circle

@[ext]
structure Tangents (P : Type _) [EuclideanPlane P] where
  left : P
  right : P

lemma tangent_circle_intersected {ω : Circle P} {p : P} (h : p LiesOut ω) : (Circle.mk_pt_pt_diam p ω.center (pt_liesout_ne_center h).symm) Intersect ω := sorry

def pt_tangent_circle_pts {ω : Circle P} {p : P} (h : p LiesOut ω) : Tangents P where
  left := (CC_Intersected_pts (tangent_circle_intersected h)).left
  right := (CC_Intersected_pts (tangent_circle_intersected h)).right

theorem tangents_lieson_circle {ω : Circle P} {p : P} (h : p LiesOut ω) : ((pt_tangent_circle_pts h).left LiesOn ω) ∧ ((pt_tangent_circle_pts h).right LiesOn ω) := by
  rcases CC_inx_pts_lieson_circles (tangent_circle_intersected h) with ⟨_, ⟨h₂, ⟨_, h₄⟩⟩⟩
  exact ⟨h₂, h₄⟩

lemma tangents_ne_pt {ω : Circle P} {p : P} (h : p LiesOut ω) : ((pt_tangent_circle_pts h).left ≠ p) ∧ ((pt_tangent_circle_pts h).right ≠ p) := sorry

theorem line_tangent_circle {ω : Circle P} {p : P} (h : p LiesOut ω) : ((DLIN p (pt_tangent_circle_pts h).left (tangents_ne_pt h).1) Tangent ω) ∧ ((DLIN p (pt_tangent_circle_pts h).right (tangents_ne_pt h).2) Tangent ω) := sorry

theorem tangent_pts_eq_tangents {ω : Circle P} {p : P} (h : p LiesOut ω) : (DirLC_Tangent_pt (line_tangent_circle h).1 = (pt_tangent_circle_pts h).left) ∧ (DirLC_Tangent_pt (line_tangent_circle h).2 = (pt_tangent_circle_pts h).right) := sorry

theorem length_of_tangent {ω : Circle P} {p : P} (h : p LiesOut ω) : dist p (pt_tangent_circle_pts h).left = dist p (pt_tangent_circle_pts h).right := sorry

theorem tangent_and_intersected_chord_theorem {ω : Circle P} {p : P} (h : p LiesOut ω) : sorry := sorry

end Circle

end tangent

section power

namespace Circle

theorem circle_power_thm {ω : Circle P} {p : P} {l : DirLine P} (h₁ : DirLine.IsIntersected l ω) (h₂ : p LiesOn l) : sorry := sorry

theorem chord_power_thm {ω : Circle P} {p : P} {l : DirLine P} (h₁ : DirLine.IsIntersected l ω) (h₂ : p LiesOn l) (h₃ : p LiesInt ω) : (dist p (DirLC_Intersected_pts h₁).front) * (dist p (DirLC_Intersected_pts h₁).back) = - power ω p := sorry

theorem secant_power_thm {ω : Circle P} {p : P} {l : DirLine P} (h₁ : DirLine.IsIntersected l ω) (h₂ : p LiesOn l) (h₃ : p LiesOut ω) : (dist p (DirLC_Intersected_pts h₁).front) * (dist p (DirLC_Intersected_pts h₁).back) = power ω p := sorry

end Circle

end power

section radical_axis

namespace Circle

end Circle

end radical_axis

end EuclidGeom
