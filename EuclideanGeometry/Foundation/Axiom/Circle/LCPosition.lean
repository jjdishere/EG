import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

section DirLC

namespace Circle

protected def DirLine.IsDisjoint (l : DirLine P) (ω : Circle P) : Prop := dist_pt_line ω.center l.toLine > ω.radius

protected def DirLine.IsTangent (l : DirLine P) (ω : Circle P) : Prop := dist_pt_line ω.center l.toLine = ω.radius

protected def DirLine.IsSecant (l : DirLine P) (ω : Circle P) : Prop := dist_pt_line ω.center l.toLine < ω.radius

protected def DirLine.IsIntersected (l : DirLine P) (ω : Circle P) : Prop := dist_pt_line ω.center l.toLine ≤ ω.radius

end Circle

scoped infix : 50 "Secant" => Circle.DirLine.IsSecant
scoped infix : 50 "Tangent" => Circle.DirLine.IsTangent
scoped infix : 50 "Disjoint" => Circle.DirLine.IsDisjoint

namespace Circle

theorem DirLC_disjoint_pt_liesout_circle {l : DirLine P} {ω : Circle P} {A : P} (h : l Disjoint ω) (hh : A LiesOn l.toLine) : A LiesOut ω := sorry


theorem DirLC_intersect_iff_tangent_or_secant {l : DirLine P} {ω : Circle P} : (DirLine.IsIntersected l ω) ↔ (l Tangent ω) ∨ (l Secant ω) := sorry

@[ext]
structure DirLCInxpts (P : Type _) [EuclideanPlane P] where
  front : P
  back : P

def DirLC_Intersected_pts {l : DirLine P} {ω : Circle P} (h : DirLine.IsIntersected l ω) : DirLCInxpts P where
  front := sorry
  back := sorry

theorem DirLC_inx_pts_lieson_circle {l : DirLine P} {ω : Circle P} (h : DirLine.IsIntersected l ω) : ((DirLC_Intersected_pts h).front LiesOn ω) ∧ ((DirLC_Intersected_pts h).back LiesOn ω) := sorry

theorem DirLC_inx_pts_same_iff_tangent {l : DirLine P} {ω : Circle P} (h : DirLine.IsIntersected l ω) : (DirLC_Intersected_pts h).front = (DirLC_Intersected_pts h).back ↔ (l Tangent ω) := sorry

def DirLC_Tangent_pt {l : DirLine P} {ω : Circle P} (h : l Tangent ω) : P := (DirLC_Intersected_pts (DirLC_intersect_iff_tangent_or_secant.mpr (Or.inl h))).front

lemma DirLC_tangent_pt_ne_center {l : DirLine P} {ω : Circle P} (h : l Tangent ω) : DirLC_Tangent_pt h ≠ ω.center := sorry

theorem DirLC_tangent_pt_center_perp_line {l : DirLine P} {ω : Circle P} (h : l Tangent ω) : (LIN ω.center (DirLC_Tangent_pt h) (DirLC_tangent_pt_ne_center h)) ⟂ l.toLine := sorry

/- DirLine and circle have at most two intersections. -/
/- maybe not need -/
theorem DirLC_intersection_eq_inxpts {l : DirLine P} {ω : Circle P} {A : P} (h : DirLine.IsIntersected l ω) (h₁ : A LiesOn l.toLine) (h₂ : A LiesOn ω) : (A = (DirLC_Intersected_pts h).front) ∨ (A = (DirLC_Intersected_pts h).back) := sorry

end Circle

end DirLC


section LC

namespace Circle

protected def Line.IsDisjoint (l : Line P) (ω : Circle P) : Prop := dist_pt_line ω.center l > ω.radius

protected def Line.IsTangent (l : Line P) (ω : Circle P) : Prop := dist_pt_line ω.center l = ω.radius

protected def Line.IsSecant (l : Line P) (ω : Circle P) : Prop := dist_pt_line ω.center l < ω.radius

protected def Line.IsIntersected (l : Line P) (ω : Circle P) : Prop := dist_pt_line ω.center l ≤ ω.radius

end Circle

scoped infix : 50 "Secant" => Circle.Line.IsSecant
scoped infix : 50 "Tangent" => Circle.Line.IsTangent
scoped infix : 50 "Disjoint" => Circle.Line.IsDisjoint

end LC

end EuclidGeom
