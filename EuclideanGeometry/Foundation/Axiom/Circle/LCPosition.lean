import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

section LCPosition

namespace Circle

protected def IsSeparated (l : Line P) (ω : Circle P) : Prop := dist_pt_line ω.center l > ω.radius

protected def IsTangent (l : Line P) (ω : Circle P) : Prop := dist_pt_line ω.center l = ω.radius

protected def IsIntersected (l : Line P) (ω : Circle P) : Prop := dist_pt_line ω.center l < ω.radius

end Circle

scoped infix : 50 "Separate" => Circle.IsSeparated
scoped infix : 50 "Tangent" => Circle.IsTangent
scoped infix : 50 "Intersect" => Circle.IsIntersected

def Tangent_point {l : Line P} {ω : Circle P} (ht : l Tangent ω) : P := perp_foot ω.center l

theorem Tangent_point_LiesOn_Circle {l : Line P} {ω : Circle P} (ht : l Tangent ω) : (Tangent_point ht) LiesOn ω := sorry

end LCPosition


section ray_position

namespace Circle

def source_Int_Of_Intersection_one (r : Ray P) (ω : Circle P) : Prop := (r.source LiesInt ω) ∧ (r.toLine Intersect ω)

/- ************************************************ -/
/- to prove this theorem, we need a lemma: the distance between a point and any point on a line is bigger than the distance between this point and this line -/
theorem Ray_Source_Int_toLine_Intersect {r : Ray P} {ω : Circle P} (h : r.source LiesInt ω) : r.toLine Intersect ω := sorry

/- use the perp foot -/
def source_Int_Intersection {r : Ray P} {ω : Circle P} (h : source_Int_Of_Intersection_one r ω) : P := ((Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center r.toLine) ^ 2)) • r.2.1) +ᵥ (perp_foot ω.center r.toLine)

/- use the Pythagoras theorem -/
theorem source_Int_Intersection_LiesOn_Circle {r : Ray P} {ω : Circle P} (h : source_Int_Of_Intersection_one r ω) : (source_Int_Intersection h) LiesOn ω := sorry

def source_Out_Of_Intersection_zero (r : Ray P) (ω : Circle P) : Prop := (r.source LiesOut ω) ∧ (r.toLine Separate ω)

def source_Out_Of_Intersection_two (r : Ray P) (ω : Circle P) : Prop := (r.source LiesOut ω) ∧ (r.toLine Intersect ω)

/- (-Dir) +ᵥ perp foot -/
def source_Out_Intersection_in_seg {r : Ray P} {ω : Circle P} (h : source_Out_Of_Intersection_two r ω) : P := (-(Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center r.toLine) ^ 2)) • r.2.1) +ᵥ (perp_foot ω.center r.toLine)

/- Dir +ᵥ perp foot -/
def source_Out_Intersection_out_seg {r : Ray P} {ω : Circle P} (h : source_Out_Of_Intersection_two r ω) : P := ((Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center r.toLine) ^ 2)) • r.2.1) +ᵥ (perp_foot ω.center r.toLine)

theorem source_Out_Intersection_LiesOn_Circle {r : Ray P} {ω : Circle P} (h : source_Out_Of_Intersection_two r ω) : ((source_Out_Intersection_in_seg h) LiesOn ω) ∧ ((source_Out_Intersection_out_seg h) LiesOn ω) := sorry

def source_Out_Of_Tangent (r : Ray P) (ω : Circle P) : Prop := (r.source LiesOut ω) ∧ (r.toLine Tangent ω)

def source_Out_Tangent_point {r : Ray P} {ω : Circle P} (h : source_Out_Of_Tangent r ω) : P := Tangent_point h.right

theorem source_Out_Tangent_point_LiesOn_Circle {r : Ray P} {ω : Circle P} (h : source_Out_Of_Tangent r ω) : (source_Out_Tangent_point h) LiesOn ω := sorry

def source_On_Of_Tangent (r : Ray P) (ω : Circle P) : Prop := (r.source LiesOn ω) ∧ (r.toLine Tangent ω)

def source_On_Tangent_point {r : Ray P} {ω : Circle P} (h : source_On_Of_Tangent r ω) : P := r.source

def source_On_Of_Intersection_two (r : Ray P) (ω : Circle P) : Prop := (r.source LiesOn ω) ∧ (r.toLine Intersect ω)

def source_On_Intersection_not_self {r : Ray P} {ω : Circle P} (h : source_On_Of_Intersection_two r ω) : P := ((Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center r.toLine) ^ 2)) • r.2.1) +ᵥ (perp_foot ω.center r.toLine)

theorem source_On_Intersection_LiesOn_Circle {r : Ray P} {ω : Circle P} (h : source_On_Of_Intersection_two r ω) : (source_On_Intersection_not_self h) LiesOn ω := sorry

/- If a point is outside the circle, then we can construct two tangent rays, with their tangent points, which we can distinguish the rays with the position between circle.center and these tangent rays, and distinguish the points with the position between (RAY circle.center pt) and these tangent points. -/

/- ************************************************ -/
/- think how to construct the tangent points the simplest way -/

/- left means this tangent point lies on the left of (RAY circle.center pt) -/
def pt_Out_Left_Tangent_Point {p : P} {ω : Circle P} (h : p LiesOut ω) : P := sorry

def pt_Out_Right_Tangent_Point {p : P} {ω : Circle P} (h : p LiesOut ω) : P := sorry

theorem pt_Out_Tangent_Points_ne_self {p : P} {ω : Circle P} (h : p LiesOut ω) : ((pt_Out_Left_Tangent_Point h) ≠ p) ∧ ((pt_Out_Right_Tangent_Point h) ≠ p) := sorry

theorem pt_Out_Tangent_Points_LiesOn_Circle {p : P} {ω : Circle P} (h : p LiesOut ω) : ((pt_Out_Left_Tangent_Point h) LiesOn ω) ∧ ((pt_Out_Right_Tangent_Point h) LiesOn ω) := sorry

/- left means circle.center lies on the left of this tangent ray -/
def pt_Out_Left_Tangent_Ray {p : P} {ω : Circle P} (h : p LiesOut ω) : Ray P := RAY p (pt_Out_Left_Tangent_Point h) (pt_Out_Tangent_Points_ne_self h).left

def pt_Out_Right_Tangent_Ray {p : P} {ω : Circle P} (h : p LiesOut ω) : Ray P := RAY p (pt_Out_Right_Tangent_Point h) (pt_Out_Tangent_Points_ne_self h).right

/- ******************************************* -/
/- maybe need more theorems about the coercion -/

theorem pt_Out_Tangent_Rays_Tangent_Circle {p : P} {ω : Circle P} (h : p LiesOut ω) : ((pt_Out_Left_Tangent_Ray h) Tangent ω) ∧ ((pt_Out_Right_Tangent_Ray h) Tangent ω) := sorry

end Circle

end ray_position


section line_intersection

namespace Circle

/- left means this point lies on the left of the perpendicular ray with circle.center to be the source -/
/- ray.toDir * I +ᵥ perp foot -/
def Line_Intersection_Left_Point {l : Line P} {ω : Circle P} (h : l Intersect ω) : P := sorry

/- ray.toDir * (-I) +ᵥ perp foot -/
def Line_Intersection_Right_Point {l : Line P} {ω : Circle P} (h : l Intersect ω) : P := sorry

theorem Line_Intersection_Points_LiesOn_Line {l : Line P} {ω : Circle P} (h : l Intersect ω) : ((Line_Intersection_Left_Point h) LiesOn l) ∧ ((Line_Intersection_Right_Point h) LiesOn l) := sorry

theorem Line_Intersection_Points_LiesOn_Circle {l : Line P} {ω : Circle P} (h : l Intersect ω) : ((Line_Intersection_Left_Point h) LiesOn ω) ∧ ((Line_Intersection_Right_Point h) LiesOn ω) := sorry

end Circle

end line_intersection

end EuclidGeom
