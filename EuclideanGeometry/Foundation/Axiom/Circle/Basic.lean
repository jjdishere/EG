import EuclideanGeometry.Foundation.Axiom.Position.Orientation
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular

noncomputable section
namespace EuclidGeom

/- Class of Circles-/
@[ext]
class Circle (P : Type _) [EuclideanPlane P] where 
  center : P
  radius : ℝ
  rad_pos : 0 < radius

variable {P : Type _} [EuclideanPlane P]

namespace Circle

def mk_pt_pt (O A : P) (h : A ≠ O) : Circle P where
  center := O
  radius := (SEG O A).length
  rad_pos := (length_pos_iff_nd).mpr h

def mk_pt_pt_pt (A B C: P) (h : ¬ colinear A B C) : Circle P := sorry

end Circle

scoped notation "CIR" => Circle.mk_pt_pt

scoped notation "⨀" => Circle.mk_pt_pt

section coersion

-- this should not live here, this belongs to construction.
-- def Triangle_nd.toCir (tr_nd : Triangle_nd P) : Circle P := sorry

end coersion


section position

namespace Circle

-- Define the power of a point P relative to a circle ω with center O and radius r to be OP ^ 2 - r ^ 2

def power (ω : Circle P) (p : P) : ℝ := (SEG ω.center p).length ^ 2 - ω.radius ^ 2

/- `One seldom uses Inside a circle in reality.` Should we delete this? Int On Out is enough-/
protected def IsInside (p : P) (ω : Circle P) : Prop := (SEG ω.center p).length ≤  ω.radius

protected def IsOn (p : P) (ω : Circle P) : Prop := (SEG ω.center p).length = ω.radius

protected def IsInt (p : P) (ω : Circle P) : Prop := (SEG ω.center p).length < ω.radius

def IsOutside (p : P) (ω : Circle P) : Prop := ω.radius < (SEG ω.center p).length

protected def carrier (ω : Circle P) : Set P := { p : P | Circle.IsOn p ω }

protected def interior (ω : Circle P) : Set P := { p : P | Circle.IsInt p ω }

instance : Carrier P (Circle P) where
  carrier := fun ω => ω.carrier

instance : Interior P (Circle P) where
  interior := fun ω => ω.interior

end Circle 

/- `One seldom uses Inside a circle in reality.` Should we delete this? Int On Out is enough-/
scoped infix : 50 "LiesIn" => Circle.IsInside

scoped infix : 50 "LiesOut" => Circle.IsOutside

namespace Circle


theorem inside_circle_iff_power_neg (p : P) (ω : Circle P) : p LiesIn ω ↔ ω.power p ≤  0 := sorry

theorem interior_of_circle_iff_power_neg (p : P) (ω : Circle P) : p LiesInt ω ↔ ω.power p < 0 := sorry

theorem lies_on_circle_iff_power_zero (p : P) (ω : Circle P) : p LiesOn ω ↔ ω.power p = 0 := sorry

theorem outside_circle_iff_power_pos (p : P) (ω : Circle P) : p LiesOut ω ↔ 0 < ω.power p  := sorry

theorem interior_of_circle_iff_inside_not_on_circle (p : P) (ω : Circle P) : p LiesInt ω ↔ (p LiesIn ω) ∧ (¬ p LiesOn ω) := sorry

-- Define a concept of segment to be entirely contained in a circle, to mean that the two endpoints of a segment to lie inside a circle.

def seg_lies_inside_circle (l : Seg P) (ω : Circle P) : Prop := l.source LiesIn ω ∧ l.target LiesIn ω

end Circle

scoped infix : 50 "SegInCir" => Circle.seg_lies_inside_circle

namespace Circle

-- very hard question: if a segment lies inside a circle, then the interior point of a

theorem pt_lies_inside_circle_of_seg_inside_circle {l : Seg P} {ω : Circle P} (h : l SegInCir ω) {p : P} (lieson : p LiesInt l) : p LiesInt ω := sorry

end Circle

end position


section line_position

namespace Circle

def IsDeparture (l : Line P) (ω : Circle P) : Prop := dist_pt_line ω.center l > ω.radius

def IsTangent (l : Line P) (ω : Circle P) : Prop := dist_pt_line ω.center l = ω.radius

def IsIntersected (l : Line P) (ω : Circle P) : Prop := dist_pt_line ω.center l < ω.radius

end Circle

scoped infix : 50 "Departure" => Circle.IsDeparture
scoped infix : 50 "Tangent" => Circle.IsTangent
scoped infix : 50 "Intersect" => Circle.IsIntersected

def Tangent_point {l : Line P} {ω : Circle P} (ht : l Tangent ω) : P := perp_foot ω.center l

theorem Tangent_point_LiesOn_Circle {l : Line P} {ω : Circle P} (ht : l Tangent ω) : (Tangent_point ht) LiesOn ω := sorry

end line_position


section ray_position

namespace Circle

def source_Int_Of_Intersection_one (r : Ray P) (ω : Circle P) : Prop := (r.source LiesInt ω) ∧ (r.toLine Intersect ω)

def source_Int_Intersection {r : Ray P} {ω : Circle P} (h : source_Int_Of_Intersection_one r ω) : P := sorry

theorem source_Int_Intersection_LiesOn_Circle {r : Ray P} {ω : Circle P} (h : source_Int_Of_Intersection_one r ω) : (source_Int_Intersection h) LiesOn ω := sorry

def source_Out_Of_Intersection_zero (r : Ray P) (ω : Circle P) : Prop := (r.source LiesOut ω) ∧ (r.toLine Departure ω)

def source_Out_Of_Intersection_two (r : Ray P) (ω : Circle P) : Prop := (r.source LiesOut ω) ∧ (r.toLine Intersect ω)

def source_Out_Intersection_in_seg {r : Ray P} {ω : Circle P} (h : source_Out_Of_Intersection_two r ω) : P := sorry

def source_Out_Intersection_out_seg {r : Ray P} {ω : Circle P} (h : source_Out_Of_Intersection_two r ω) : P := sorry

theorem source_Out_Intersection_LiesOn_Circle {r : Ray P} {ω : Circle P} (h : source_Out_Of_Intersection_two r ω) : ((source_Out_Intersection_in_seg h) LiesOn ω) ∧ ((source_Out_Intersection_out_seg h) LiesOn ω) := sorry

def source_Out_Of_Tangent (r : Ray P) (ω : Circle P) : Prop := (r.source LiesOut ω) ∧ (r.toLine Tangent ω)

def source_Out_Tangent_point {r : Ray P} {ω : Circle P} (h : source_Out_Of_Tangent r ω) : P := sorry

theorem source_Out_Tangent_point_LiesOn_Circle {r : Ray P} {ω : Circle P} (h : source_Out_Of_Tangent r ω) : (source_Out_Tangent_point h) LiesOn ω := sorry

def source_On_Of_Tangent (r : Ray P) (ω : Circle P) : Prop := (r.source LiesOn ω) ∧ (r.toLine Tangent ω)

def source_On_Tangent_point {r : Ray P} {ω : Circle P} (h : source_On_Of_Tangent r ω) : P := r.source

def source_On_Of_Intersection_two (r : Ray P) (ω : Circle P) : Prop := (r.source LiesOn ω) ∧ (r.toLine Intersect ω)

def source_On_Intersection_not_self {r : Ray P} {ω : Circle P} (h : source_On_Of_Intersection_two r ω) : P := sorry

theorem source_On_Intersection_LiesOn_Circle {r : Ray P} {ω : Circle P} (h : source_On_Of_Intersection_two r ω) : (source_On_Intersection_not_self h) LiesOn ω := sorry

/- If a point is outside the circle, then we can construct two tangent rays which we can distinguish them with the position of circle.center and these tangent rays. -/
def pt_Out_Left_Tangent_Ray {p : P} {ω : Circle P} (h : p LiesOut ω) : Ray P := sorry

def pt_Out_Right_Tangent_Ray {p : P} {ω : Circle P} (h : p LiesOut ω) : Ray P := sorry

end Circle

end ray_position




-- ray with circle
-- line with circle
end EuclidGeom
