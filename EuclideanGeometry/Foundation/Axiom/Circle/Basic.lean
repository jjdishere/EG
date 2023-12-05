import EuclideanGeometry.Foundation.Axiom.Position.Orientation
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash

noncomputable section
namespace EuclidGeom

/- Class of Circles-/
@[ext]
structure Circle (P : Type _) [EuclideanPlane P] where
  center : P
  radius : ℝ
  rad_pos : 0 < radius

variable {P : Type _} [EuclideanPlane P]

namespace Circle

def mk_pt_pt (O A : P) (h : A ≠ O) : Circle P where
  center := O
  radius := dist O A
  rad_pos := dist_pos.mpr h.symm

def mk_pt_pt_pt (A B C: P) (h : ¬ colinear A B C) : Circle P := sorry

end Circle

scoped notation "CIR" => Circle.mk_pt_pt

scoped notation "⨀" => Circle.mk_pt_pt

namespace Circle

def mk_pt_radius (O : P) {r : ℝ} (rpos : r > 0) : Circle P where
  center := O
  radius := r
  rad_pos := rpos

def mk_pt_pt_diam (A B : P) (h : B ≠ A) : Circle P where
  center := (SEG A B).midpoint
  radius := dist (SEG A B).midpoint B
  rad_pos := dist_pos.mpr (SEG_nd A B h).midpt_ne_target

end Circle

section coercion

-- this should not live here, this belongs to construction.
-- def Triangle_nd.toCir (tr_nd : Triangle_nd P) : Circle P := sorry

end coercion


section position

namespace Circle

/- `One seldom uses Inside a circle in reality.` Should we delete this? Int On Out is enough-/
protected def IsInside (p : P) (ω : Circle P) : Prop := dist ω.center p ≤  ω.radius

protected def IsOn (p : P) (ω : Circle P) : Prop := dist ω.center p = ω.radius

protected def IsInt (p : P) (ω : Circle P) : Prop := dist ω.center p < ω.radius

def IsOutside (p : P) (ω : Circle P) : Prop := ω.radius < dist ω.center p

protected def carrier (ω : Circle P) : Set P := { p : P | Circle.IsOn p ω }

protected def interior (ω : Circle P) : Set P := { p : P | Circle.IsInt p ω }
--`Interior is NOT a subset of carrier`

instance : Fig (Circle P) P where
  carrier := Circle.carrier

instance : Interior (Circle P) P where
  interior := Circle.interior

end Circle

/- `One seldom uses Inside a circle in reality.` Should we delete this? Int On Out is enough-/
scoped infix : 50 " LiesIn " => Circle.IsInside

scoped infix : 50 " LiesOut " => Circle.IsOutside

namespace Circle

theorem pt_liesout_ne_center {p : P} {ω : Circle P} (h : p LiesOut ω) : p ≠ ω.center := by
  apply dist_pos.mp
  rw [dist_comm]
  have : dist ω.center p > ω.radius := h
  have : ω.radius > 0 := ω.rad_pos
  linarith

theorem interior_of_circle_iff_inside_not_on_circle (p : P) (ω : Circle P) : p LiesInt ω ↔ (p LiesIn ω) ∧ (¬ p LiesOn ω) := by
  show dist ω.center p < ω.radius ↔ (dist ω.center p ≤ ω.radius) ∧ (¬ dist ω.center p = ω.radius)
  push_neg
  exact lt_iff_le_and_ne

-- Define a concept of segment to be entirely contained in a circle, to mean that the two endpoints of a segment to lie inside a circle.

def seg_lies_inside_circle (l : Seg P) (ω : Circle P) : Prop := l.source LiesIn ω ∧ l.target LiesIn ω

end Circle

scoped infix : 50 " SegInCir " => Circle.seg_lies_inside_circle

namespace Circle

-- very hard question: if a segment lies inside a circle, then the interior point of a

theorem pt_lies_inside_circle_of_seg_inside_circle {l : Seg P} {ω : Circle P} (h : l SegInCir ω) {p : P} (lieson : p LiesInt l) : p LiesInt ω := sorry

end Circle

end position

-- ray with circle
-- line with circle
end EuclidGeom
