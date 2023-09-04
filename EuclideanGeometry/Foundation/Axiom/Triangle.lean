import EuclideanGeometry.Foundation.Axiom.Position

noncomputable section
namespace EuclidGeom
open Classical
/- Fundations of triangles -/

/- Definition of oriented triangles: three vertices, and three oriented segments, AND ORIENTATION!!!, plus compatibility.  ???  So we need to use Is_on_the_left_of_ray as a type Prop, and us this to define orientation.  -/
-- to be settled
class Triangle (P : Type _) [EuclideanPlane P] where 
  point₁ : P
  point₂ : P
  point₃ : P
  nontriv : ¬ colinear point₁ point₂ point₃

namespace Triangle

variable {P : Type _} [EuclideanPlane P]

def nontriv₁ (tr : Triangle P) := (ne_of_not_colinear tr.nontriv).1

def nontriv₂ (tr : Triangle P) := (ne_of_not_colinear tr.nontriv).2.1

def nontriv₃ (tr : Triangle P) := (ne_of_not_colinear tr.nontriv).2.2

def is_cclock (tr : Triangle P): Prop := tr.3 LiesOnLeft (Ray.mk_pt_pt tr.1 tr.2 tr.nontriv₃)

--implies  1 left of 23, 2 left of 31

-- not is_cclock implies 1 right of 23, ..., ...

def edge₁ (tr : Triangle P) : DSeg P:= DSeg.mk_pt_pt tr.2 tr.3 tr.nontriv₁

def edge₂ (tr : Triangle P) : DSeg P:= DSeg.mk_pt_pt tr.3 tr.1 tr.nontriv₂

def edge₃ (tr : Triangle P) : DSeg P:= DSeg.mk_pt_pt tr.1 tr.2 tr.nontriv₃

def IsInside  (A : P) (tr : Triangle P) : Prop := if tr.is_cclock then A LiesOnLeft tr.edge₁.toRay ∧ A LiesOnLeft tr.edge₂.toRay ∧ A LiesOnLeft tr.edge₃.toRay else A LiesOnRight tr.edge₁.toRay ∧ A LiesOnRight tr.edge₂.toRay ∧ A LiesOnRight tr.edge₃.toRay

def area (tr : Triangle P) : ℝ := sorry 

end Triangle

scoped infix : 50 "IsInsideLTriangle" => Triangle.IsInside


/- Function to determine the orientation of a triangle. -/

/- Define interior of an oriented triangle -/


/- congruences of triangles, separate definitions for reversing orientation or not, (requiring all sides and angles being the same)-/

/- criteria of congruence of triangles. -/

end EuclidGeom