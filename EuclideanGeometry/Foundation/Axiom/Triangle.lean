import EuclideanGeometry.Foundation.Axiom.Position

noncomputable section
namespace EuclidGeom

open Classical

/- Class of generalized triangles -/
class Triangle (P : Type _) [EuclideanPlane P] where 
  point₁ : P
  point₂ : P
  point₃ : P

namespace Triangle

variable {P : Type _} [EuclideanPlane P]

--implies  1 left of 23, 2 left of 31

-- not is_cclock implies 1 right of 23, ..., ...

def edge₁ (tr : Triangle P) : Seg P:= Seg.mk tr.2 tr.3

def edge₂ (tr : Triangle P) : Seg P:= Seg.mk tr.3 tr.1

def edge₃ (tr : Triangle P) : Seg P:= Seg.mk tr.1 tr.2

def area (tr : Triangle P) : ℝ := sorry 

end Triangle

section nondeg

namespace Triangle
variable {P : Type _} [EuclideanPlane P] (tr : Triangle P) (nontriv : ¬ colinear tr.1 tr.2 tr.3)

def nontriv₁ := (ne_of_not_colinear nontriv).1

def nontriv₂ := (ne_of_not_colinear nontriv).2.1

def nontriv₃ := (ne_of_not_colinear nontriv).2.2

/- Only nondegenerate triangles can talk about orientation -/
def is_cclock : Prop := tr.3 LiesOnLeft (Ray.mk_pt_pt tr.1 tr.2 (tr.nontriv₃ nontriv))

end Triangle

end nondeg

namespace Triangle

variable {P : Type _} [EuclideanPlane P]

def IsInside  (A : P) (tr : Triangle P) : Prop := by 
  by_cases colinear tr.1 tr.2 tr.3
  · exact False
  · exact (if tr.is_cclock h then A LiesOnLeft tr.edge₁.toRay_of_nontriv (tr.nontriv₁ h) ∧ A LiesOnLeft tr.edge₂.toRay_of_nontriv (tr.nontriv₂ h) ∧ A LiesOnLeft tr.edge₃.toRay_of_nontriv (tr.nontriv₃ h) else A LiesOnRight tr.edge₁.toRay_of_nontriv (tr.nontriv₁ h)∧ A LiesOnRight tr.edge₂.toRay_of_nontriv (tr.nontriv₂ h) ∧ A LiesOnRight tr.edge₃.toRay_of_nontriv (tr.nontriv₃ h))

end Triangle

scoped infix : 50 "IsInsideTriangle" => Triangle.IsInside

/- Function to determine the orientation of a triangle. -/

/- Define interior of an oriented triangle -/


/- congruences of triangles, separate definitions for reversing orientation or not, (requiring all sides and angles being the same)-/

/- criteria of congruence of triangles. -/

end EuclidGeom