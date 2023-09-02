import EuclideanGeometry.Foundation.Axiom.Position

noncomputable section
namespace EuclidGeom



/- Fundations of triangles -/

/- Definition of oriented triangles: three vertices, and three oriented segments, AND ORIENTATION!!!, plus compatibility.  ???  So we need to use Is_on_the_left_of_ray as a type Prop, and us this to define orientation.  -/
-- to be settled
class LTriangle (P : Type _) [EuclideanPlane P] where 
  point1 : P
  point2 : P
  point3 : P
  nontriv1 : (point2 ≠ point3) 
  nontriv2 : (point3 ≠ point1)
  nontriv3 : (point1 ≠ point2)
  left : (third IsOnLeftOf (Ray.mk' point1 point2 nontriv3))

namespace LTriangle

variable {P : Type _} [EuclideanPlane P]

def edge1 (tr : LTriangle P) : DirSeg P:= DirSeg.mk' tr.2 tr.3 tr.nontriv1

def edge2 (tr : LTriangle P) : DirSeg P:= DirSeg.mk' tr.3 tr.1 tr.nontriv2

def edge3 (tr : LTriangle P) : DirSeg P:= DirSeg.mk' tr.1 tr.2 tr.nontriv3

def IsInside  (A : P) (tr : LTriangle P) : Prop := A IsOnLeftOf tr.edge1 ∧ A IsOnLeftOf tr.edge2 ∧ A IsOnLeftOf tr.edge3

end LTriangle

scoped infix : 50 "IsInsideLTriangle" => LTriangle.IsInside


/- Function to determine the orientation of a triangle. -/

/- Define interior of an oriented triangle -/


/- congruences of triangles, separate definitions for reversing orientation or not, (requiring all sides and angles being the same)-/

/- criteria of congruence of triangles. -/

end EuclidGeom