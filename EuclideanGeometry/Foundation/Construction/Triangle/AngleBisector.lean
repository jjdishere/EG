import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Isometry.Rotation
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
/-!

-/
noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] 

namespace Angle

/- when the Angle is flat, bisector is on the left side-/
def bisector (ang : Angle P) : Ray P := sorry

def is_bisector (ang : Angle P) (ray : Ray P): Prop := sorry

def extended_bisector (ang : Angle P) : Line P := sorry

end Angle
/-definition property: lies on the bisector means bisect the angle-/
theorem lie_on_bisector (ang: Angle P) (A : P): sorry := sorry

/-extended bisector as the locus satisfying the sum of distance to each ray of the angle is 0 -/
theorem lie_on_extended_bisector_of_distance_zero (ang: Angle P) : sorry := sorry

/-bisector lies inside the angle-/

/-construct the intercentor as the intersection of two bisector-/

/-a triangle_nd admit an unique intercenter-/


def is_intercenter (triangle_nd : Triangle_nd P) (A : P) : sorry := sorry

theorem lie_on_bisector_of_lie_on_extended_bisector_inside_angle(ang : Angle P)  : sorry := sorry

/-the intercenter lies inside of the triangle-/

theorem intercenter_lies_in_triangle (triangle_nd : Triangle_nd P): sorry := sorry

end EuclidGeom