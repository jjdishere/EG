import EuclideanGeometry.Foundation.Axiom.Position
import EuclideanGeometry.Foundation.Axiom.Ray_ex
import EuclideanGeometry.Foundation.Axiom.Angle_ex

/- This file discuss the relative positions of points and rays on a plane. -/
noncomputable section
namespace EuclidGeom


variable {P : Type _} [EuclideanPlane P] 

theorem pts_are_distinct_of_two_rays_of_oangle (oang : OAngle P) (nontriv : oang.is_nontriv) (A B : P) (ha : A LiesOnIntRay oang.start_ray) (hb : B LiesOnIntRay oang.end_ray) : A ≠ B := by sorry


/- Position of three (distinct) points.  Giving to colinear (futher classification) -/
-- `see line_ex`




section midpoint

-- midpoint of a segment

variable {P : Type _} [EuclideanPlane P]

namespace Seg

def midpoint (l : Seg P) : P := (l.target -ᵥ l.source) /2 +ᵥ l.source

-- The midpoint of a segment lies on the segment 

theorem mid_point_lies_on (l : Seg P) : l.midpoint LiesOnSeg l := by sorry

-- A point is the mid opint of a segment if and only it defines the same vector to the source and the target of the segment

theorem mid_pt_iff_same_vector_to_source_and_target (p : P) (l : Seg P) : p = l.midpoint ↔ (SEG l.source p).toVec = (SEG p l.target).toVec := by sorry

-- The midpoint has same distance to the two end points of the segment

theorem same_distance_of_mid_point_of_seg (l : Seg P) : (SEG l.source l.midpoint).length = (SEG l.midpoint l.target).length := by sorry

-- A point is the mid-point of a nontrivial segment if and only if it lines on the segment and 

theorem is_midpoint_iff_lieson_and_same_distance_of_nontriv (p : P) (l : Seg P) (nontriv : l.is_nontriv) : p = l.midpoint ↔ p LiesOnSeg l ∧ (SEG l.source p).length = (SEG p l.target).length := by sorry

end Seg

end midpoint

end EuclidGeom