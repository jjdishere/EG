import EuclideanGeometry.Foundation.Axiom.Position
import EuclideanGeometry.Foundation.Axiom.Ray_ex
import EuclideanGeometry.Foundation.Axiom.Angle_ex

/- This file discuss the relative positions of points and rays on a plane. -/
noncomputable section
namespace EuclidGeom


variable {P : Type _} [EuclideanPlane P] 

theorem pts_are_distinct_of_two_rays_of_oangle (oang : OAngle P) (nontriv : oangle.is_nontriv) (A B : P) (ha : A LiesOnIntRay oangle.start_ray) (hb : B LiesOnIntRay oangle.end_ray) : A ≠ B := by sorry


/- Position of three (distinct) points.  Giving to colinear (futher classification) -/
-- `see line_ex`


end EuclidGeom