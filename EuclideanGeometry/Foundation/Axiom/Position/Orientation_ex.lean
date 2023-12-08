import EuclideanGeometry.Foundation.Axiom.Position.Orientation
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex

/- This file discuss the relative positions of points and rays on a plane. -/
noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem pts_are_distinct_of_two_rays_of_angle (ang : Angle P) (nontriv : ang.IsND) (A B : P) (ha : A LiesInt ang.start_ray) (hb : B LiesInt ang.end_ray) : A ≠ B := by sorry


/- Position of three (distinct) points.  Giving to colinear (futher classification) -/
-- `see line_ex`

-- If a point does not lie on the line associated to the ray, then it is either on the left or the right of the ray

theorem Ray.left_iff_not_right_of_not_lies_on {a : P} {l : Ray P} (h : ¬ (a LiesOn l)) : (a LiesOnLeft l) ↔ ¬ (a LiesOnRight l) := sorry

theorem Ray.not_lies_on_iff_left_or_right (a : P) (l : Ray P) : (¬ (a LiesOn l)) ↔ (a LiesOnLeft l) ∨ (a LiesOnRight l) := sorry

end EuclidGeom
