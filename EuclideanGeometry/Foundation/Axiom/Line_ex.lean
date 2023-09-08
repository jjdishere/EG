import EuclideanGeometry.Foundation.Axiom.Line
import EuclideanGeometry.Foundation.Axiom.Position_ex
import EuclideanGeometry.Foundation.Axiom.Ray_ex

noncomputable section


namespace EuclidGeom



variable {P : Type _} [EuclideanPlane P] 

-- A point lies on a line associated to a ray if and only if it lies on the ray or the reverse of the ray


theorem Ray.lies_on_line_of_ray_iff_lies_on_ray_or_lies_on_rev_of_ray (a : P) (l : Ray P) : (a LiesOnLine l) ↔ (a LiesOnRay l) ∨
 (a LiesOnRay l.reverse) := sorry

-- If a point does not lie on the line associated to the ray, then it is either on the left or the right of the ray

theorem Ray.left_iff_not_right_of_not_lies_on {a : P} {l : Ray P} (h : ¬ (a LiesOnLine l)) : (a LiesOnLeft l) ↔ ¬ (a LiesOnRight l) := sorry

theorem Ray.not_lies_on_iff_left_or_right (a : P) (l : Ray P) : (¬ (a LiesOnLine l)) ↔ (a LiesOnLeft l) ∨ (a LiesOnRight l) := sorry
  


end EuclidGeom