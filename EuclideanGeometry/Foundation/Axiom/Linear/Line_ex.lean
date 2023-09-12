import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex

noncomputable section


namespace EuclidGeom


variable {P : Type _} [EuclideanPlane P] 



-- compatibility with coersion to Proj
section compatibility_coersion_to_Proj

theorem toProj_eq_toLine_toProj_of_Ray (ray : Ray P) : ray.toProj = ray.toLine.toProj := by sorry

end compatibility_coersion_to_Proj


-- A point lies on a line associated to a ray if and only if it lies on the ray or the reverse of the ray


theorem Ray.lies_on_line_of_ray_iff_lies_on_ray_or_lies_on_rev_of_ray (a : P) (l : Ray P) : (a LiesOn l) ↔ (a LiesOn l) ∨
 (a LiesOn l.reverse) := sorry

end EuclidGeom