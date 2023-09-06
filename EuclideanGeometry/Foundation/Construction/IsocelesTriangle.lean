import EuclideanGeometry.Foundation.Axiom.Triangle

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

-- Prefer to define IsIsocelesTriangle than to just state the properties. Isoceles triangle by definition has a prefered orientation

namespace Triangle

def IsIsocTri (tr : Triangle P) : Prop := tr.edge₂ = tr.edge₃

theorem IsIsocTri_iff_two_angles_eq_of_nontriv_triangle (tr : Triangle P) (nontriv : tr.is_nontriv) : tr.IsIsocTri ↔ (tr.angle₂ nontriv = - tr.angle₃ nontriv) := sorry
-- To show angle equal => sides equal, use anti-congruent of the triangle with itself.


end Triangle

end EuclidGeom