import EuclideanGeometry.Foundation.Axiom.Triangle
import EuclideanGeometry.Foundation.Axiom.Triangle_ex
import EuclideanGeometry.Foundation.Axiom.Trigonometric

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

-- Prefer to define IsIsocelesTriangle than to just state the properties. Isoceles triangle by definition has a prefered orientation

namespace Triangle

section Isoceles_Triangles

def IsIsoceles (tri : Triangle P) : Prop := tri.edge₂.length = tri.edge₃.length

theorem isoceles_iff_two_angles_eq_of_nontriv_triangle (tri : Triangle P) (nontriv : tri.is_nontriv) : tri.IsIsoceles ↔ (tri.angle₂ nontriv = - tri.angle₃ nontriv) := sorry
-- To show angle equal => sides equal, use anti-congruent of the triangle with itself.


-- Changing the order of vertices 2 and 3 in an isoceles triangle does not change the property of being an isoceles triangle.
theorem isoceles_of_flip_vertices (tri : Triangle P) (h : tri.IsIsoceles) : tri.flip_vertices.IsIsoceles := by sorry




end Isoceles_Triangles

-- Define equilateral triangle

def IsEquilateral (tri : Triangle P) : Prop := tri.edge₁.length = tri.edge₂.length ∧ tri.edge₁.length = tri.edge₃.length

theorem Isoceles_of_Equilateral (tri : Triangle P) (h : tri.IsEquilateral) : tri.IsIsoceles := by sorry

-- Changing the order of vertices in an equilateral triangle does not change the property of being an isoceles triangle.
theorem equilateral_of_flip_vertices (tri : Triangle P) (h : tri.IsEquilateral) : tri.flip_vertices.IsEquilateral := by sorry

theorem equilateral_of_perm_vertices (tri : Triangle P) (h : tri.IsEquilateral) : tri.perm_vertices.IsEquilateral := by sorry

-- A nontrivial triangle is an equilateral triangle if and only if all of its angles are equal.

theorem equilateral_iff_eq_angle_of_nontriv (tri : Triangle P) (nontriv : tri.is_nontriv) : tri.IsEquilateral ↔ tri.angle₁ = tri.angle₂ ∧ tri.angle₁ = tri.angle₃ := by sorry

-- An clockwise equilateral triangle has all angles being π/3

theorem sixty_degree_of_cclock_equilateral_tri (tri : Triangle P) (nontriv : tri.is_nontriv) (cclock : tri.is_cclock nontriv) : tri.angle₁ nontriv = (π / 3) ∧ tri.angle₂ nontriv = π / 3 ∧ tri.angle₃ nontriv = π / 3 := by sorry

-- An anticlockwise equilateral triangle has all angles being - π/3

theorem neg_sixty_degree_of_acclock_equilateral_tri (tri : Triangle P) (nontriv : tri.is_nontriv) (acclock : ¬ tri.is_cclock nontriv) : tri.angle₁ nontriv = - π / 3 ∧ tri.angle₂ nontriv = - π / 3 ∧ tri.angle₃ nontriv = - π / 3 := by sorry

-- An isoceles triangle is an equilateral triangle if one of its angle is π/3 (or -π /3). Here there are two possibilities

theorem equilateral_of_isoceles_of_sixty_degree_1 (tri : Triangle P) (nontriv : tri.is_nontriv) (h : tri.angle₁ nontriv = π /3 ∨ tri.angle₁ nontriv = - π / 3) : tri.IsEquilateral := by sorry

theorem equilateral_of_isoceles_of_sixty_degree_2 (tri : Triangle P) (nontriv : tri.is_nontriv) (h : tri.angle₂ nontriv = π /3 ∨ tri.angle₂ nontriv = - π / 3) : tri.IsEquilateral := by sorry

end Triangle

end EuclidGeom