import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_ex
import EuclideanGeometry.Foundation.Axiom.Triangle.Trigonometric

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

-- Prefer to define IsIsocelesTriangle than to just state the properties. Isoceles triangle by definition has a prefered orientation


section IsocelesTriangles

def Triangle.IsIsoceles (tri : Triangle P) : Prop := tri.edge₂.length = tri.edge₃.length

theorem is_isoceles_tri_iff_ang_eq_ang_of_nd_tri {tri_nd : Triangle_nd P} : tri_nd.1.IsIsoceles ↔ (tri_nd.angle₂.value= - tri_nd.angle₃.value) := sorry
-- To show angle equal => sides equal, use anti-congruent of the triangle with itself. SAS

namespace Triangle

-- Changing the order of vertices 2 and 3 in an isoceles triangle does not change the property of being an isoceles triangle.
theorem is_isoceles_of_flip_vert_isoceles (tri : Triangle P) (h : tri.IsIsoceles) : tri.flip_vertices.IsIsoceles := by sorry



end Triangle


end IsocelesTriangles

-- Define regular triangle

def Triangle.IsRegular (tri : Triangle P) : Prop := tri.edge₁.length = tri.edge₂.length ∧ tri.edge₁.length = tri.edge₃.length

namespace Triangle

theorem isoceles_of_regular (tri : Triangle P) (h : tri.IsRegular) : tri.IsIsoceles := by sorry

-- Changing the order of vertices in a regular triangle does not change the property of being an regular triangle.
theorem regular_of_regular_flip_vert (tri : Triangle P) (h : tri.IsRegular) : tri.flip_vertices.IsRegular := by sorry

theorem regular_of_regular_perm_vert (tri : Triangle P) (h : tri.IsRegular) : tri.perm_vertices.IsRegular := by sorry


end Triangle

-- A nontrivial triangle is an regular triangle if and only if all of its angles are equal.
theorem regular_tri_iff_eq_angle_of_nd_tri (tri_nd : Triangle_nd P) : tri_nd.1.IsRegular ↔ tri_nd.angle₁.value = tri_nd.angle₂.value ∧ tri_nd.angle₁.value = tri_nd.angle₃.value := by sorry

-- An clockwise regular triangle has all angles being π/3

theorem ang_eq_sixty_deg_of_cclock_regular_tri (tri_nd : Triangle_nd P) (cclock : tri_nd.is_cclock) : tri_nd.angle₁.value= (π / 3) ∧ tri_nd.angle₂.value = π / 3 ∧ tri_nd.angle₃.value = π / 3 := by sorry

-- An anticlockwise equilateral triangle has all angles being - π/3

theorem ang_eq_sixty_deg_of_acclock_regular_tri (tri_nd : Triangle_nd P) (acclock : ¬ tri_nd.is_cclock) : tri_nd.angle₁.value= - π / 3 ∧ tri_nd.angle₂.value = - π / 3 ∧ tri_nd.angle₃.value = - π / 3 := by sorry

-- An isoceles triangle is an equilateral triangle if one of its angle is π/3 (or -π /3). Here there are two possibilities

theorem regular_tri_of_isoceles_tri_of_fst_ang_eq_sixty_deg(tri_nd : Triangle_nd P) (h : tri_nd.angle₁.value = π /3 ∨ tri_nd.angle₁.value = - π / 3) : tri_nd.1.IsRegular := by sorry

theorem regular_tri_of_isoceles_tri_of_snd_ang_eq_sixty_deg (tri_nd : Triangle_nd P) (h : tri_nd.angle₂.value = π /3 ∨ tri_nd.angle₂.value = - π / 3) : tri_nd.1.IsRegular:= by sorry

theorem regular_tri_of_isoceles_tri_of_trd_ang_eq_sixty_deg (tri_nd : Triangle_nd P) (h : tri_nd.angle₃.value = π /3 ∨ tri_nd.angle₃.value = - π / 3) : tri_nd.1.IsRegular:= by sorry

end EuclidGeom