import EuclideanGeometry.Foundation.Axiom.Triangle

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] (tr : Triangle P) (tr_nd : Triangle_nd P)

namespace Triangle

def perm_vertices : (Triangle P) where
  point₁ := tr.point₂
  point₂ := tr.point₃
  point₃ := tr.point₁
  
-- We decide not to define reverse permutation of triangles, just do composition twice.

-- Permuting three times returns to the original triangle.
theorem eq_self_of_perm_vertices_three_times : tr.perm_vertices.perm_vertices.perm_vertices = tr := by sorry


-- flip vertices for triangles means to flip the second and the third vertices.

def flip_vertices : (Triangle P) where
  point₁ := tr.point₁
  point₂ := tr.point₃
  point₃ := tr.point₂

end Triangle

namespace Triangle_nd

def perm_vertices : (Triangle_nd P) := ⟨tr_nd.1.perm_vertices, flip_colinear_snd_trd.mt $ flip_colinear_fst_snd.mt tr_nd.2⟩

def flip_vertices : (Triangle_nd P) := ⟨tr_nd.1.flip_vertices, flip_colinear_snd_trd.mt tr_nd.2⟩

end Triangle_nd

theorem eq_self_of_flip_vertices_twice : tr.flip_vertices.flip_vertices = tr := by sorry

-- Not sure this is the best theorem to p
theorem eq_flip_of_perm_twice_of_perm_flip_vertices : tr.flip_vertices.perm_vertices.perm_vertices = tr.perm_vertices.flip_vertices := by sorry

-- compatibility of permutation/flip of vertices with orientation of the triangle

theorem same_orient_of_perm_vertices : tr_nd.is_cclock = (tr_nd.perm_vertices.is_cclock) := by sorry

theorem reverse_orient_of_flip_vertices : tr_nd.is_cclock = ¬ tr_nd.flip_vertices.is_cclock := by sorry

-- compatiblility of permutation/flip of vertices with inside triangle

theorem is_inside_of_is_inside_perm_vertices (tr : Triangle P) (p : P) (inside : p IsInsideTriangle tr) : p IsInsideTriangle tr.perm_vertices := by sorry

theorem is_inside_of_is_inside_flip_vertices (tr : Triangle P) (p : P) (inside : p IsInsideTriangle tr) : p IsInsideTriangle tr.flip_vertices := by sorry

end EuclidGeom