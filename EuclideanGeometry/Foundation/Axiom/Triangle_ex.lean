import EuclideanGeometry.Foundation.Axiom.Triangle

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] (tri : Triangle P)

namespace Triangle

def perm_vertices : (Triangle P) where
  point₁ := tri.point₂
  point₂ := tri.point₃
  point₃ := tri.point₁

def revperm_vertices : (Triangle P) where
  point₁ := tri.point₃
  point₂ := tri.point₁
  point₃ := tri.point₂

theorem perm_of_revperm_vertices : tri.perm_vertices.revperm_vertices = tri := by sorry

theorem revperm_of_revperm_eq_perm_vertices : tri.revperm_vertices.revperm_vertices = tri.perm_vertices := by sorry

-- More theorems along this line : tri.rev.perm = tri  and tri.perm.perm = tri.revperm




end Triangle


end EuclidGeom