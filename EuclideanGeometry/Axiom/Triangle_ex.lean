import EuclideanGeometry.Axiom.Triangle

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] (tri : LTriangle P)

namespace LTriangle

def perm_vertices : (LTriangle P) where
  point1 := tri.point2
  point2 := tri.point3
  point3 := tri.point1
  nontriv1 := sorry
  nontriv2 := sorry
  nontriv3 := sorry
  left := sorry

def revperm_vertices : (LTriangle P) where
  point1 := tri.point3
  point2 := tri.point1
  point3 := tri.point2
  nontriv1 := sorry
  nontriv2 := sorry
  nontriv3 := sorry
  left := sorry

theorem perm_of_revperm_vertices : tri.perm_vertices.revperm_vertices = tri := by sorry

theorem revperm_of_revperm_eq_perm_vertices : tri.revperm_vertices.revperm_vertices = tri.perm_vertices := by sorry

-- More theorems along this line : tri.rev.perm = tri  and tri.perm.perm = tri.revperm




end LTriangle


end EuclidGeom