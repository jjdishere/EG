import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_ex

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

structure Triangle_nd.IsAcute (tri_nd : Triangle_nd P) : Prop where
  angle₁ : - π / 2 < tri_nd.angle₁.value ∧ tri_nd.angle₁.value < π / 2
  angle₂ : - π / 2 < tri_nd.angle₂.value ∧ tri_nd.angle₂.value < π / 2
  angle₃ : - π / 2 < tri_nd.angle₃.value ∧ tri_nd.angle₃.value < π / 2
variable {tr_nd₁ tr_nd₂ : Triangle_nd P}

theorem angle_eq_of_cosine_eq_of_cclock (cclock : tr_nd₁.is_cclock ↔ tr_nd₂.is_cclock) (cosine : Real.cos tr_nd₁.angle₁.value = Real.cos tr_nd₂.angle₁.value) : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value := by
  have g : (0 < tr_nd₁.angle₁.value ∧ 0 < tr_nd₂.angle₁.value) ∨ (tr_nd₁.angle₁.value < 0 ∧ tr_nd₂.angle₁.value < 0) := by
      exact (Triangle.pos_pos_or_neg_neg_of_iff_cclock).mp cclock
  rcases g with x | y
  · have x₁ : (0 < tr_nd₁.angle₁.value) ∧ (tr_nd₁.angle₁.value < π) := sorry
    have x₂ : (0 < tr_nd₂.angle₁.value) ∧ (tr_nd₂.angle₁.value < π) := sorry
    exact (Dir.pos_angle_eq_angle_iff_cos_eq_cos tr_nd₁.angle₁.value tr_nd₂.angle₁.value x₁ x₂).mp cosine
  · have y₁ : (-π < tr_nd₁.angle₁.value) ∧ (tr_nd₁.angle₁.value < 0) := sorry
    have y₂ : (-π < tr_nd₂.angle₁.value) ∧ (tr_nd₂.angle₁.value < 0) := sorry
    exact (Dir.neg_angle_eq_angle_iff_cos_eq_cos tr_nd₁.angle₁.value tr_nd₂.angle₁.value y₁ y₂).mp cosine

namespace Triangle_nd

theorem edge_eq_edge_of_perm_vertices_two_times (tr_nd : Triangle_nd P) : tr_nd.1.edge₁.length = tr_nd.perm_vertices.perm_vertices.1.edge₃.length ∧ tr_nd.1.edge₂.length = tr_nd.perm_vertices.perm_vertices.1.edge₁.length ∧ tr_nd.1.edge₃.length = tr_nd.perm_vertices.perm_vertices.1.edge₂.length := sorry

theorem angle_eq_angle_of_perm_vertices_two_times (tr_nd : Triangle_nd P) : tr_nd.angle₁.value = tr_nd.perm_vertices.perm_vertices.angle₃.value ∧ tr_nd.angle₂.value = tr_nd.perm_vertices.perm_vertices.angle₁.value ∧ tr_nd.angle₃.value = tr_nd.perm_vertices.perm_vertices.angle₂.value := by sorry

end Triangle_nd

end EuclidGeom
