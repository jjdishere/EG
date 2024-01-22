import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular

/-!

-/
noncomputable section
namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

def TriangleND.Height1 (tr_nd : TriangleND P) : SegND P := sorry

-- this takes care of corner cases such as right triangles, where AH ⟂ BC runs into trouble since A = H
def IsOrthocenter (tr_nd : TriangleND P) (H : P) : Prop := inner (VEC tr_nd.point₁ H) (VEC tr_nd.point₂ tr_nd.point₃) = (0 : ℝ) ∧ inner (VEC tr_nd.point₂ H) (VEC tr_nd.point₃ tr_nd.point₁) = (0 : ℝ) ∧ inner (VEC tr_nd.point₃ H) (VEC tr_nd.point₁ tr_nd.point₂) = (0 : ℝ)

theorem orthocenter_exists (tr : Triangle P) (H : P) (h₁ : inner (VEC tr.point₁ H) (VEC tr.point₂ tr.point₃) = (0 : ℝ)) (h₂ : inner (VEC tr.point₂ H) (VEC tr.point₃ tr.point₁) = (0 : ℝ)) : inner (VEC tr.point₃ H) (VEC tr.point₁ tr.point₂) = (0 : ℝ) := by
  set A := tr.point₁
  set B := tr.point₂
  set C := tr.point₃
  rw [← vec_sub_vec C, inner_sub_left, sub_eq_zero] at h₁ h₂
  rw [← vec_sub_vec C A B, inner_sub_right, sub_eq_zero, ← neg_vec B C, inner_neg_right, h₁, h₂, real_inner_comm, ← inner_neg_left, neg_vec]

def TriangleND.Orthocenter (tr_nd : TriangleND P) : P := sorry

theorem TriangleND.orthocenter_is_orthocenter (tr_nd : TriangleND P) : IsOrthocenter tr_nd tr_nd.Orthocenter := sorry

end EuclidGeom
