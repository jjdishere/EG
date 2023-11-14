import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral
import EuclideanGeometry.Foundation.Construction.Polygon.Trapezoid

/-!

-/
noncomputable section
namespace EuclidGeom

-- `Add class parallelogram and state every theorem in structure`
class Parallelogram (P : Type _) [EuclideanPlane P] extends Quadrilateral_cvx P where
--  `to be added`

def Quadrilateral_cvx.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P) : Prop := ( qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) ∧ (qdr_cvx.edge_nd₁₄ ∥ (qdr_cvx.edge_nd₂₃))

def Quadrilateral.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases qdr IsConvex
  · exact (Quadrilateral_cvx.mk_is_convex h).IsParallelogram
  · exact False

postfix : 50 "IsPRG" => Quadrilateral.IsParallelogram

variable {P : Type _} [EuclideanPlane P]

section criteria
variable {A B C D : P} (h : (QDR A B C D) IsConvex)
variable {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P)

/-- Given Quadrilateral_cvx qdr_cvx, qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄ and qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃, then qdr_cvx is a Parallelogram. -/
theorem is_prg_of_para_para (h₁ : qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) (h₂ : qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃) : qdr_cvx.IsParallelogram := by
  unfold Quadrilateral_cvx.IsParallelogram
  constructor
  exact h₁
  exact h₂

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, AB ∥ CD and AD ∥ BC, Quadrilateral ABCD is a Parallelogram. -/
theorem is_prg_of_para_para_variant (h₁ : (SEG_nd A B (Quadrilateral_cvx.nd₁₂ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd C D (Quadrilateral_cvx.nd₃₄ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (SEG_nd A D (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd B C (Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex h)))) : QDR A B C D IsPRG := by
  unfold Quadrilateral.IsParallelogram
  rw [dif_pos h]
  unfold Quadrilateral_cvx.IsParallelogram
  constructor
  exact h₁
  exact h₂

/-- Given Quadrilateral_cvx qdr_cvx, and (qdr_cvx.edge_nd₁₂).1.length = (qdr_cvx.edge_nd₃₄).1.length and qdr_cvx.edge_nd₁₄.1.length = qdr_cvx.edge_nd₂₃.1.length, qdr_cvx is a Parallelogram. -/
theorem is_prg_of_eq_length_eq_length (h₁ : (qdr_cvx.edge_nd₁₂).1.length = (qdr_cvx.edge_nd₃₄).1.length) (h₂ : qdr_cvx.edge_nd₁₄.1.length = qdr_cvx.edge_nd₂₃.1.length) : qdr_cvx.IsParallelogram := sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AB = CD and AD = BC, Quadrilateral ABCD is a Parallelogram. -/
theorem is_prg_of_eq_length_eq_length_variant (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG A D).length = (SEG B C).length) : QDR A B C D IsPRG := sorry

/-- Given Quadrilateral_cvx qdr_cvx, and qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄ and (qdr_cvx.edge_nd₁₂).1.length = (qdr_cvx.edge_nd₃₄).1.length, qdr_cvx is a Parallelogram. -/
theorem is_prg_of_para_eq_length (h₁ : qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) (h₂ : qdr_cvx.edge_nd₁₂.1.length = qdr_cvx.edge_nd₃₄.1.length) : qdr_cvx.IsParallelogram := sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AB ∥ CD and AB = CD, Quadrilateral ABCD is a Parallelogram. -/
theorem is_prg_of_para_eq_length_variant (h₁ : (SEG_nd A B (Quadrilateral_cvx.nd₁₂ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd C D (Quadrilateral_cvx.nd₃₄ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (SEG A B).length = (SEG C D).length) : QDR A B C D IsPRG := sorry

/-- Given Quadrilateral_cvx qdr_cvx, and qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃ and (qdr_cvx.edge_nd₁₄).1.length = (qdr_cvx.edge_nd₂₃).1.length, qdr_cvx is a Parallelogram. -/
theorem is_prg_of_para_eq_length' (h₁ : qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃) (h₂ : qdr_cvx.edge_nd₁₄.1.length = qdr_cvx.edge_nd₂₃.1.length) : qdr_cvx.IsParallelogram := sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AD ∥ BC and AD = BC, Quadrilateral ABCD is a Parallelogram. -/
theorem is_prg_of_para_eq_length'_variant (h₁ : (SEG_nd A D (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd B C (Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (SEG A D).length = (SEG B C).length) : QDR A B C D IsPRG := sorry

/-- Given Quadrilateral_cvx qdr_cvx, and angle₁ = angle₃ and angle₂ = angle₄, qdr_cvx is a Parallelogram. -/
theorem is_prg_of_eq_angle_value_eq_angle_value (h₁ : qdr_cvx.angle₁ = qdr_cvx.angle₃) (h₂ : qdr_cvx.angle₂ = qdr_cvx.angle₄) : qdr_cvx.IsParallelogram := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and ∠DAB = ∠BCD and ∠ABC = ∠CDA, Quadrilateral ABCD is a Parallelogram. -/
theorem is_prg_of_eq_angle_value_eq_angle_value_variant (h₁ : (ANG D A B (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex h)) (Quadrilateral_cvx.nd₁₂ (Quadrilateral_cvx.mk_is_convex h))) = (ANG B C D (Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex h)).symm (Quadrilateral_cvx.nd₃₄ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (ANG A B C (Quadrilateral_cvx.nd₁₂ (Quadrilateral_cvx.mk_is_convex h)).symm (Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex h))) = (ANG C D A (Quadrilateral_cvx.nd₃₄ (Quadrilateral_cvx.mk_is_convex h)).symm (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex h)).symm)) : QDR A B C D IsPRG := by
  sorry

/-- Given Quadrilateral_cvx qdr_cvx, and qdr_cvx.diag_nd₁₃.1.midpoint = qdr_cvx.diag_nd₂₄.1.midpoint, qdr_cvx is a Parallelogram. -/
theorem is_prg_of_diag_inx_eq_mid_eq_mid (h : qdr_cvx.diag_nd₁₃.1.midpoint = qdr_cvx.diag_nd₂₄.1.midpoint) : qdr_cvx.IsParallelogram := sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and the midpoint of the diagonal AC and BD is the same, Quadrilateral ABCD is a Parallelogram. -/
theorem is_prg_of_diag_inx_eq_mid_eq_mid_variant (h : (SEG A C).midpoint = (SEG B D).midpoint) : QDR A B C D IsPRG := sorry

end criteria

section property
variable {A B C D : P}
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)

/-- Given Quadrilateral qdr IsPRG, Quadrilateral qdr IsConvex. -/
theorem is_convex_of_is_prg (h : qdr.IsParallelogram) : qdr.IsConvex := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases j: qdr.IsConvex
  · simp only [j]
  · simp only [j, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, Quadrilateral ABCD IsConvex. -/
theorem is_convex_of_is_prg_variant (h : QDR A B C D IsPRG) : (QDR A B C D) IsConvex := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases j: QDR A B C D IsConvex
  · simp only [j]
  · simp only [j, dite_false] at h

/-- Given Quadrilateral qdr IsPRG, qdr.point₃ ≠ qdr.point₁. -/
theorem nd₁₃_of_is_prg (h : qdr.IsParallelogram) : qdr.point₃ ≠ qdr.point₁ := by
  have s : qdr.IsConvex:= is_convex_of_is_prg qdr h
  unfold Quadrilateral.IsConvex at s
  by_cases j: qdr.point₃ ≠ qdr.point₁
  · simp only [ne_eq, j, not_false_eq_true]
  simp at j
  · simp only [ne_eq, j, false_and, dite_false] at s

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, C ≠ A. -/
theorem nd₁₃_of_is_prg_variant (h : QDR A B C D IsPRG) : C ≠ A := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_variant h
  unfold Quadrilateral.IsConvex at s
  by_cases j: C ≠ A
  · simp only [ne_eq, j, not_false_eq_true]
  simp at j
  · simp only [ne_eq, j, false_and, dite_false] at s

/-- Given Quadrilateral qdr IsPRG, qdr.point₄ ≠ qdr.point₂. -/
theorem nd₂₄_of_is_prg (h : qdr.IsParallelogram) : qdr.point₄ ≠ qdr.point₂ := by
  have s : qdr.IsConvex:= is_convex_of_is_prg qdr h
  unfold Quadrilateral.IsConvex at s
  by_cases j: qdr.point₄ ≠ qdr.point₂
  · simp only [ne_eq, j, not_false_eq_true]
  simp at j
  · simp only [ne_eq, j, and_false, dite_false] at s

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, D ≠ B. -/
theorem nd₂₄_of_is_prg_variant (h : QDR A B C D IsPRG) : D ≠ B := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_variant h
  unfold Quadrilateral.IsConvex at s
  by_cases j: D ≠ B
  · simp only [ne_eq, j, not_false_eq_true]
  simp at j
  · simp only [ne_eq, j, and_false, dite_false] at s

/-- Given Quadrilateral qdr IsPRG, qdr.point₂ ≠ qdr.point₁. -/
theorem nd₁₂_of_is_prg (h : qdr.IsParallelogram) : qdr.point₂ ≠ qdr.point₁ := by
  have s : qdr.IsConvex:= is_convex_of_is_prg qdr h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₂

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, B ≠ A. -/
theorem nd₁₂_of_is_prg_variant (h : QDR A B C D IsPRG) : B ≠ A := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_variant h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₂

/-- Given Quadrilateral qdr IsPRG, qdr.point₃ ≠ qdr.point₂. -/
theorem nd₂₃_of_is_prg (h : qdr.IsParallelogram) : qdr.point₃ ≠ qdr.point₂ := by
  have s : qdr.IsConvex:= is_convex_of_is_prg qdr h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₂₃

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, C ≠ B. -/
theorem nd₂₃_of_is_prg_variant (h : QDR A B C D IsPRG) : C ≠ B := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_variant h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₂₃

/-- Given Quadrilateral qdr IsPRG, qdr.point₄ ≠ qdr.point₃. -/
theorem nd₃₄_of_is_prg (h : qdr.IsParallelogram) : qdr.point₄ ≠ qdr.point₃ := by
  have s : qdr.IsConvex:= is_convex_of_is_prg qdr h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₃₄

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, D ≠ C. -/
theorem nd₃₄_of_is_prg_variant (h : QDR A B C D IsPRG) : D ≠ C := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_variant h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₃₄

/-- Given Quadrilateral qdr IsPRG, qdr.point₄ ≠ qdr.point₁. -/
theorem nd₁₄_of_is_prg (h : qdr.IsParallelogram) : qdr.point₄ ≠ qdr.point₁ := by
  have s : qdr.IsConvex:= is_convex_of_is_prg qdr h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₄

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, D ≠ A. -/
theorem nd₁₄_of_is_prg_variant (h : QDR A B C D IsPRG) : D ≠ A := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_variant h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₄

/-- Given Quadrilateral qdr IsPRG, the opposite sides are parallel namely (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_abstract qdr h)) ∥ (SEG_nd qdr.point₃ qdr.point₄ (nd₃₄_of_is_prg_abstract qdr h)). -/
theorem para_of_is_prg (h : qdr.IsParallelogram) : (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg qdr h)) ∥ (SEG_nd qdr.point₃ qdr.point₄ (nd₃₄_of_is_prg qdr h)):= by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: qdr.IsConvex
  simp only [k, dite_true] at h
  unfold Quadrilateral_cvx.IsParallelogram at h
  rcases h with ⟨a,b⟩
  exact a
  simp only [k, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the opposite sides are parallel namely AB ∥ CD. -/
theorem para_of_is_prg_variant (h : QDR A B C D IsPRG) : (SEG_nd A B (nd₁₂_of_is_prg_variant h)) ∥ (SEG_nd C D (nd₃₄_of_is_prg_variant h)) := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  unfold Quadrilateral_cvx.IsParallelogram at h
  rcases h with ⟨a,b⟩
  exact a
  simp only [k, dite_false] at h

/-- Given Quadrilateral qdr IsPRG, the opposite sides are parallel namely (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_abstract qdr h)) ∥ (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_abstract qdr h)). -/
theorem para_of_is_prg' (h : qdr.IsParallelogram) : (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg qdr h)) ∥ (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg qdr h)):= by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: qdr.IsConvex
  simp only [k, dite_true] at h
  unfold Quadrilateral_cvx.IsParallelogram at h
  rcases h with ⟨a,b⟩
  exact b
  simp only [k, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the opposite sides are parallel namely AD ∥ BC. -/
theorem para_of_is_prg'_variant (h : QDR A B C D IsPRG) : (SEG_nd A D (nd₁₄_of_is_prg_variant h)) ∥ SEG_nd B C (nd₂₃_of_is_prg_variant h) := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  unfold Quadrilateral_cvx.IsParallelogram at h
  rcases h with ⟨a,b⟩
  exact b
  simp only [k, dite_false] at h

/-- Given Quadrilateral qdr IsPRG, the opposite sides are equal namely (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_abstract qdr h)).1.length = (SEG_nd qdr.point₃ qdr.point₄ (nd₁₂_of_is_prg_abstract qdr h)).1.length. -/
theorem eq_length_of_is_prg  (h : qdr.IsParallelogram) : (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg qdr h)).1.length = (SEG_nd qdr.point₃ qdr.point₄ (nd₃₄_of_is_prg qdr h)).1.length := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: qdr.IsConvex
  simp only [k, dite_true] at h
  sorry
  simp only [k, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the opposite sides are equal namely (SEG A B).length = (SEG C D).length. -/
theorem eq_length_of_is_prg_variant  (h : QDR A B C D IsPRG) : (SEG A B).length = (SEG C D).length := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  sorry
  simp only [k, dite_false] at h

/-- Given Quadrilateral qdr IsPRG, the opposite sides are equal namely (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_abstract qdr h)).1.length = (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_abstract qdr h)).1.length. -/
theorem eq_length_of_is_prg'  (h : qdr.IsParallelogram) : (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg qdr h)).1.length = (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg qdr h)).1.length := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: qdr.IsConvex
  simp only [k, dite_true] at h
  sorry
  simp only [k, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the opposite sides are equal namely (SEG A D).length = (SEG B C).length. -/
theorem eq_length_of_is_prg'_variant  (h : QDR A B C D IsPRG) : (SEG A D).length = (SEG B C).length := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  sorry
  simp only [k, dite_false] at h

/-- Given Quadrilateral qdr IsPRG, the opposite angles are equal namely ANG qdr.point₁ qdr.point₂ qdr.point₃ = ANG qdr.point₃ qdr.point₄ qdr.point₁. -/
theorem eq_angle_value_of_is_prg (h : qdr.IsParallelogram) : ANG qdr.point₁ qdr.point₂ qdr.point₃ ((nd₁₂_of_is_prg qdr h).symm) (nd₂₃_of_is_prg qdr h) = ANG qdr.point₃ qdr.point₄ qdr.point₁ ((nd₃₄_of_is_prg qdr h).symm) ((nd₁₄_of_is_prg qdr h).symm) := by
  unfold Quadrilateral.IsParallelogram at h
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the opposite angles are equal namely ANG A B C = ANG C D A. -/
theorem eq_angle_value_of_is_prg_variant (h : QDR A B C D IsPRG) : ANG A B C ((nd₁₂_of_is_prg_variant h).symm) (nd₂₃_of_is_prg_variant h) = ANG C D A ((nd₃₄_of_is_prg_variant h).symm) ((nd₁₄_of_is_prg_variant h).symm) := by
  have h₁ : (SEG_nd A B (nd₁₂_of_is_prg_variant h)) ∥ SEG_nd C D (nd₃₄_of_is_prg_variant h) := para_of_is_prg_variant h
  have h₂ : (SEG_nd A D (nd₁₄_of_is_prg_variant h)) ∥ SEG_nd B C (nd₂₃_of_is_prg_variant h) := para_of_is_prg'_variant h
  unfold Quadrilateral.IsParallelogram at h
  sorry

/-- Given Quadrilateral qdr IsPRG, the opposite angles are equal namely ANG qdr.point₄ qdr.point₁ qdr.point₂ = ANG qdr.point₂ qdr.point₃ qdr.point₄. -/
theorem eq_angle_value_of_is_prg'_abstract (h : qdr.IsParallelogram) : ANG qdr.point₄ qdr.point₁ qdr.point₂ ((nd₁₄_of_is_prg qdr h)) ((nd₁₂_of_is_prg qdr h)) = ANG qdr.point₂ qdr.point₃ qdr.point₄ ((nd₂₃_of_is_prg qdr h).symm) (nd₃₄_of_is_prg qdr h):= by
  unfold Quadrilateral.IsParallelogram at h
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the opposite angles are equal namely ANG D A B = ANG B C D. -/
theorem eq_angle_value_of_is_prg' (h : QDR A B C D IsPRG) : ANG D A B (nd₁₄_of_is_prg_variant h) (nd₁₂_of_is_prg_variant h) = ANG B C D ((nd₂₃_of_is_prg_variant h).symm) (nd₃₄_of_is_prg_variant h) := by
  have h₁ : (SEG_nd A B (nd₁₂_of_is_prg_variant h)) ∥ SEG_nd C D (nd₃₄_of_is_prg_variant h) := para_of_is_prg_variant h
  have h₂ : (SEG_nd A D (nd₁₄_of_is_prg_variant h)) ∥ SEG_nd B C (nd₂₃_of_is_prg_variant h) := para_of_is_prg'_variant h
  unfold Quadrilateral.IsParallelogram at h
  sorry

/-- Given Quadrilateral qdr IsPRG, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ = (SEG qdr.point₁ qdr.point₃).midpoint. -/
theorem eq_midpt_of_diag_inx_of_is_prg_abstract {E : P} (h : qdr.IsParallelogram) : Quadrilateral_cvx.diag_inx (QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ (is_convex_of_is_prg qdr h)) = (SEG qdr.point₁ qdr.point₃).midpoint :=
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx A B C D = (SEG A C).midpoint. -/
theorem eq_midpt_of_diag_inx_of_is_prg {E : P} (h : QDR A B C D IsPRG) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg_variant h)) = (SEG A C).midpoint :=
  have h : (SEG_nd A B (nd₁₂_of_is_prg_variant h)) ∥ SEG_nd C D (nd₃₄_of_is_prg_variant h) := para_of_is_prg_variant h
  sorry

/-- Given Quadrilateral qdr IsPRG, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ = (SEG qdr.point₂ qdr.point₄).midpoint. -/
theorem eq_midpt_of_diag_inx_of_is_prg'_abstract {E : P} (h : qdr.IsParallelogram) : Quadrilateral_cvx.diag_inx (QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ (is_convex_of_is_prg qdr h)) = (SEG qdr.point₂ qdr.point₄).midpoint :=
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx A B C D = (SEG B D).midpoint. -/
theorem eq_midpt_of_diag_inx_of_is_prg' {E : P} (h : QDR A B C D IsPRG) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg_variant h)) = (SEG B D).midpoint :=
  have h : (SEG_nd A B (nd₁₂_of_is_prg_variant h)) ∥ SEG_nd C D (nd₃₄_of_is_prg_variant h) := para_of_is_prg_variant h
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the sum of the squares of each side equals to the sum of the squares of the diagonals namely 2 * (SEG qdr.point₁ qdr.point₂).length ^ 2 + 2 * (SEG qdr.point₂ qdr.point₃).length ^ 2 = (SEG qdr.point₁ qdr.point₃).length ^ 2 + (SEG qdr.point₂ qdr.point₄).length ^ 2. -/
theorem parallelogram_law_abstract (h : qdr.IsParallelogram) : 2 * (SEG qdr.point₁ qdr.point₂).length ^ 2 + 2 * (SEG qdr.point₂ qdr.point₃).length ^ 2 = (SEG qdr.point₁ qdr.point₃).length ^ 2 + (SEG qdr.point₂ qdr.point₄).length ^ 2 :=
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the sum of the squares of each side equals to the sum of the squares of the diagonals namely 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2. -/
theorem parallelogram_law (h : QDR A B C D IsPRG) : 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2 :=
  sorry

end property

end EuclidGeom
