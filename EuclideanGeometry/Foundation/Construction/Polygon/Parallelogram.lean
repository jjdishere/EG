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

theorem is_prg_of_para_para (h₁ : (SEG_nd A B (Quadrilateral_cvx.nd₁₂ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd C D (Quadrilateral_cvx.nd₃₄ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (SEG_nd A D (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd B C (Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex h)))) : QDR A B C D IsPRG := by
  unfold Quadrilateral.IsParallelogram
  rw [dif_pos h]
  unfold Quadrilateral_cvx.IsParallelogram
  constructor
  exact h₁
  exact h₂

theorem is_prg_of_eq_length_eq_length (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG B C).length = (SEG A D).length) : QDR A B C D IsPRG := sorry

-- a pair of edge both eq_length and parallel
theorem is_prg_of_para_eq_length (h₁ : (SEG_nd A B (Quadrilateral_cvx.nd₁₂ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd C D (Quadrilateral_cvx.nd₃₄ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (SEG A B).length = (SEG C D).length) : QDR A B C D IsPRG := sorry

theorem is_prg_of_para_eq_length' (h₁ : (SEG_nd A D (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd B C (Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (SEG A D).length = (SEG B C).length) : QDR A B C D IsPRG := sorry

theorem is_prg_of_eq_angle_value_eq_angle_value (h₁ : (ANG D A B sorry sorry) = (ANG B C D sorry sorry)) (h₂ : (ANG A B C sorry sorry) = (ANG C D A sorry sorry)) : QDR A B C D IsPRG := sorry

theorem is_prg_of_diag_inx_eq_mid_eq_mid (h : (SEG A C).midpoint = (SEG B D).midpoint) : QDR A B C D IsPRG := sorry

/-
0. is_prg_of_para_para
1. is_prg_of_eq_length_eq_length
2. is_prg_of_para_eq_length -- a pair of edge both eq_length and parallel
3. is_prg_of_eq_angle_value_eq_angle_value
4. is_prg_of_diag_inx_eq_mid_eq_mid -- diag intersection is the midpoint of both diagonal
-/
end criteria

section property
variable {A B C D : P}

theorem is_convex_of_is_prg (h : QDR A B C D IsPRG) : (QDR A B C D) IsConvex := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases j: QDR A B C D IsConvex
  · simp only [j]
  · simp only [j, dite_false] at h

theorem nd₁₃_of_is_prg (h : QDR A B C D IsPRG) : C ≠ A := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg h
  unfold Quadrilateral.IsConvex at s
  by_cases j: C ≠ A
  · simp only [ne_eq, j, not_false_eq_true]
  simp at j
  · simp only [ne_eq, j, false_and, dite_false] at s

theorem nd₂₄_of_is_prg (h : QDR A B C D IsPRG) : D ≠ B := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg h
  unfold Quadrilateral.IsConvex at s
  by_cases j: D ≠ B
  · simp only [ne_eq, j, not_false_eq_true]
  simp at j
  · simp only [ne_eq, j, and_false, dite_false] at s

theorem nd₁₂_of_is_prg (h : QDR A B C D IsPRG) : B ≠ A := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₂

theorem nd₂₃_of_is_prg (h : QDR A B C D IsPRG) : C ≠ B := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₂₃

theorem nd₃₄_of_is_prg (h : QDR A B C D IsPRG) : D ≠ C := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₃₄

theorem nd₁₄_of_is_prg (h : QDR A B C D IsPRG) : D ≠ A := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₄

theorem para_of_is_prg (h : QDR A B C D IsPRG) : (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ (SEG_nd C D (nd₃₄_of_is_prg h)) := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  unfold Quadrilateral_cvx.IsParallelogram at h
  rcases h with ⟨a,b⟩
  exact a
  simp only [k, dite_false] at h

theorem para_of_is_prg' (h : QDR A B C D IsPRG) : (SEG_nd A D (nd₁₄_of_is_prg h)) ∥ SEG_nd B C (nd₂₃_of_is_prg h) := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  unfold Quadrilateral_cvx.IsParallelogram at h
  rcases h with ⟨a,b⟩
  exact b
  simp only [k, dite_false] at h

theorem eq_length_of_is_prg  (h : QDR A B C D IsPRG) : (SEG A B).length = (SEG C D).length := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  sorry
  simp only [k, dite_false] at h

theorem eq_length_of_is_prg'  (h : QDR A B C D IsPRG) : (SEG A D).length = (SEG B C).length := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  sorry
  simp only [k, dite_false] at h

theorem eq_angle_value_of_is_prg (h : QDR A B C D IsPRG) : ANG A B C ((nd₁₂_of_is_prg h).symm) (nd₂₃_of_is_prg h) = ANG C D A ((nd₃₄_of_is_prg h).symm) ((nd₁₄_of_is_prg h).symm) := by
  have h₁ : (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ SEG_nd C D (nd₃₄_of_is_prg h) := para_of_is_prg h
  have h₂ : (SEG_nd A D (nd₁₄_of_is_prg h)) ∥ SEG_nd B C (nd₂₃_of_is_prg h) := para_of_is_prg' h
  unfold Quadrilateral.IsParallelogram at h
  sorry

theorem eq_angle_value_of_is_prg' (h : QDR A B C D IsPRG) : ANG D A B (nd₁₄_of_is_prg h) (nd₁₂_of_is_prg h) = ANG B C D ((nd₂₃_of_is_prg h).symm) (nd₃₄_of_is_prg h) := by
  have h₁ : (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ SEG_nd C D (nd₃₄_of_is_prg h) := para_of_is_prg h
  have h₂ : (SEG_nd A D (nd₁₄_of_is_prg h)) ∥ SEG_nd B C (nd₂₃_of_is_prg h) := para_of_is_prg' h
  unfold Quadrilateral.IsParallelogram at h
  sorry

theorem eq_midpt_of_diag_inx_of_is_prg {E : P} (h : QDR A B C D IsPRG) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg h)) = (SEG A C).midpoint :=
  have h : (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ SEG_nd C D (nd₃₄_of_is_prg h) := para_of_is_prg h
  sorry

theorem eq_midpt_of_diag_inx_of_is_prg' {E : P} (h : QDR A B C D IsPRG) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg h)) = (SEG B D).midpoint :=
  have h : (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ SEG_nd C D (nd₃₄_of_is_prg h) := para_of_is_prg h
  sorry

theorem parallelogram_law (h : QDR A B C D IsPRG) : 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2 :=
  sorry

end property

end EuclidGeom
