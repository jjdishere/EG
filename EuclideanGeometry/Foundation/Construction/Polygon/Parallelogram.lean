import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral

/-!

-/
noncomputable section
namespace EuclidGeom

def Quadrilateral_cvx.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P) : Prop := ( qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) ∧ (qdr_cvx.edge_nd₁₄ ∥ (qdr_cvx.edge_nd₂₃))

def Quadrilateral.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases qdr IsConvex
  · exact (Quadrilateral_cvx.mk_is_convex h).IsParallelogram
  · exact False

postfix : 50 "IsPRG" => Quadrilateral.IsParallelogram

variable {P : Type _} [EuclideanPlane P]

section criteria
variable {A B C D : P} (h : (QDR A B C D) IsConvex)

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, AB ∥ CD and AD ∥ BC, Quadrilateral ABCD is a Parallelogram. -/
theorem is_prg_of_para_para (h₁ : (SEG_nd A B (Quadrilateral_cvx.nd₁₂ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd C D (Quadrilateral_cvx.nd₃₄ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (SEG_nd A D (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd B C (Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex h)))) : QDR A B C D IsPRG := by
  unfold Quadrilateral.IsParallelogram
  rw [dif_pos h]
  unfold Quadrilateral_cvx.IsParallelogram
  constructor
  exact h₁
  exact h₂

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AB = CD and AD = BC, Quadrilateral ABCD is a Parallelogram. -/
theorem is_prg_of_eq_length_eq_length (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG A D).length = (SEG B C).length) : QDR A B C D IsPRG := sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AB ∥ CD and AB = CD, Quadrilateral ABCD is a Parallelogram. -/
theorem is_prg_of_para_eq_length (h₁ : (SEG_nd A B (Quadrilateral_cvx.nd₁₂ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd C D (Quadrilateral_cvx.nd₃₄ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (SEG A B).length = (SEG C D).length) : QDR A B C D IsPRG := sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AD ∥ BC and AD = BC, Quadrilateral ABCD is a Parallelogram. -/
theorem is_prg_of_para_eq_length' (h₁ : (SEG_nd A D (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd B C (Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (SEG A D).length = (SEG B C).length) : QDR A B C D IsPRG := sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and ∠DAB = ∠BCD and ∠ABC = ∠CDA, Quadrilateral ABCD is a Parallelogram. -/
theorem is_prg_of_eq_angle_value_eq_angle_value (h₁ : (ANG D A B sorry sorry) = (ANG B C D sorry sorry)) (h₂ : (ANG A B C sorry sorry) = (ANG C D A sorry sorry)) : QDR A B C D IsPRG := sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and the midpoint of the diagonal AC and BD is the same, Quadrilateral ABCD is a Parallelogram. -/
theorem is_prg_of_diag_inx_eq_mid_eq_mid (h : (SEG A C).midpoint = (SEG B D).midpoint) : QDR A B C D IsPRG := sorry

end criteria

section property
variable {A B C D : P}

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, Quadrilateral ABCD IsConvex. -/
theorem is_convex_of_is_prg (h : QDR A B C D IsPRG) : (QDR A B C D) IsConvex := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases j: QDR A B C D IsConvex
  · simp only [j]
  · simp only [j, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, C ≠ A. -/
theorem nd₁₃_of_is_prg (h : QDR A B C D IsPRG) : C ≠ A := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg h
  unfold Quadrilateral.IsConvex at s
  by_cases j: C ≠ A
  · simp only [ne_eq, j, not_false_eq_true]
  simp at j
  · simp only [ne_eq, j, false_and, dite_false] at s

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, D ≠ B. -/
theorem nd₂₄_of_is_prg (h : QDR A B C D IsPRG) : D ≠ B := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg h
  unfold Quadrilateral.IsConvex at s
  by_cases j: D ≠ B
  · simp only [ne_eq, j, not_false_eq_true]
  simp at j
  · simp only [ne_eq, j, and_false, dite_false] at s

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, B ≠ A. -/
theorem nd₁₂_of_is_prg (h : QDR A B C D IsPRG) : B ≠ A := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₂

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, C ≠ B. -/
theorem nd₂₃_of_is_prg (h : QDR A B C D IsPRG) : C ≠ B := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₂₃

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, D ≠ C. -/
theorem nd₃₄_of_is_prg (h : QDR A B C D IsPRG) : D ≠ C := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₃₄

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, D ≠ A. -/
theorem nd₁₄_of_is_prg (h : QDR A B C D IsPRG) : D ≠ A := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₄

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the opposite sides are parallel namely AB ∥ CD. -/
theorem para_of_is_prg (h : QDR A B C D IsPRG) : (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ (SEG_nd C D (nd₃₄_of_is_prg h)) := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  unfold Quadrilateral_cvx.IsParallelogram at h
  rcases h with ⟨a,b⟩
  exact a
  simp only [k, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the opposite sides are parallel namely AD ∥ BC. -/
theorem para_of_is_prg' (h : QDR A B C D IsPRG) : (SEG_nd A D (nd₁₄_of_is_prg h)) ∥ SEG_nd B C (nd₂₃_of_is_prg h) := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  unfold Quadrilateral_cvx.IsParallelogram at h
  rcases h with ⟨a,b⟩
  exact b
  simp only [k, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the opposite sides are equal namely (SEG A B).length = (SEG C D).length. -/
theorem eq_length_of_is_prg  (h : QDR A B C D IsPRG) : (SEG A B).length = (SEG C D).length := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  sorry
  simp only [k, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the opposite sides are equal namely (SEG A D).length = (SEG B C).length. -/
theorem eq_length_of_is_prg'  (h : QDR A B C D IsPRG) : (SEG A D).length = (SEG B C).length := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  sorry
  simp only [k, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the opposite angles are equal namely ANG A B C = ANG C D A. -/
theorem eq_angle_value_of_is_prg (h : QDR A B C D IsPRG) : ANG A B C ((nd₁₂_of_is_prg h).symm) (nd₂₃_of_is_prg h) = ANG C D A ((nd₃₄_of_is_prg h).symm) ((nd₁₄_of_is_prg h).symm) := by
  have h₁ : (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ SEG_nd C D (nd₃₄_of_is_prg h) := para_of_is_prg h
  have h₂ : (SEG_nd A D (nd₁₄_of_is_prg h)) ∥ SEG_nd B C (nd₂₃_of_is_prg h) := para_of_is_prg' h
  unfold Quadrilateral.IsParallelogram at h
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the opposite angles are equal namely ANG D A B = ANG B C D. -/
theorem eq_angle_value_of_is_prg' (h : QDR A B C D IsPRG) : ANG D A B (nd₁₄_of_is_prg h) (nd₁₂_of_is_prg h) = ANG B C D ((nd₂₃_of_is_prg h).symm) (nd₃₄_of_is_prg h) := by
  have h₁ : (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ SEG_nd C D (nd₃₄_of_is_prg h) := para_of_is_prg h
  have h₂ : (SEG_nd A D (nd₁₄_of_is_prg h)) ∥ SEG_nd B C (nd₂₃_of_is_prg h) := para_of_is_prg' h
  unfold Quadrilateral.IsParallelogram at h
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx A B C D = (SEG A C).midpoint. -/
theorem eq_midpt_of_diag_inx_of_is_prg {E : P} (h : QDR A B C D IsPRG) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg h)) = (SEG A C).midpoint :=
  have h : (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ SEG_nd C D (nd₃₄_of_is_prg h) := para_of_is_prg h
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx A B C D = (SEG B D).midpoint. -/
theorem eq_midpt_of_diag_inx_of_is_prg' {E : P} (h : QDR A B C D IsPRG) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg h)) = (SEG B D).midpoint :=
  have h : (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ SEG_nd C D (nd₃₄_of_is_prg h) := para_of_is_prg h
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG, the sum of the squares of each side equals to the sum of the squares of the diagonals namely 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2. -/
theorem parallelogram_law (h : QDR A B C D IsPRG) : 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2 :=
  sorry

end property

end EuclidGeom
