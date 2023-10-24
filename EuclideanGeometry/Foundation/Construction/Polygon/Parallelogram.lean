<<<<<<< HEAD
import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral

/-!

-/
noncomputable section
namespace EuclidGeom

def Quadrilateral_cvx.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P) : Prop := (LinearObj.seg_nd qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) ∧ (LinearObj.seg_nd qdr_cvx.edge_nd₂₃ ∥ qdr_cvx.edge_nd₄₁)

def Quadrilateral.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases qdr IsConvex
  · exact (Quadrilateral_cvx.mk_is_convex h).IsParallelogram
  · exact False

postfix : 50 "IsPRG" => Quadrilateral.IsParallelogram

variable {P : Type _} [EuclideanPlane P]

section criteria
variable {A B C D : P} (h : (QDR A B C D) IsConvex)

theorem is_prg_of_para_para (h₁ : LinearObj.seg_nd (SEG_nd A B (Quadrilateral_cvx.nd₁₂ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd C D (Quadrilateral_cvx.nd₃₄ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : LinearObj.seg_nd (SEG_nd B C (Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd D A (Quadrilateral_cvx.nd₄₁ (Quadrilateral_cvx.mk_is_convex h)))) : QDR A B C D IsPRG := by
  rw [Quadrilateral.IsParallelogram]
  sorry

theorem is_prg_of_eq_length_eq_length (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG B C).length = (SEG D A).length) : QDR A B C D IsPRG := sorry

-- a pair of edge both eq_length and parallel
theorem is_prg_of_para_eq_length (h₁ : LinearObj.seg_nd (SEG_nd A B (Quadrilateral_cvx.nd₁₂ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd C D (Quadrilateral_cvx.nd₃₄ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (SEG A B).length = (SEG C D).length) : QDR A B C D IsPRG := sorry

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
  have s : (QDR A B C D) IsConvex:= by
    exact is_convex_of_is_prg h
  unfold Quadrilateral.IsConvex at s
  by_cases j: C ≠ A
  · simp only [ne_eq, j, not_false_eq_true]
  · simp only [ne_eq, j, false_and, dite_false] at s

theorem nd₂₄_of_is_prg (h : QDR A B C D IsPRG) : D ≠ B := by
  have s : (QDR A B C D) IsConvex:= by
    exact is_convex_of_is_prg h
  unfold Quadrilateral.IsConvex at s
  by_cases j: D ≠ B
  · simp only [ne_eq, j, not_false_eq_true]
  · simp only [ne_eq, j, and_false, dite_false] at s

theorem nd₁₂_of_is_prg (h : QDR A B C D IsPRG) : B ≠ A := by
  have s : (QDR A B C D) IsConvex:= by
    exact is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₂

theorem nd₂₃_of_is_prg (h : QDR A B C D IsPRG) : C ≠ B := by
  have s : (QDR A B C D) IsConvex:= by
    exact is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₂₃

theorem nd₃₄_of_is_prg (h : QDR A B C D IsPRG) : D ≠ C := by
  have s : (QDR A B C D) IsConvex:= by
    exact is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₃₄

theorem nd₄₁_of_is_prg (h : QDR A B C D IsPRG) : A ≠ D := by
  have s : (QDR A B C D) IsConvex:= by
    exact is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₄₁

theorem para_of_is_prg (h : QDR A B C D IsPRG) : LinearObj.seg_nd (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ SEG_nd D C ((nd₃₄_of_is_prg h).symm) := by
  unfold Quadrilateral.IsParallelogram at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  unfold Quadrilateral_cvx.IsParallelogram at h
  sorry
  sorry

theorem para_of_is_prg' (h : QDR A B C D IsPRG) : LinearObj.seg_nd (SEG_nd B C (nd₂₃_of_is_prg h)) ∥ SEG_nd D A (nd₄₁_of_is_prg h) := by
  unfold Quadrilateral.IsParallelogram at h

  sorry

theorem eq_length_of_is_prg  (h : QDR A B C D IsPRG) : (SEG B C).length = (SEG D A).length := by
  unfold Quadrilateral.IsParallelogram at h

  sorry

theorem eq_length_of_is_prg'  (h : QDR A B C D IsPRG) : (SEG A B).length = (SEG C D).length := by
  unfold Quadrilateral.IsParallelogram at h
  sorry

theorem eq_angle_value_of_is_prg (h : QDR A B C D IsPRG) : ANG A B C ((nd₁₂_of_is_prg h).symm) (nd₂₃_of_is_prg h) = ANG C D A ((nd₃₄_of_is_prg h).symm) (nd₄₁_of_is_prg h) := by
  have h₁ : LinearObj.seg_nd (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ SEG_nd D C ((nd₃₄_of_is_prg h).symm) := para_of_is_prg h
  have h₂ : LinearObj.seg_nd (SEG_nd B C (nd₂₃_of_is_prg h)) ∥ SEG_nd D A (nd₄₁_of_is_prg h) := para_of_is_prg' h
  unfold Quadrilateral.IsParallelogram at h

  sorry

theorem eq_angle_value_of_is_prg' (h : QDR A B C D IsPRG) : ANG D A B ((nd₄₁_of_is_prg h).symm) (nd₁₂_of_is_prg h) = ANG B C D ((nd₂₃_of_is_prg h).symm) (nd₃₄_of_is_prg h) := by
  have h₁ : LinearObj.seg_nd (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ SEG_nd D C ((nd₃₄_of_is_prg h).symm) := para_of_is_prg h
  have h₂ : LinearObj.seg_nd (SEG_nd B C (nd₂₃_of_is_prg h)) ∥ SEG_nd D A (nd₄₁_of_is_prg h) := para_of_is_prg' h
  unfold Quadrilateral.IsParallelogram at h

  sorry

theorem eq_midpt_of_diag_inx_of_is_prg {E : P} (h : QDR A B C D IsPRG) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg h)) = (SEG A C).midpoint :=
  have h : LinearObj.seg_nd (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ SEG_nd D C ((nd₃₄_of_is_prg h).symm) := para_of_is_prg h

  sorry

theorem eq_midpt_of_diag_inx_of_is_prg' {E : P} (h : QDR A B C D IsPRG) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg h)) = (SEG B D).midpoint :=
  have h : LinearObj.seg_nd (SEG_nd A B (nd₁₂_of_is_prg h)) ∥ SEG_nd D C ((nd₃₄_of_is_prg h).symm) := para_of_is_prg h

  sorry

--holidaymaker

theorem parallelogram_law (h : QDR A B C D IsPRG) : 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2 :=
  sorry

end property

end EuclidGeom
=======
import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral

/-!

-/
noncomputable section
namespace EuclidGeom

def Quadrilateral_cvx.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P) : Prop := (LinearObj.seg_nd qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) ∧ (LinearObj.seg_nd qdr_cvx.edge_nd₂₃ ∥ qdr_cvx.edge_nd₄₁)

def Quadrilateral.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases qdr IsConvex
  · exact (Quadrilateral_cvx.mk_is_convex h).IsParallelogram
  · exact False 

postfix : 50 "IsPRG" => Quadrilateral.IsParallelogram

variable {P : Type _} [EuclideanPlane P]

section criteria
variable {A B C D : P} (h : (QDR A B C D) IsConvex)
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
  · simp [j]
  · simp [j] at h



theorem nd₁₃_of_is_prg (h : QDR A B C D IsPRG) : C ≠ A := by
  have s : (QDR A B C D) IsConvex:= by
    exact is_convex_of_is_prg h
  unfold  Quadrilateral.IsConvex at s
  by_cases j: C ≠ A
  · simp [j]
  · simp [j] at s

theorem nd₂₄_of_is_prg (h : QDR A B C D IsPRG) : D ≠ B := by
  have s : (QDR A B C D) IsConvex:= by
    exact is_convex_of_is_prg h
  unfold  Quadrilateral.IsConvex at s
  by_cases j:  D ≠ B
  · simp [j]
  · simp [j] at s
  
theorem nd₁₂_of_is_prg (h : QDR A B C D IsPRG) : B ≠ A := by
  have s : (QDR A B C D) IsConvex:= by
    exact is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₂

theorem nd₂₃_of_is_prg (h : QDR A B C D IsPRG) : C ≠ B := by
  have s : (QDR A B C D) IsConvex:= by
    exact is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₂₃

theorem nd₃₄_of_is_prg (h : QDR A B C D IsPRG) : D ≠ C := by
  have s : (QDR A B C D) IsConvex:= by
    exact is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₃₄

theorem nd₄₁_of_is_prg (h : QDR A B C D IsPRG) : A ≠ D := by
  have s : (QDR A B C D) IsConvex:= by
    exact is_convex_of_is_prg h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₄₁


/- 
3. nd₂₄_of_is_prg
4. nd₁₂_of_is_prg
5. nd₂₃_of_is_prg
6. nd₃₄_of_is_prg
7. nd₄₁_of_is_prg
-/

theorem para_of_is_prg (h : QDR A B C D IsPRG) : LinearObj.seg_nd (SEG_nd A B sorry) ∥ SEG_nd D C sorry := sorry

theorem para_of_is_prg' (h : QDR A B C D IsPRG) : LinearObj.seg_nd (SEG_nd B C sorry) ∥ SEG_nd D A sorry := sorry

/- 
10. eq_length_of_is_prg -- length AB = length CD
11. eq_length_of_is_prg'
12. eq_angle_value_of_is_prg -- 2 pairs of angles are equal, use ANG
13. eq_angle_value_of_is_prg'
-/

theorem eq_midpt_of_diag_inx_of_is_prg {E : P} (h : QDR A B C D IsPRG) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg h)) = (SEG A C).midpoint := sorry

theorem eq_midpt_of_diag_inx_of_is_prg' {E : P} (h : QDR A B C D IsPRG) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg h)) = (SEG B D).midpoint := sorry

theorem parallelogram_law (h : QDR A B C D IsPRG) : 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2
:= sorry

end property

end EuclidGeom
>>>>>>> 4a692f2e4ef85131a4b42a5a699b5dde8fd3bf1e
