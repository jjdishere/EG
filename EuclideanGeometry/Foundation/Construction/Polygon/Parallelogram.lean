import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral

/-!

-/
noncomputable section
namespace EuclidGeom

def Quadrilateral_cvx.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P) : Prop := (qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) ∧ (qdr_cvx.edge_nd₂₃ ∥ qdr_cvx.edge_nd₄₁)

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
  sorry

theorem nd₁₃_of_is_prg (h : QDR A B C D IsPRG) : C ≠ A := sorry

/-
3. nd₂₄_of_is_prg
4. nd₁₂_of_is_prg
5. nd₂₃_of_is_prg
6. nd₃₄_of_is_prg
7. nd₄₁_of_is_prg
-/

theorem para_of_is_prg (h : QDR A B C D IsPRG) : SEG_nd A B sorry ∥ SEG_nd D C sorry := sorry

theorem para_of_is_prg' (h : QDR A B C D IsPRG) : SEG_nd B C sorry ∥ SEG_nd D A sorry := sorry

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
