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
1. is_prg_of_
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

theorem para_of_is_prg (h : QDR A B C D IsPRG) : LinearObj.seg_nd (SEG_nd A B sorry) ∥ SEG_nd D C sorry := sorry

theorem para_of_is_prg' (h : QDR A B C D IsPRG) : LinearObj.seg_nd (SEG_nd B C sorry) ∥ SEG_nd D A sorry := sorry

/- 
10. eq_length_of_is_prg -- length AB = length CD
11. eq_length_of_is_prg'
12. eq_angle_value_of_is_prg -- 2 pairs of angles are equal, use ANG
13. eq_angle_value_of_is_prg'
-/

theorem eq_length_of_diag_inx_of_is_prg {E : P} (h : QDR A B C D IsPRG) (e : E = Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg h))) : (SEG A E).length = (SEG C E).length := sorry

theorem eq_length_of_diag_inx_of_is_prg' {E : P} (h : QDR A B C D IsPRG) (e : E = Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg h))) : (SEG B E).length = (SEG D E).length := sorry

theorem parallelogram_law (h : QDR A B C D IsPRG) : 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2
:= sorry

end property

end EuclidGeom