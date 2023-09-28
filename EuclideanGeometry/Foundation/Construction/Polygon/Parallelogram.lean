import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral

/-!

-/
noncomputable section
namespace EuclidGeom

def Quadrilateral_cvx.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P) : Prop := (LinearObj.seg_nd qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) ∧ (LinearObj.seg_nd qdr_cvx.edge_nd₂₃ ∥ qdr_cvx.edge_nd₄₁)

def Quadrilateral.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases qdr.IsConvex
  · exact (Quadrilateral_cvx.mk_is_convex h).IsParallelogram
  · exact False 

postfix : 50 "IsPRG" => Quadrilateral.IsParallelogram

variable {P : Type _} [EuclideanPlane P]

section criteria

variable (qdr : Quadrilateral P)
/- 

-/
end criteria

section property

theorem cvx_of_is_prg 

end property

end EuclidGeom