import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral

/-!

-/
noncomputable section
namespace EuclidGeom

class Parallelogram (P : Type*) [EuclideanPlane P] extends Quadrilateral_cvx P where
  para : LinearObj.seg_nd toQuadrilateral_cvx.edgeND₁₂ ∥ toQuadrilateral_cvx.edgeND₃₄
  para' : LinearObj.seg_nd toQuadrilateral_cvx.edgeND₂₃ ∥ toQuadrilateral_cvx.edgeND₄₁

/-
section make
namespace Parallelogram
/-
construct parallelgram from (protected def)
1. a point and 2 VecND that is not parallel
2. 3 point that is not collinear
-/

end Parallelogram
end make
-/

def Quadrilateral_cvx.is_parallelogram {P : Type*} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P) : Prop := (LinearObj.seg_nd qdr_cvx.edgeND₁₂ ∥ qdr_cvx.edgeND₃₄) ∧ (LinearObj.seg_nd qdr_cvx.edgeND₂₃ ∥ qdr_cvx.edgeND₄₁)

def Quadrilateral.is_parallelogram {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases qdr.IsConvex
  · exact (Quadrilateral_cvx.mk_is_convex h).is_parallelogram
  · exact False

theorem Parallelogram.is_parallelgram : sorry := sorry

def Parallelogram.mk_is_parallelgram {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr.is_parallelogram) : Parallelogram P := sorry

section criteria
/-

-/

end criteria

section property

end property

end EuclidGeom

  /-
  nd₁₃ : point₃ ≠ point₁
  nd₂₄ : point₄ ≠ point₂
  diag_not_para : ¬ SEG_nd point₂ point₄ nd₂₄ ∥ (LinearObj.seg_nd (SEG_nd point₁ point₃ nd₁₃))
  diag_intx : Line.inx (SEG_nd point₁ point₃ nd₁₃).toLine (SEG_nd point₂ point₄ nd₂₄).toLine diag_not_para LiesInt (SEG point₁ point₃) ∧ Line.inx (SEG_nd point₁ point₃ nd₁₃).toLine (SEG_nd point₂ point₄ nd₂₄).toLine diag_not_para LiesInt (SEG point₂ point₄)
  -/
