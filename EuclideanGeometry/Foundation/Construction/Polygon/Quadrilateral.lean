import EuclideanGeometry.Foundation.Axiom.Position.Convex
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

/-!
# Quadrilateral

In this file we define general quadrilaterals as four points on the plane and convex quadrilaterals.

## Important Definitions
* `Quadrilateral P` : general quadrilaterals on the plane `P`, i.e. four points on `P`
* `Quadrilateral_cvx P` : convex quadrilaterals on the plane `P`

## Notation
* `QDR A B C D` : notation for quadrilateral `A B C D`

## Implementation Notes
Currently, we just defines general quadrilaterals and convex quadrilaterals. There are more classes in between. For example, quadrilateral without self-intersection, quadrilateral of non-degenerate (which means it does not self-intersect and not degenerate to a triangle).
Of course many definitions work on these classes already, but without necessarity in application, we will not formalize these class for present.
-/

noncomputable section
namespace EuclidGeom

/-- Class of Quadrilateral: A quadrilateral consists of four points; it is the generalized quadrilateral formed by these four points -/
@[ext]
class Quadrilateral (P : Type _) [EuclideanPlane P] where
  point₁ : P
  point₂ : P
  point₃ : P
  point₄ : P

/-- For four points $A$ $B$ $C$ $D$ on a plane, instead of writing Quadrilateral.mk $A$ $B$ $C$ $D$ for the quadrilateral formed by $A$ $B$ $C$ $D$, we use QDR $A$ $B$ $C$ $D$ to denote such a quadrilateral. -/
scoped notation "QDR" => Quadrilateral.mk

namespace Quadrilateral
variable {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P}

/-- Given a quadrilateral qdr, qdr.edge₁₂ is the edge from the first point to the second point of a quadrilateral. -/
def edge₁₂ : Seg P := SEG qdr.1 qdr.2

/-- The edge from the second point to the third point of a quadrilateral -/
def edge₂₃ : Seg P := SEG qdr.2 qdr.3

/-- The edge from the third point to the fourth point of a quadrilateral -/
def edge₃₄ : Seg P := SEG qdr.3 qdr.4

/-- The edge from the 1st point to the 4th point of a quadrilateral -/
def edge₁₄ : Seg P := SEG qdr.1 qdr.4

/-- The diagonal from the first point to the third point of a quadrilateral -/
def diag₁₃ : Seg P := SEG qdr.1 qdr.3

/-- The diagonal from the second point to the fourth point of a quadrilateral -/
def diag₂₄ : Seg P := SEG qdr.2 qdr.4

end Quadrilateral


/--
A quadrilateral is called convex if
1. both diagnals are non-degenerate,
2. two diagonals are not parallel to each other,
3. the interior of two diagonals intersect at one point, i.e. the intersection point of the underlying lines of the diagonals lies in the interior of both diagonals.
-/
def Quadrilateral.IsConvex {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases ((qdr.point₁ ≠ qdr.point₃) ∧ (qdr.point₂ ≠ qdr.point₄))
  · by_cases g : (¬ SEG_nd qdr.point₂ qdr.point₄ (h.2).symm ∥ (SEG_nd qdr.point₁ qdr.point₃ (h.1).symm))
    · exact Line.inx (SEG_nd qdr.point₁ qdr.point₃ (h.1).symm).toLine (SEG_nd qdr.point₂ qdr.point₄ (h.2).symm).toLine g LiesInt (SEG qdr.point₁ qdr.point₃) ∧ Line.inx (SEG_nd qdr.point₁ qdr.point₃ (h.1).symm).toLine (SEG_nd qdr.point₂ qdr.point₄ (h.2).symm).toLine g LiesInt (SEG qdr.point₂ qdr.point₄)
    · exact False
  · exact False

scoped postfix : 50 "IsConvex" => Quadrilateral.IsConvex

/--
Class of Convex Quadrilateral: A convex quadrilateral is quadrilateral with the property of convex.
-/
@[ext]
class Quadrilateral_cvx (P : Type _) [EuclideanPlane P] extends Quadrilateral P where
  convex : toQuadrilateral IsConvex

def Quadrilateral_cvx.mk_pt_pt_pt_pt_convex {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D) IsConvex) : Quadrilateral_cvx P where
  toQuadrilateral := (QDR A B C D)
  convex := h

scoped notation "QDR_cvx" => Quadrilateral_cvx.mk_pt_pt_pt_pt_convex

namespace Quadrilateral_cvx

/-- Given a property that a quadrilateral qdr is convex, this function returns qdr itself as an object in the class of convex quadrilateral-/
def mk_is_convex {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsConvex) : Quadrilateral_cvx P where
  toQuadrilateral := qdr
  convex := h

section property
-- properties of convex quadrilateral `to be added`

variable {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P)

/-- Given a convex quadrilateral qdr_cvx, diagonal from the first point to the second point is not degenerate, i.e. the second point is not equal to the first point. -/
theorem nd₁₃ : qdr_cvx.point₃ ≠ qdr_cvx.point₁ := sorry

/-- Given a convex quadrilateral qdr_cvx, diagonal from the first point to the second point is not degenerate, i.e. the second point is not equal to the first point. -/
theorem nd₂₄ : qdr_cvx.point₄ ≠ qdr_cvx.point₂ := sorry

/-- The non-degenerate diagonal from the first point and third point of a convex quadrilateral -/
def diag_nd₁₃ : Seg_nd P := SEG_nd qdr_cvx.point₁ qdr_cvx.point₃ qdr_cvx.nd₁₃

/-- The non-degenerate diagonal from the second point and fourth point of a convex quadrilateral -/
def diag_nd₂₄ : Seg_nd P := SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.nd₂₄

/-- Given a convex quadrilateral qdr_cvx, edge from the first point to the second point is not degenerate, i.e. the second point is not equal to the first point. -/
theorem nd₁₂ : qdr_cvx.point₂ ≠ qdr_cvx.point₁ := sorry

/-- Given a convex quadrilateral qdr_cvx, edge from the 2nd point to the 3rd point is not degenerate, i.e. the second point is not equal to the first point. -/
theorem nd₂₃ : qdr_cvx.point₃ ≠ qdr_cvx.point₂ := sorry

/-- Given a convex quadrilateral qdr_cvx, edge from the 3rd point to the 4th point is not degenerate, i.e. the second point is not equal to the first point. -/
theorem nd₃₄ : qdr_cvx.point₄ ≠ qdr_cvx.point₃ := sorry

/-- Given a convex quadrilateral qdr_cvx, edge from the 1st point to the 4th point is not degenerate, i.e. the second point is not equal to the first point. -/
theorem nd₁₄ : qdr_cvx.point₄ ≠ qdr_cvx.point₁ := sorry

/-- The edge from the first point to the second point of a quadrilateral -/
def edge_nd₁₂ : Seg_nd P := SEG_nd qdr_cvx.point₁ qdr_cvx.point₂ (qdr_cvx.nd₁₂)

/-- The edge from the second point to the third point of a quadrilateral -/
def edge_nd₂₃ : Seg_nd P := SEG_nd qdr_cvx.point₂ qdr_cvx.point₃ (qdr_cvx.nd₂₃)

/-- The edge from the third point to the fourth point of a quadrilateral -/
def edge_nd₃₄ : Seg_nd P := SEG_nd qdr_cvx.point₃ qdr_cvx.point₄ (qdr_cvx.nd₃₄)

/-- The edge from the fourth point to the first point of a quadrilateral -/
def edge_nd₁₄ : Seg_nd P := SEG_nd qdr_cvx.point₁ qdr_cvx.point₄ (qdr_cvx.nd₁₄)

/-- Two diagonals are not parallel to each other -/
theorem diag_not_para : ¬ qdr_cvx.diag_nd₂₄ ∥ qdr_cvx.diag_nd₁₃ := sorry

def diag_inx : P := Line.inx qdr_cvx.diag_nd₁₃.toLine qdr_cvx.diag_nd₂₄.toLine qdr_cvx.diag_not_para

/-- The interior of two diagonals intersect at one point, i.e. the intersection point of the underlying lines of the diagonals lies in the interior of both diagonals. -/
theorem diag_inx_lies_int : qdr_cvx.diag_inx LiesInt qdr_cvx.diag_nd₁₃.1 ∧ qdr_cvx.diag_inx LiesInt qdr_cvx.diag_nd₂₄.1
:= sorry

theorem not_colinear₁₂₃ : ¬ colinear qdr_cvx.1.1 qdr_cvx.1.2 qdr_cvx.1.3 := sorry

theorem not_colinear₂₃₄ : ¬ colinear qdr_cvx.1.2 qdr_cvx.1.3 qdr_cvx.1.4 := sorry

theorem not_colinear₃₄₁ : ¬ colinear qdr_cvx.1.3 qdr_cvx.1.4 qdr_cvx.1.1 := sorry

theorem not_colinear₄₁₂ : ¬ colinear qdr_cvx.1.4 qdr_cvx.1.1 qdr_cvx.1.2 := sorry
end property

end Quadrilateral_cvx

section criteria
-- the criteria of a quadrilateral being convex `to be added`

end criteria

end EuclidGeom
