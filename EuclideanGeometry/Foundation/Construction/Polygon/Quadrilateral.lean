import EuclideanGeometry.Foundation.Axiom.Position.Convex
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash

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
structure Quadrilateral (P : Type _) [EuclideanPlane P] where
  point₁ : P
  point₂ : P
  point₃ : P
  point₄ : P

/-- For four points $A$ $B$ $C$ $D$ on a plane, instead of writing Quadrilateral.mk $A$ $B$ $C$ $D$ for the quadrilateral formed by $A$ $B$ $C$ $D$, we use QDR $A$ $B$ $C$ $D$ to denote such a quadrilateral. -/
scoped notation "QDR" => Quadrilateral.mk

namespace Quadrilateral
variable {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P}

/-- Given a quadrilateral qdr, qdr.edge₁₂ is the edge from the first point to the second point of a quadrilateral. -/
@[pp_dot]
def edge₁₂ : Seg P := SEG qdr.1 qdr.2

/-- The edge from the second point to the third point of a quadrilateral -/
@[pp_dot]
def edge₂₃ : Seg P := SEG qdr.2 qdr.3

/-- The edge from the third point to the fourth point of a quadrilateral -/
@[pp_dot]
def edge₃₄ : Seg P := SEG qdr.3 qdr.4

/-- The edge from the 1st point to the 4th point of a quadrilateral -/
@[pp_dot]
def edge₁₄ : Seg P := SEG qdr.1 qdr.4

/-- The diagonal from the first point to the third point of a quadrilateral -/
@[pp_dot]
def diag₁₃ : Seg P := SEG qdr.1 qdr.3

/-- The diagonal from the second point to the fourth point of a quadrilateral -/
@[pp_dot]
def diag₂₄ : Seg P := SEG qdr.2 qdr.4

end Quadrilateral

/--
A quadrilateral is called convex if
1. both diagnals are non-degenerate,
2. two diagonals are not parallel to each other,
3. the interior of two diagonals intersect at one point, i.e. the intersection point of the underlying lines of the diagonals lies in the interior of both diagonals.
-/
@[pp_dot]
def Quadrilateral.IsConvex {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases h : ((qdr.point₁ ≠ qdr.point₃) ∧ (qdr.point₂ ≠ qdr.point₄))
  · by_cases g : (¬ SEG_nd qdr.point₂ qdr.point₄ (h.2).symm ∥ (SEG_nd qdr.point₁ qdr.point₃ (h.1).symm))
    · exact Line.inx (SEG_nd qdr.point₁ qdr.point₃ (h.1).symm).toLine (SEG_nd qdr.point₂ qdr.point₄ (h.2).symm).toLine (Ne.symm g) LiesInt (SEG qdr.point₁ qdr.point₃) ∧ Line.inx (SEG_nd qdr.point₁ qdr.point₃ (h.1).symm).toLine (SEG_nd qdr.point₂ qdr.point₄ (h.2).symm).toLine (Ne.symm g) LiesInt (SEG qdr.point₂ qdr.point₄)
    · exact False
  · exact False

scoped postfix : 50 "IsConvex" => Quadrilateral.IsConvex

/--
Class of Convex Quadrilateral: A convex quadrilateral is quadrilateral with the property of convex.
-/
@[ext]
structure Quadrilateral_cvx (P : Type _) [EuclideanPlane P] extends Quadrilateral P where
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

section criteria_cvx
variable {A B C D : P}

-- theorem is_convex_of four inferior angle
-- theorem is_convex_of both diag divids other pts
-- theorem is_convex_of three side
-- `to be added`

end criteria_cvx

section property
-- properties of convex quadrilateral `to be added`

variable {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P)

/-- Given a convex quadrilateral qdr_cvx, diagonal from the first point to the second point is not degenerate, i.e. the second point is not equal to the first point. -/
theorem nd₁₃ : qdr_cvx.point₃ ≠ qdr_cvx.point₁ := by
  have h: qdr_cvx.IsConvex := convex _
  unfold Quadrilateral.IsConvex at h
  by_cases k: qdr_cvx.point₁ ≠ qdr_cvx.point₃ ∧ qdr_cvx.point₂ ≠ qdr_cvx.point₄
  exact k.left.symm
  simp only [k, dite_false] at h

/-- Given a convex quadrilateral qdr_cvx, diagonal from the first point to the second point is not degenerate, i.e. the second point is not equal to the first point. -/
theorem nd₂₄ : qdr_cvx.point₄ ≠ qdr_cvx.point₂ := by
  have h: qdr_cvx.IsConvex := convex _
  unfold Quadrilateral.IsConvex at h
  by_cases k: qdr_cvx.point₁ ≠ qdr_cvx.point₃ ∧ qdr_cvx.point₂ ≠ qdr_cvx.point₄
  exact k.right.symm
  simp only [k, dite_false] at h

/-- The non-degenerate diagonal from the first point and third point of a convex quadrilateral -/
def diag_nd₁₃ : SegND P := SEG_nd qdr_cvx.point₁ qdr_cvx.point₃ qdr_cvx.nd₁₃

/-- The non-degenerate diagonal from the second point and fourth point of a convex quadrilateral -/
def diag_nd₂₄ : SegND P := SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.nd₂₄

/-- Two diagonals are not parallel to each other -/
theorem diag_not_para : ¬ qdr_cvx.diag_nd₁₃ ∥ qdr_cvx.diag_nd₂₄ := by
  have h: qdr_cvx.point₁ ≠ qdr_cvx.point₃ ∧ qdr_cvx.point₂ ≠ qdr_cvx.point₄ := ⟨qdr_cvx.nd₁₃.symm, qdr_cvx.nd₂₄.symm⟩
  have k: qdr_cvx.IsConvex := convex _
  unfold Quadrilateral.IsConvex at k
  simp only [ne_eq, h, not_false_eq_true, and_self, dite_true] at k
  by_contra q
  have r: qdr_cvx.diag_nd₂₄ ∥ qdr_cvx.diag_nd₁₃ := by exact q.symm
  rw [diag_nd₁₃, diag_nd₂₄] at r
  simp [r] at k

/-- The intersection point of two diagonals -/
@[pp_dot]
def diag_inx : P := Line.inx qdr_cvx.diag_nd₁₃.toLine qdr_cvx.diag_nd₂₄.toLine qdr_cvx.diag_not_para

/-- The interior of two diagonals intersect at one point, i.e. the intersection point of the underlying lines of the diagonals lies in the interior of both diagonals. -/
theorem diag_inx_lies_int : qdr_cvx.diag_inx LiesInt qdr_cvx.diag_nd₁₃.1 ∧ qdr_cvx.diag_inx LiesInt qdr_cvx.diag_nd₂₄.1
:= by
  have h: qdr_cvx.point₁ ≠ qdr_cvx.point₃ ∧ qdr_cvx.point₂ ≠ qdr_cvx.point₄ := ⟨qdr_cvx.nd₁₃.symm, qdr_cvx.nd₂₄.symm⟩
  have k: qdr_cvx.IsConvex := convex _
  unfold Quadrilateral.IsConvex at k
  simp only [ne_eq, h, not_false_eq_true, and_self, dite_true] at k
  have g: ¬ qdr_cvx.diag_nd₂₄ ∥ qdr_cvx.diag_nd₁₃ := Ne.symm qdr_cvx.diag_not_para
  rw [diag_nd₁₃, diag_nd₂₄] at g
  simp only [g, dite_true] at k
  exact k

/-- Given a convex quadrilateral qdr_cvx ABCD, quadrilateral QDR BCDA is also convex. -/
theorem permute_is_convex : (QDR qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁) IsConvex := by
  unfold Quadrilateral.IsConvex
  have h : qdr_cvx.point₂ ≠ qdr_cvx.point₄ ∧ qdr_cvx.point₃ ≠ qdr_cvx.point₁ := ⟨qdr_cvx.nd₂₄.symm, qdr_cvx.nd₁₃⟩
  simp only [ne_eq, h, not_false_eq_true, and_self, dite_true]
  have g: ¬ qdr_cvx.diag_nd₁₃ ∥ qdr_cvx.diag_nd₂₄ := qdr_cvx.diag_not_para
  rw [diag_nd₁₃, diag_nd₂₄] at g
  have g': ¬ (SEG_nd qdr_cvx.point₃ qdr_cvx.point₁ h.2.symm) ∥ (SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ h.1.symm) := by
    apply Ne.symm (SegND.not_para_rev_of_not_para (Ne.symm g))
  simp only [g', not_false_eq_true, dite_true]
  have g'': ¬ (SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ h.1.symm) ∥ (SEG_nd qdr_cvx.point₃ qdr_cvx.point₁ h.2.symm) := Ne.symm g'
  have nd₃₁_eq_nd₁₃ : (SEG_nd qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.nd₁₃.symm).toLine = (SEG_nd qdr_cvx.point₁ qdr_cvx.point₃ qdr_cvx.nd₁₃).toLine := by
    exact (Line.line_of_pt_pt_eq_rev qdr_cvx.nd₁₃.symm)
  have inx_eq : qdr_cvx.diag_inx = LineInx (SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.nd₂₄).toLine (SEG_nd qdr_cvx.point₁ qdr_cvx.point₃ qdr_cvx.nd₁₃).toLine (Ne.symm qdr_cvx.diag_not_para) := Eq.symm (Line.inx.symm (SegND.not_para_toLine_of_not_para qdr_cvx.diag_nd₁₃ qdr_cvx.diag_nd₂₄ qdr_cvx.diag_not_para))
  rcases qdr_cvx.diag_inx_lies_int with ⟨a, b⟩
  have inx_eq' : qdr_cvx.diag_inx = Line.inx (SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.nd₂₄).toLine (SEG_nd qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.nd₁₃.symm).toLine g'':= by
    rw [inx_eq]
    congr 1
    exact nd₃₁_eq_nd₁₃.symm
  rw [←inx_eq']
  exact ⟨b, (Seg.lies_int_rev_iff_lies_int.mp a)⟩

/-- Given a convex quadrilateral qdr_cvx, edge from the first point to the second point is not degenerate, i.e. the second point is not equal to the first point. -/
theorem nd₁₂ : qdr_cvx.point₂ ≠ qdr_cvx.point₁ := by
  have h: qdr_cvx.point₁ ≠ qdr_cvx.point₃ ∧ qdr_cvx.point₂ ≠ qdr_cvx.point₄ := ⟨qdr_cvx.nd₁₃.symm, qdr_cvx.nd₂₄.symm⟩
  have k: qdr_cvx.IsConvex := convex _
  unfold Quadrilateral.IsConvex at k
  simp only [ne_eq, h, not_false_eq_true, and_self, dite_true] at k
  have g: ¬ qdr_cvx.diag_nd₂₄ ∥ qdr_cvx.diag_nd₁₃ := Ne.symm qdr_cvx.diag_not_para
  rw [diag_nd₁₃, diag_nd₂₄] at g
  simp only [g, dite_true] at k
  by_contra q
  have point₁_lieson_diag_nd₁₃: qdr_cvx.point₁ LiesOn qdr_cvx.diag_nd₁₃ := qdr_cvx.diag_nd₁₃.source_lies_on
  have point₁_lieson_diag_nd₂₄: qdr_cvx.point₁ LiesOn qdr_cvx.diag_nd₂₄ := by
    rw [←q]
    exact qdr_cvx.diag_nd₂₄.source_lies_on
  have s: qdr_cvx.point₁ IsInxOf qdr_cvx.diag_nd₁₃.toLine qdr_cvx.diag_nd₂₄.toLine := ⟨seg_lies_on_line point₁_lieson_diag_nd₁₃, seg_lies_on_line point₁_lieson_diag_nd₂₄⟩
  have t: qdr_cvx.diag_inx = qdr_cvx.point₁ := unique_of_inx_of_line_of_not_para qdr_cvx.diag_not_para s (Line.inx_is_inx qdr_cvx.diag_not_para (l₁ := qdr_cvx.diag_nd₁₃.toLine) (l₂ := qdr_cvx.diag_nd₂₄.toLine))
  have point₁_lies_int_diag_nd₁₃: qdr_cvx.point₁ LiesInt qdr_cvx.diag_nd₁₃ := by
    rw [←t]
    exact qdr_cvx.diag_inx_lies_int.1
  have point₁_not_lies_int_diag_nd₁₃: ¬ qdr_cvx.point₁ LiesInt qdr_cvx.diag_nd₁₃ := qdr_cvx.diag_nd₁₃.source_not_lies_int
  exact point₁_not_lies_int_diag_nd₁₃ point₁_lies_int_diag_nd₁₃

/-- Given a convex quadrilateral qdr_cvx, edge from the 2nd point to the 3rd point is not degenerate, i.e. the second point is not equal to the first point. -/
theorem nd₂₃ : qdr_cvx.point₃ ≠ qdr_cvx.point₂ := by
  let permute := (QDR qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁)
  have h : permute IsConvex := permute_is_convex qdr_cvx
  let permute_convex := mk_is_convex h
  exact permute_convex.nd₁₂

/-- Given a convex quadrilateral qdr_cvx, edge from the 3rd point to the 4th point is not degenerate, i.e. the second point is not equal to the first point. -/
theorem nd₃₄ : qdr_cvx.point₄ ≠ qdr_cvx.point₃ := by
  let permute := (QDR qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁)
  have h : permute IsConvex := permute_is_convex qdr_cvx
  let permute_convex := mk_is_convex h
  exact permute_convex.nd₂₃

/-- Given a convex quadrilateral qdr_cvx, edge from the 1st point to the 4th point is not degenerate, i.e. the second point is not equal to the first point. -/
theorem nd₁₄ : qdr_cvx.point₄ ≠ qdr_cvx.point₁ := by
  let permute := (QDR qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁)
  have h : permute IsConvex := permute_is_convex qdr_cvx
  let permute_convex := mk_is_convex h
  exact permute_convex.nd₃₄.symm

/-- The edge from the first point to the second point of a quadrilateral -/
@[pp_dot]
def edge_nd₁₂ : SegND P := SEG_nd qdr_cvx.point₁ qdr_cvx.point₂ (qdr_cvx.nd₁₂)

/-- The edge from the second point to the third point of a quadrilateral -/
@[pp_dot]
def edge_nd₂₃ : SegND P := SEG_nd qdr_cvx.point₂ qdr_cvx.point₃ (qdr_cvx.nd₂₃)

/-- The edge from the third point to the fourth point of a quadrilateral -/
@[pp_dot]
def edge_nd₃₄ : SegND P := SEG_nd qdr_cvx.point₃ qdr_cvx.point₄ (qdr_cvx.nd₃₄)

/-- The edge from the fourth point to the first point of a quadrilateral -/
@[pp_dot]
def edge_nd₁₄ : SegND P := SEG_nd qdr_cvx.point₁ qdr_cvx.point₄ (qdr_cvx.nd₁₄)

/-- Given a convex quadrilateral qdr_cvx, its 1st, 2nd and 3rd points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₁ point₂}$ is not the same as the projective direction of the vector $\overrightarrow{point₁ point₃}$. -/
theorem not_colinear₁₂₃ : ¬ colinear qdr_cvx.1.1 qdr_cvx.1.2 qdr_cvx.1.3 := sorry

/-- Given a convex quadrilateral qdr_cvx, its 2nd, 3rd and 4th points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₂ point₃}$ is not the same as the projective direction of the vector $\overrightarrow{point₂ point₄}$. -/
theorem not_colinear₂₃₄ : ¬ colinear qdr_cvx.1.2 qdr_cvx.1.3 qdr_cvx.1.4 := sorry

/-- Given a convex quadrilateral qdr_cvx, its 3rd, 4th and 1st points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₃ point₄}$ is not the same as the projective direction of the vector $\overrightarrow{point₃ point₁}$. -/
theorem not_colinear₃₄₁ : ¬ colinear qdr_cvx.1.3 qdr_cvx.1.4 qdr_cvx.1.1 := sorry

/-- Given a convex quadrilateral qdr_cvx, its 4th, 1st and 3rd points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₃ point₄}$ is not the same as the projective direction of the vector $\overrightarrow{point₃ point₁}$. -/
theorem not_colinear₄₁₃ : ¬ colinear qdr_cvx.1.4 qdr_cvx.1.1 qdr_cvx.1.3 := sorry

/-- Given a convex quadrilateral qdr_cvx, its 4th, 3rd and 1st points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₃ point₄}$ is not the same as the projective direction of the vector $\overrightarrow{point₃ point₁}$. -/
theorem not_colinear₄₃₁ : ¬ colinear qdr_cvx.1.4 qdr_cvx.1.3 qdr_cvx.1.1 := sorry

/-- Given a convex quadrilateral qdr_cvx, its 1st, 4th and 3rd points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₃ point₄}$ is not the same as the projective direction of the vector $\overrightarrow{point₃ point₁}$. -/
theorem not_colinear₁₄₃ : ¬ colinear qdr_cvx.1.1 qdr_cvx.1.4 qdr_cvx.1.3 := sorry

/-- Given a convex quadrilateral qdr_cvx, its 4th, 1st and 2nd points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₄ point₁}$ is not the same as the projective direction of the vector $\overrightarrow{point₄ point₂}$. -/
theorem not_colinear₄₁₂ : ¬ colinear qdr_cvx.1.4 qdr_cvx.1.1 qdr_cvx.1.2 := sorry

/-- Given a convex quadrilateral qdr_cvx, its 2nd, 1st and 4th points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₄ point₁}$ is not the same as the projective direction of the vector $\overrightarrow{point₄ point₂}$. -/
theorem not_colinear₂₁₄ : ¬ colinear qdr_cvx.1.2 qdr_cvx.1.1 qdr_cvx.1.4 := sorry

/-- Given a convex quadrilateral qdr_cvx, its 1st, 4th and 2nd points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₄ point₁}$ is not the same as the projective direction of the vector $\overrightarrow{point₄ point₂}$. -/
theorem not_colinear₁₄₂ : ¬ colinear qdr_cvx.1.1 qdr_cvx.1.4 qdr_cvx.1.2 := sorry

/-- Given a convex quadrilateral qdr_cvx, its 1st, 2nd and 4th points are not colinear, i.e. the projective direction of the vector $\overrightarrow{point₄ point₁}$ is not the same as the projective direction of the vector $\overrightarrow{point₄ point₂}$. -/
theorem not_colinear₁₂₄ : ¬ colinear qdr_cvx.1.1 qdr_cvx.1.2 qdr_cvx.1.4 := sorry

-- We need to add a bunch of such theorems as they may be useful in discussing general quadrilaterals, i.e. not convex, even as contradictory in proofs.

/--angle at point₁ of qdr_cvx-/
@[pp_dot]
def angle₁ : Angle P := ANG qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.nd₁₄ qdr_cvx.nd₁₂

/--angle at point₂ of qdr_cvx-/
@[pp_dot]
def angle₂ : Angle P := ANG qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.nd₁₂.symm qdr_cvx.nd₂₃

/--angle at point₃ of qdr_cvx-/
@[pp_dot]
def angle₃ : Angle P := ANG qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.nd₂₃.symm qdr_cvx.nd₃₄

/--angle at point₄ of qdr_cvx-/
@[pp_dot]
def angle₄ : Angle P := ANG qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.nd₃₄.symm qdr_cvx.nd₁₄.symm

/--triangle point₄ point₁ point₂, which includes angle₁-/
@[pp_dot]
def triangle₁ : Triangle_nd P := TRI_nd qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.not_colinear₄₁₂

/--triangle point₁ point₂ point₃, which includes angle₂-/
@[pp_dot]
def triangle₂ : Triangle_nd P := TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃

/--triangle point₂ point₃ point₄, which includes angle₃-/
@[pp_dot]
def triangle₃ : Triangle_nd P := TRI_nd qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.not_colinear₂₃₄

/--triangle point₃ point₄ point₁, which includes angle₄-/
@[pp_dot]
def triangle₄ : Triangle_nd P := TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁

theorem cclock_eq : qdr_cvx.triangle₁.is_cclock ↔ qdr_cvx.triangle₃.is_cclock := sorry

theorem cclock_eq' : qdr_cvx.triangle₂.is_cclock ↔ qdr_cvx.triangle₄.is_cclock := sorry

end property

end Quadrilateral_cvx

section criteria
-- the criteria of a quadrilateral being convex `to be added`

end criteria

end EuclidGeom
