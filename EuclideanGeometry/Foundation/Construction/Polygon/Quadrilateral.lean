import EuclideanGeometry.Foundation.Axiom.Position.Convex
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Position.Orientation

/-!
# Quadrilateral

In this file we define general quadrilaterals as four points on the plane and convex quadrilaterals.

## Important Definitions
* `Quadrilateral P` : general quadrilaterals on the plane `P`, i.e. four points on `P`
* `QuadrilateralND P` : quadrilaterals on the plane `P` s.t. the points that adjacent is not same
* `Quadrilateral_cvx P` : convex quadrilaterals on the plane `P`

## Notation
* `QDR A B C D` : notation for quadrilateral `A B C D`

## Implementation Notes
Currently, we just defines general quadrilaterals, non-degenerate quadrilateral (adjacent points are not the same, or cyclic-non-degenerate) and convex quadrilaterals.
There are classes in between. For example, quadrilateral without self-intersection, quadrilateral of stronger non-degenerate (any two points are not same, we call it alternatively-non-degenerate temporarily).
Of course many definitions work on these classes already, but without necessarity in application, we will not formalize these class for present.
-/

noncomputable section
namespace EuclidGeom

open Angle

/-- Class of Quadrilateral: A quadrilateral consists of four points; it is the generalized quadrilateral formed by these four points -/
@[ext]
structure Quadrilateral (P : Type*) [EuclideanPlane P] where
  point₁ : P
  point₂ : P
  point₃ : P
  point₄ : P

/-- For four points $A$ $B$ $C$ $D$ on a plane, instead of writing Quadrilateral.mk $A$ $B$ $C$ $D$ for the quadrilateral formed by $A$ $B$ $C$ $D$, we use QDR $A$ $B$ $C$ $D$ to denote such a quadrilateral. -/
scoped notation "QDR" => Quadrilateral.mk

namespace Quadrilateral
variable {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P}

/-- Given a quadrilateral qdr, qdr.edge₁₂ is the edge from the first point to the second point of a quadrilateral. -/
@[pp_dot]
def edge₁₂ : Seg P := SEG qdr.point₁ qdr.point₂

/-- The edge from the second point to the third point of a quadrilateral -/
@[pp_dot]
def edge₂₃ : Seg P := SEG qdr.point₂ qdr.point₃

/-- The edge from the third point to the fourth point of a quadrilateral -/
@[pp_dot]
def edge₃₄ : Seg P := SEG qdr.point₃ qdr.point₄

/-- The edge from the 1st point to the 4th point of a quadrilateral -/
@[pp_dot]
def edge₁₄ : Seg P := SEG qdr.point₁ qdr.point₄

/-- The diagonal from the first point to the third point of a quadrilateral -/
@[pp_dot]
def diag₁₃ : Seg P := SEG qdr.point₁ qdr.point₃

/-- The diagonal from the second point to the fourth point of a quadrilateral -/
@[pp_dot]
def diag₂₄ : Seg P := SEG qdr.point₂ qdr.point₄

/-- The perm quadrilateral, the first point of the perm is the second point of the origin, etc. -/
@[pp_dot]
def perm : Quadrilateral P := QDR qdr.point₂ qdr.point₃ qdr.point₄ qdr.point₁

/-- The flip quadrilateral, exchanged the second point and the fourth. -/
@[pp_dot]
def flip : Quadrilateral P := QDR qdr.point₁ qdr.point₄ qdr.point₃ qdr.point₂

/- the simp theorems -/
variable (A B C D : P)
@[simp]
theorem edge₁₂_simp : (QDR A B C D).edge₁₂ = (SEG A B) := rfl
@[simp]
theorem edge₂₃_simp : (QDR A B C D).edge₂₃ = (SEG B C) := rfl
@[simp]
theorem edge₃₄_simp : (QDR A B C D).edge₃₄ = (SEG C D) := rfl
@[simp]
theorem edge₁₄_simp : (QDR A B C D).edge₁₄ = (SEG A D) := rfl
@[simp]
theorem diag₁₃_simp : (QDR A B C D).diag₁₃ = (SEG A C) := rfl
@[simp]
theorem diag₂₄_simp : (QDR A B C D).diag₂₄ = (SEG B D) := rfl

@[simp]
theorem perm_simp : (QDR A B C D).perm = (QDR B C D A) := rfl
@[simp]
theorem flip_simp : (QDR A B C D).flip = (QDR A D C B) := rfl

end Quadrilateral

/--
A quadrilateral is called non-degenerate if the points that adjacent is not same
-/
@[pp_dot]
structure Quadrilateral.IsND {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop where
  nd₁₂ : (qdr.2 ≠ qdr.1)
  nd₂₃ : (qdr.3 ≠ qdr.2)
  nd₃₄ : (qdr.4 ≠ qdr.3)
  nd₁₄ : (qdr.4 ≠ qdr.1)

/--
Class of nd Quadrilateral: A nd quadrilateral is quadrilateral with the property of nd.
-/
@[ext]
structure QuadrilateralND (P : Type*) [EuclideanPlane P] extends Quadrilateral P where
  nd : toQuadrilateral.IsND

def QuadrilateralND.mk_pt_pt_pt_pt_nd {P : Type*} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) : QuadrilateralND P where
  toQuadrilateral := (QDR A B C D)
  nd := h

scoped notation "QDR_nd" => QuadrilateralND.mk_pt_pt_pt_pt_nd

/-- Given a property that a quadrilateral qdr is nd, this function returns qdr itself as an object in the class of nd quadrilateral -/
def QuadrilateralND.mk_nd {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr.IsND) : QuadrilateralND P where
  toQuadrilateral := qdr
  nd := h

scoped notation "QDR_nd'" => QuadrilateralND.mk_nd

/-- A quadrilateral satisfies InGPos if every 3 vertices are not collinear. -/
@[pp_dot]
structure Quadrilateral.InGPos {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop where
  not_collinear₁₂₃: ( ¬ Collinear qdr.point₁ qdr.point₂ qdr.point₃)
  not_collinear₂₃₄: ( ¬ Collinear qdr.point₂ qdr.point₃ qdr.point₄)
  not_collinear₃₄₁: ( ¬ Collinear qdr.point₃ qdr.point₄ qdr.point₁)
  not_collinear₄₁₂: ( ¬ Collinear qdr.point₄ qdr.point₁ qdr.point₂)

-- scoped postfix : 50 "IsPrg_GPos" => Quadrilateral.GPos

namespace QuadrilateralND

section property_nd
-- properties of nd quadrilateral `to be added`

variable {P : Type*} [EuclideanPlane P] (qdr_nd : QuadrilateralND P)

/-- The edge from the first point to the second point of a QuadrilateralND is non-degenerate. -/
instance nd₁₂ : PtNe qdr_nd.1.2 qdr_nd.1.1 := Fact.mk qdr_nd.nd.nd₁₂

/-- The edge from the first point to the second point of a QuadrilateralND is non-degenerate. -/
instance nd₂₃ : PtNe qdr_nd.1.3 qdr_nd.1.2 := Fact.mk qdr_nd.nd.nd₂₃

/-- The edge from the first point to the second point of a QuadrilateralND is non-degenerate. -/
instance nd₃₄ : PtNe qdr_nd.1.4 qdr_nd.1.3 := Fact.mk qdr_nd.nd.nd₃₄

/-- The edge from the first point to the second point of a QuadrilateralND is non-degenerate. -/
instance nd₁₄ : PtNe qdr_nd.1.4 qdr_nd.1.1 := Fact.mk qdr_nd.nd.nd₁₄

/-- The edge from the first point to the second point of a quadrilateral -/
@[pp_dot]
def edgeND₁₂ : SegND P := SEG_nd qdr_nd.point₁ qdr_nd.point₂

/-- The edge from the second point to the third point of a quadrilateral -/
@[pp_dot]
def edgeND₂₃ : SegND P := SEG_nd qdr_nd.point₂ qdr_nd.point₃

/-- The edge from the third point to the fourth point of a quadrilateral -/
@[pp_dot]
def edgeND₃₄ : SegND P := SEG_nd qdr_nd.point₃ qdr_nd.point₄

/-- The edge from the fourth point to the first point of a quadrilateral -/
@[pp_dot]
def edgeND₄₁ : SegND P := SEG_nd qdr_nd.point₄ qdr_nd.point₁

/--angle at point₁ of qdr_nd-/
@[pp_dot]
def angle₁ : Angle P := ANG qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂

/--angle at point₂ of qdr_nd-/
@[pp_dot]
def angle₂ : Angle P := ANG qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃

/--angle at point₃ of qdr_nd-/
@[pp_dot]
def angle₃ : Angle P := ANG qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄

/--angle at point₄ of qdr_nd-/
@[pp_dot]
def angle₄ : Angle P := ANG qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁

/--triangle point₄ point₁ point₂, which includes angle₁-/
@[pp_dot]
def triangle₁ : Triangle P := TRI qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂

/--triangle point₁ point₂ point₃, which includes angle₂-/
@[pp_dot]
def triangle₂ : Triangle P := TRI qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃

/--triangle point₂ point₃ point₄, which includes angle₃-/
@[pp_dot]
def triangle₃ : Triangle P := TRI qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄

/--triangle point₃ point₄ point₁, which includes angle₄-/
@[pp_dot]
def triangle₄ : Triangle P := TRI qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁

/-- The perm of QuadrilateralND is also QuadrilateralND. -/
theorem perm_is_nd : (qdr_nd.toQuadrilateral.perm).IsND := ⟨ qdr_nd.nd₂₃.out, qdr_nd.nd₃₄.out, qdr_nd.nd₁₄.out.symm, qdr_nd.nd₁₂.out.symm ⟩

/-- The perm QuadrilateralND, the first point of the perm is the second point of the origin, etc. -/
@[pp_dot]
def perm : QuadrilateralND P := mk_nd (perm_is_nd qdr_nd)

/-- The flip of QuadrilateralND is also QuadrilateralND. -/
theorem flip_is_nd : (qdr_nd.toQuadrilateral.flip).IsND := ⟨ qdr_nd.nd₁₄.out, qdr_nd.nd₃₄.out.symm, qdr_nd.nd₂₃.out.symm, qdr_nd.nd₁₂.out ⟩

/-- The flip QuadrilateralND, exchanged the second point and the fourth. -/
@[pp_dot]
def flip : QuadrilateralND P := mk_nd (flip_is_nd qdr_nd)

/- the simp theorems -/
variable (A B C D : P)

theorem flip_angle₁_value_eq_neg_angle₁ : qdr_nd.flip.angle₁.value = - qdr_nd.angle₁.value := by
  unfold QuadrilateralND.angle₁
  have h := neg_value_of_rev_ang (h₁ := qdr_nd.nd₁₂) (h₂ := qdr_nd.nd₁₄)
  unfold value_of_angle_of_three_point_nd at h
  rw [←h]
  congr 1

theorem flip_angle₂_value_eq_neg_angle₄ : qdr_nd.flip.angle₂.value = - qdr_nd.angle₄.value := by
  unfold QuadrilateralND.angle₄
  have h := neg_value_of_rev_ang (h₁ := qdr_nd.nd₁₄.symm) (h₂ := qdr_nd.nd₃₄.symm)
  unfold value_of_angle_of_three_point_nd at h
  rw [←h]
  congr 1

theorem flip_angle₃_value_eq_neg_angle₃ : qdr_nd.flip.angle₃.value = - qdr_nd.angle₃.value := by
  unfold QuadrilateralND.angle₃
  have h := neg_value_of_rev_ang (h₁ := qdr_nd.nd₃₄) (h₂ := qdr_nd.nd₂₃.symm)
  unfold value_of_angle_of_three_point_nd at h
  rw [←h]
  congr 1

theorem flip_angle₄_value_eq_neg_angle₂ : qdr_nd.flip.angle₄.value = - qdr_nd.angle₂.value := by
  unfold QuadrilateralND.angle₂
  have h := neg_value_of_rev_ang (h₁ := qdr_nd.nd₂₃) (h₂ := qdr_nd.nd₁₂.symm)
  unfold value_of_angle_of_three_point_nd at h
  rw [←h]
  congr 1

end property_nd

/-- A Quadrilateral which satisfies InGPos satisfies IsND. -/
theorem nd_of_gpos {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} (InGPos : qdr.InGPos): qdr.IsND:= by
  constructor
  · exact (ne_of_not_collinear InGPos.not_collinear₁₂₃).right.right
  · exact (ne_of_not_collinear InGPos.not_collinear₂₃₄).right.right
  · exact (ne_of_not_collinear InGPos.not_collinear₃₄₁).right.right
  · exact (ne_of_not_collinear InGPos.not_collinear₄₁₂).right.right.symm

instance {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} : Coe qdr.InGPos qdr.IsND := {coe := nd_of_gpos}

end QuadrilateralND

/--
A Quadrilateral is called convex if it's ND and four angles have the same sign.
-/
-- @[pp_dot]
-- def QuadrilateralND.IsConvex {P : Type*} [EuclideanPlane P] (qdr_nd : QuadrilateralND P) : Prop := (qdr_nd.angle₁.value.IsPos ∧ qdr_nd.angle₂.value.IsPos ∧ qdr_nd.angle₃.value.IsPos ∧ qdr_nd.angle₄.value.IsPos) ∨ (qdr_nd.angle₁.value.IsNeg ∧ qdr_nd.angle₂.value.IsNeg ∧ qdr_nd.angle₃.value.IsNeg ∧ qdr_nd.angle₄.value.IsNeg)

-- @[pp_dot]
-- def Quadrilateral.IsConvex {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
--   by_cases h : qdr.IsND
--   · exact (QuadrilateralND.mk_nd h).IsConvex
--   · exact False

@[pp_dot]
def Quadrilateral.IsConvex {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases h : qdr.IsND
  · have qdr_nd : QuadrilateralND P := QDR_nd' h
    exact (qdr_nd.angle₁.value.IsPos ∧ qdr_nd.angle₂.value.IsPos ∧ qdr_nd.angle₃.value.IsPos ∧ qdr_nd.angle₄.value.IsPos) ∨ (qdr_nd.angle₁.value.IsNeg ∧ qdr_nd.angle₂.value.IsNeg ∧ qdr_nd.angle₃.value.IsNeg ∧ qdr_nd.angle₄.value.IsNeg)
  · exact False

scoped postfix : 50 "IsConvex" => Quadrilateral.IsConvex

theorem Quadrilateral.isND_of_is_convex {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr.IsConvex) : qdr.IsND := by
  by_contra g
  unfold Quadrilateral.IsConvex at h
  simp only [g, dite_false] at h

instance {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} : Coe qdr.IsConvex qdr.IsND := {coe := Quadrilateral.isND_of_is_convex}

-- theorem QuadrilateralND.toqdr_cvx_of_cvx {P : Type*} [EuclideanPlane P] {qdr_nd : QuadrilateralND P} (h : qdr_nd.IsConvex) : qdr_nd.toQuadrilateral.IsConvex := by
--   have k : qdr_nd.toQuadrilateral.IsND := qdr_nd.nd
--   have l : qdr_nd = (QDR_nd' k) := rfl
--   rw [l] at h
--   unfold Quadrilateral.IsConvex
--   simp only [k, h, dite_eq_ite, ite_true]

-- instance {P : Type*} [EuclideanPlane P] {qdr_nd : QuadrilateralND P} : Coe qdr_nd.IsConvex qdr_nd.toQuadrilateral.IsConvex := {coe := QuadrilateralND.toqdr_cvx_of_cvx}

theorem Quadrilateral.nd_cvx_iff_cvx {P : Type*} [EuclideanPlane P] (qdr_nd : QuadrilateralND P) : qdr_nd.IsConvex ↔ (qdr_nd.angle₁.value.IsPos ∧ qdr_nd.angle₂.value.IsPos ∧ qdr_nd.angle₃.value.IsPos ∧ qdr_nd.angle₄.value.IsPos) ∨ (qdr_nd.angle₁.value.IsNeg ∧ qdr_nd.angle₂.value.IsNeg ∧ qdr_nd.angle₃.value.IsNeg ∧ qdr_nd.angle₄.value.IsNeg) := by
  unfold Quadrilateral.IsConvex
  have nd : qdr_nd.toQuadrilateral.IsND := qdr_nd.nd
  simp only [nd, dite_true]
  rfl

theorem Quadrilateral_cvx.nd_is_convex_iff_is_convex {P : Type*} [EuclideanPlane P] (qdr_nd : QuadrilateralND P) : qdr_nd.IsConvex ↔ qdr_nd.toQuadrilateral.IsConvex := by
  unfold Quadrilateral.IsConvex
  simp only [qdr_nd.nd, dite_true]

instance {P : Type*} [EuclideanPlane P] {qdr_nd : QuadrilateralND P} : Coe qdr_nd.IsConvex qdr_nd.toQuadrilateral.IsConvex := {coe := (Quadrilateral_cvx.nd_is_convex_iff_is_convex qdr_nd).mp}

instance {P : Type*} [EuclideanPlane P] {qdr_nd : QuadrilateralND P} : Coe qdr_nd.toQuadrilateral.IsConvex qdr_nd.IsConvex := {coe := (Quadrilateral_cvx.nd_is_convex_iff_is_convex qdr_nd).mpr}

/--
Class of Convex Quadrilateral: A convex quadrilateral is quadrilateral with the property of convex.
-/
@[ext]
structure Quadrilateral_cvx (P : Type*) [EuclideanPlane P] extends QuadrilateralND P where
  convex : toQuadrilateral.IsConvex

def Quadrilateral_cvx.mk_pt_pt_pt_pt_convex {P : Type*} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsConvex) : Quadrilateral_cvx P where
  toQuadrilateral := (QDR A B C D)
  nd := h
  convex := h

scoped notation "QDR_cvx" => Quadrilateral_cvx.mk_pt_pt_pt_pt_convex

def Quadrilateral_cvx.mk_cvx {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr.IsConvex) : Quadrilateral_cvx P where
  toQuadrilateralND := QDR_nd' h
  convex := h

scoped notation "QDR_cvx'" => Quadrilateral_cvx.mk_cvx

namespace Quadrilateral_cvx

-- def mk_is_convex {P : Type*} [EuclideanPlane P] {A B C D : P} (h : (QDR A B C D).IsConvex) : Quadrilateral_cvx P := mk_pt_pt_pt_pt_convex A B C D h

-- /-- Given a property that a quadrilateral qdr is convex, this function returns qdr itself as an object in the class of convex quadrilateral-/
-- def mk_nd_is_convex {P : Type*} [EuclideanPlane P] {qdr_nd : QuadrilateralND P} (h : qdr_nd.IsConvex) : Quadrilateral_cvx P where
--   toQuadrilateralND := qdr_nd
--   convex := h

section criteria_cvx
variable {P : Type*} [EuclideanPlane P] {A B C D : P}

structure is_convex_of_three_sides_of_same_side' where
  qdr_nd : QuadrilateralND P
  same_side₁ : odist_sign qdr_nd.point₁ qdr_nd.edgeND₃₄ = odist_sign qdr_nd.point₂ qdr_nd.edgeND₃₄
  same_side₂ : odist_sign qdr_nd.point₂ qdr_nd.edgeND₄₁ = odist_sign qdr_nd.point₃ qdr_nd.edgeND₄₁
  same_side₃ : odist_sign qdr_nd.point₃ qdr_nd.edgeND₁₂ = odist_sign qdr_nd.point₄ qdr_nd.edgeND₁₂

/- Given QuadrilateralND qdr_nd, if qdr_nd.point₁ and qdr_nd.point₂ are at the same side of qdr_nd.nd₃₄, and it also holds for nd₄₁ and nd₁₂, then it's convex. -/
theorem is_convex_of_three_sides_of_same_side (p : is_convex_of_three_sides_of_same_side' (P := P)) : p.qdr_nd.IsConvex := by
  let qdr_nd := p.qdr_nd
  by_cases h : odist_sign qdr_nd.point₁ qdr_nd.edgeND₃₄ = 1
  · sorry
  · sorry

structure is_convex_of_diag_inx_lies_int' where
  qdr : Quadrilateral P
  ne₁ : qdr.point₁ ≠ qdr.point₃
  ne₂ : qdr.point₂ ≠ qdr.point₄
  diag₁₃ := (SEG_nd qdr.point₁ qdr.point₃ ne₁.symm)
  diag₂₄ := (SEG_nd qdr.point₂ qdr.point₄ ne₂.symm)
  not_para : ¬ diag₁₃ ∥ diag₂₄
  -- inx := LineInx diag₁₃.toLine diag₂₄.toLine not_para
  inx_lies_int₁ : LineInx diag₁₃.toLine diag₂₄.toLine not_para LiesInt diag₁₃
  inx_lies_int₂ : LineInx diag₁₃.toLine diag₂₄.toLine not_para LiesInt diag₂₄

/- Given Quadrilateral qdr, two diagonals intersect in their interior, then qdr is a Quadrilateral_cvx. -/
theorem is_convex_of_diag_inx_lies_int (p : is_convex_of_diag_inx_lies_int' (P := P)) : p.qdr IsConvex := by sorry
  /-
  1. proof it's nd.
  2. proof it's satisfy is_convex_of_three_sides_two_pts_at_same_side.
  3. proof sign of angle₁ = angle₃, angle₂ = angle₄.
  4. because nd₂₃ not divid pt₁ and pt₄, then sign of angle₂ = angle₃.
  -/

-- theorem is_convex_of four inferior angle (seems it's obvious compared with current definition)
-- theorem is_convex_of both diag divids other pts
-- `to be added`

end criteria_cvx

section property_cvx
-- properties of convex quadrilateral `to be added`

variable {P : Type*} [EuclideanPlane P]
variable (qdr : Quadrilateral P)
variable (qdr_nd : QuadrilateralND P)
variable (qdr_cvx : Quadrilateral_cvx P)

/-- The perm of quadrilateral_cvx is also quadrilateral_cvx. -/
theorem perm_is_convex : (QuadrilateralND.perm qdr_cvx.toQuadrilateralND).IsConvex := by
  unfold Quadrilateral.IsConvex
  sorry
  -- unfold Quadrilateral.IsConvex
  -- by_cases h : (qdr_cvx.angle₁.value.IsPos ∧ qdr_cvx.angle₂.value.IsPos ∧ qdr_cvx.angle₃.value.IsPos ∧ qdr_cvx.angle₄.value.IsPos)
  -- · have q : (qdr_cvx.perm.angle₄.value.IsPos ∧ qdr_cvx.perm.angle₁.value.IsPos ∧ qdr_cvx.perm.angle₂.value.IsPos ∧ qdr_cvx.perm.angle₃.value.IsPos) := h
  --   simp only [q, and_self, true_or]
  -- · have p: qdr_cvx.IsConvex := qdr_cvx.convex
  --   unfold Quadrilateral.IsConvex at p
  --   simp only [h, false_or] at p
  --   have q : (qdr_cvx.perm.angle₄.value.IsNeg ∧ qdr_cvx.perm.angle₁.value.IsNeg ∧ qdr_cvx.perm.angle₂.value.IsNeg ∧ qdr_cvx.perm.angle₃.value.IsNeg) := p
  --   simp only [q, and_self, or_true]

/-- The perm quadrilateral_cvx, the first point of the perm is the second point of the origin, etc. -/
def perm : Quadrilateral_cvx P := QDR_cvx' (perm_is_convex qdr_cvx)

/-- Given a convex quadrilateral qdr_cvx ABCD, quadrilateral QDR BCDA is also convex. -/
theorem perm_is_convex' : (QDR qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁) IsConvex := (qdr_cvx.perm).convex

theorem is_convex_iff_perm_is_convex : qdr_nd.IsConvex ↔ qdr_nd.perm.IsConvex := by
  constructor
  intro h
  exact perm_is_convex (QDR_cvx' h)
  intro h
  let q₁ : QuadrilateralND P := qdr_nd.perm.perm
  have h₁ : q₁.IsConvex := perm_is_convex (QDR_cvx' h)
  let q₂ : QuadrilateralND P := qdr_nd.perm.perm.perm
  have h₂ : q₂.IsConvex := perm_is_convex (QDR_cvx' h₁)
  exact perm_is_convex (QDR_cvx' h₂)

/-- The flip of quadrilateral_cvx is also quadrilateral_cvx. -/
theorem flip_is_convex : (QuadrilateralND.flip qdr_cvx.toQuadrilateralND).IsConvex := by
  unfold Quadrilateral.IsConvex
  sorry
  -- by_cases h : (qdr_cvx.angle₁.value.IsPos ∧ qdr_cvx.angle₂.value.IsPos ∧ qdr_cvx.angle₃.value.IsPos ∧ qdr_cvx.angle₄.value.IsPos)
  -- · have q : (qdr_cvx.flip.angle₁.value.IsNeg ∧ qdr_cvx.flip.angle₄.value.IsNeg ∧ qdr_cvx.flip.angle₃.value.IsNeg ∧ qdr_cvx.flip.angle₂.value.IsNeg) := by
  --     rw [(QuadrilateralND.flip_angle₁_value_eq_neg_angle₁ qdr_cvx.toQuadrilateralND), AngValue.neg_isNeg_iff_isPos (θ := qdr_cvx.angle₁.value)]
  --     rw [(QuadrilateralND.flip_angle₄_value_eq_neg_angle₂ qdr_cvx.toQuadrilateralND), AngValue.neg_isNeg_iff_isPos (θ := qdr_cvx.angle₂.value)]
  --     rw [(QuadrilateralND.flip_angle₃_value_eq_neg_angle₃ qdr_cvx.toQuadrilateralND), AngValue.neg_isNeg_iff_isPos (θ := qdr_cvx.angle₃.value)]
  --     rw [(QuadrilateralND.flip_angle₂_value_eq_neg_angle₄ qdr_cvx.toQuadrilateralND), AngValue.neg_isNeg_iff_isPos (θ := qdr_cvx.angle₄.value)]
  --     simp only [h, and_self]
  --   simp only [q, and_self, or_true]
  -- · have p: qdr_cvx.IsConvex := qdr_cvx.convex
  --   unfold QuadrilateralND.IsConvex at p
  --   simp only [h, false_or] at p
  --   have q : (qdr_cvx.flip.angle₁.value.IsPos ∧ qdr_cvx.flip.angle₄.value.IsPos ∧ qdr_cvx.flip.angle₃.value.IsPos ∧ qdr_cvx.flip.angle₂.value.IsPos) := by
  --     rw [(QuadrilateralND.flip_angle₁_value_eq_neg_angle₁ qdr_cvx.toQuadrilateralND), AngValue.neg_isPos_iff_isNeg (θ := qdr_cvx.angle₁.value)]
  --     rw [(QuadrilateralND.flip_angle₄_value_eq_neg_angle₂ qdr_cvx.toQuadrilateralND), AngValue.neg_isPos_iff_isNeg (θ := qdr_cvx.angle₂.value)]
  --     rw [(QuadrilateralND.flip_angle₃_value_eq_neg_angle₃ qdr_cvx.toQuadrilateralND), AngValue.neg_isPos_iff_isNeg (θ := qdr_cvx.angle₃.value)]
  --     rw [(QuadrilateralND.flip_angle₂_value_eq_neg_angle₄ qdr_cvx.toQuadrilateralND), AngValue.neg_isPos_iff_isNeg (θ := qdr_cvx.angle₄.value)]
  --     simp only [p, and_self]
  --   simp only [q, and_self, true_or]

def flip : Quadrilateral_cvx P := QDR_cvx' (flip_is_convex qdr_cvx)

theorem is_convex_iff_flip_is_convex : qdr_nd.IsConvex ↔ qdr_nd.flip.IsConvex := by
  constructor
  intro h
  exact flip_is_convex (QDR_cvx' h)
  intro h
  exact flip_is_convex (QDR_cvx' h)


/-- Given a convex quadrilateral qdr_cvx, diagonal from the first point to the second point is not degenerate, i.e. the second point is not equal to the first point. -/
instance nd₁₃ : PtNe qdr_cvx.point₃ qdr_cvx.point₁ := Fact.mk <| by
  by_contra h
  have g : qdr_cvx.angle₂.value = 0 := by
    unfold QuadrilateralND.angle₂
    simp only [h]
    apply same_dir_iff_value_eq_zero.mp
    simp only [mk_pt_pt_pt_dir₁, mk_pt_pt_pt_dir₂]
  have k₁ : ¬ qdr_cvx.angle₂.value.IsPos := by
    rw [g]
    exact AngValue.not_zero_isPos
  have k₂ : ¬ qdr_cvx.angle₂.value.IsNeg := by
    rw [g]
    exact AngValue.not_zero_isNeg
  have p: qdr_cvx.IsConvex := qdr_cvx.convex
  unfold Quadrilateral.IsConvex at p
  simp only [k₁, false_and, and_false, k₂, or_self] at p
  sorry

/-- Given a convex quadrilateral qdr_cvx, diagonal from the first point to the second point is not degenerate, i.e. the second point is not equal to the first point. -/
instance nd₂₄ : PtNe qdr_cvx.point₄ qdr_cvx.point₂ := (qdr_cvx.perm).nd₁₃

/-- The non-degenerate diagonal from the first point and third point of a convex quadrilateral -/
def diag_nd₁₃ : SegND P := SEG_nd qdr_cvx.point₁ qdr_cvx.point₃

/-- The non-degenerate diagonal from the second point and fourth point of a convex quadrilateral -/
def diag_nd₂₄ : SegND P := SEG_nd qdr_cvx.point₂ qdr_cvx.point₄

/-- Two diagonals are not parallel to each other -/
theorem diag_not_para : ¬ qdr_cvx.diag_nd₁₃ ∥ qdr_cvx.diag_nd₂₄ := by
  sorry
   -- have h: qdr_cvx.point₁ ≠ qdr_cvx.point₃ ∧ qdr_cvx.point₂ ≠ qdr_cvx.point₄ := ⟨qdr_cvx.nd₁₃.symm, qdr_cvx.nd₂₄.symm⟩
   -- have k: qdr_cvx.IsConvex := qdr_cvx.convex
   -- unfold QuadrilateralND.IsConvex at k
   -- simp only [ne_eq, h, not_false_eq_true, and_self, dite_true] at k
   -- by_contra q
   -- have r: qdr_cvx.diag_nd₂₄ ∥ qdr_cvx.diag_nd₁₃ := by exact q.symm
   -- rw [diag_nd₁₃, diag_nd₂₄] at r
   -- simp [r] at k

/-- The intersection point of two diagonals -/
@[pp_dot]
def diag_inx : P := Line.inx qdr_cvx.diag_nd₁₃.toLine qdr_cvx.diag_nd₂₄.toLine qdr_cvx.diag_not_para

/-- The interior of two diagonals intersect at one point, i.e. the intersection point of the underlying lines of the diagonals lies in the interior of both diagonals. -/
theorem diag_inx_lies_int : qdr_cvx.diag_inx LiesInt qdr_cvx.diag_nd₁₃ ∧ qdr_cvx.diag_inx LiesInt qdr_cvx.diag_nd₂₄ := by sorry
   -- have h: qdr_cvx.point₁ ≠ qdr_cvx.point₃ ∧ qdr_cvx.point₂ ≠ qdr_cvx.point₄ := ⟨qdr_cvx.nd₁₃.symm, qdr_cvx.nd₂₄.symm⟩
   -- have k: qdr_cvx.IsConvex := qdr_cvx.convex
   -- unfold QuadrilateralND.IsConvex at k
   -- simp only [ne_eq, h, not_false_eq_true, and_self, dite_true] at k
   -- have g: ¬ qdr_cvx.diag_nd₂₄ ∥ qdr_cvx.diag_nd₁₃ := Ne.symm qdr_cvx.diag_not_para
   -- rw [diag_nd₁₃, diag_nd₂₄] at g
   -- simp only [g, dite_true] at k
   -- exact k

/-- Given a convex quadrilateral qdr_cvx, its 1st, 2nd and 3rd points are not collinear, i.e. the projective direction of the vector $\overrightarrow{point₁ point₂}$ is not the same as the projective direction of the vector $\overrightarrow{point₁ point₃}$. -/
theorem not_collinear₁₂₃ : ¬ Collinear qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 2nd, 3rd and 4th points are not collinear, i.e. the projective direction of the vector $\overrightarrow{point₂ point₃}$ is not the same as the projective direction of the vector $\overrightarrow{point₂ point₄}$. -/
theorem not_collinear₂₃₄ : ¬ Collinear qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 3rd, 4th and 1st points are not collinear, i.e. the projective direction of the vector $\overrightarrow{point₃ point₄}$ is not the same as the projective direction of the vector $\overrightarrow{point₃ point₁}$. -/
theorem not_collinear₃₄₁ : ¬ Collinear qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 4th, 1st and 3rd points are not collinear, i.e. the projective direction of the vector $\overrightarrow{point₃ point₄}$ is not the same as the projective direction of the vector $\overrightarrow{point₃ point₁}$. -/
theorem not_collinear₄₁₃ : ¬ Collinear qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.point₃ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 4th, 3rd and 1st points are not collinear, i.e. the projective direction of the vector $\overrightarrow{point₃ point₄}$ is not the same as the projective direction of the vector $\overrightarrow{point₃ point₁}$. -/
theorem not_collinear₄₃₁ : ¬ Collinear qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 1st, 4th and 3rd points are not collinear, i.e. the projective direction of the vector $\overrightarrow{point₃ point₄}$ is not the same as the projective direction of the vector $\overrightarrow{point₃ point₁}$. -/
theorem not_collinear₁₄₃ : ¬ Collinear qdr_cvx.point₁ qdr_cvx.point₄ qdr_cvx.point₃ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 4th, 1st and 2nd points are not collinear, i.e. the projective direction of the vector $\overrightarrow{point₄ point₁}$ is not the same as the projective direction of the vector $\overrightarrow{point₄ point₂}$. -/
theorem not_collinear₄₁₂ : ¬ Collinear qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.point₂ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 2nd, 1st and 4th points are not collinear, i.e. the projective direction of the vector $\overrightarrow{point₄ point₁}$ is not the same as the projective direction of the vector $\overrightarrow{point₄ point₂}$. -/
theorem not_collinear₂₁₄ : ¬ Collinear qdr_cvx.point₂ qdr_cvx.point₁ qdr_cvx.point₄ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 1st, 4th and 2nd points are not collinear, i.e. the projective direction of the vector $\overrightarrow{point₄ point₁}$ is not the same as the projective direction of the vector $\overrightarrow{point₄ point₂}$. -/
theorem not_collinear₁₄₂ : ¬ Collinear qdr_cvx.point₁ qdr_cvx.point₄ qdr_cvx.point₂ := sorry

/-- Given a convex quadrilateral qdr_cvx, its 1st, 2nd and 4th points are not collinear, i.e. the projective direction of the vector $\overrightarrow{point₄ point₁}$ is not the same as the projective direction of the vector $\overrightarrow{point₄ point₂}$. -/
theorem not_collinear₁₂₄ : ¬ Collinear qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ := sorry

-- We need to add a bunch of such theorems as they may be useful in discussing general quadrilaterals, i.e. not convex, even as contradictory in proofs.


/--triangle point₄ point₁ point₂, which includes angle₁-/
@[pp_dot]
def triangle_nd₁ : TriangleND P := ⟨qdr_cvx.triangle₁,qdr_cvx.not_collinear₄₁₂⟩

/--triangle point₁ point₂ point₃, which includes angle₂-/
@[pp_dot]
def triangle_nd₂ : TriangleND P := ⟨qdr_cvx.triangle₂,qdr_cvx.not_collinear₁₂₃⟩

/--triangle point₂ point₃ point₄, which includes angle₃-/
@[pp_dot]
def triangle_nd₃ : TriangleND P := ⟨qdr_cvx.triangle₃,qdr_cvx.not_collinear₂₃₄⟩

/--triangle point₃ point₄ point₁, which includes angle₄-/
@[pp_dot]
def triangle_nd₄ : TriangleND P := ⟨qdr_cvx.triangle₄,qdr_cvx.not_collinear₃₄₁⟩

theorem cclock_eq : qdr_cvx.triangle_nd₁.is_cclock ↔ qdr_cvx.triangle_nd₃.is_cclock := sorry

theorem cclock_eq' : qdr_cvx.triangle_nd₂.is_cclock ↔ qdr_cvx.triangle_nd₄.is_cclock := sorry

end property_cvx

end Quadrilateral_cvx

section criteria
-- the criteria of a quadrilateral being convex `to be added`

variable {P : Type*} [EuclideanPlane P]

end criteria

end EuclidGeom
