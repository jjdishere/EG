import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral
import EuclideanGeometry.Foundation.Construction.Polygon.Trapezoid
import EuclideanGeometry.Foundation.Tactic.Congruence.Congruence
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel_trash

/-!

-/
noncomputable section
namespace EuclidGeom

-- `Add class parallelogram and state every theorem in structure`

/--

Recall certain definitions concerning quadrilaterals:

A QDR consists of four points; it is the generalized quadrilateral formed by these four points.

A QDR_nd is QDR that the points that adjacent is not same, namely $point_2 \neq point_1$, $point_3 \neq point_2$, $point_4 \neq point_3$, $point_1 \neq point_4$.

A QDR_cvx is QDR_nd that convex, current the definition is four angle has the same sign, namely $$(angle_1.IsPos \wedge angle_1.IsPos \wedge angle_1.IsPos \wedge angle_1.IsPos) \vee (angle_1.IsNeg \wedge angle_1.IsNeg \wedge angle_1.IsNeg \wedge angle_1.IsNeg)$$.

While we have great benifit using QDR_cvx as the basis of discussion of parallelogram_nd (as we will show later, all parallelogram_nds are quadrilateral_cvxs), we do have practical difficulty in proving a quadrilateral being convex. Also, it is important (but not essential, as we will see) to keep the definition of parallelogram and parallelogram_nd being the same form (we will use this 'standardised' method as a theorem later on). So we would like to switch our attention to another type of quadrilaterals: quadrilateral_nds, about which we can discuss angles, but general enough to include the degenerating cases.

In this section we define two types of parallelogram. 'parallel_nd' deals with those quadrilaterals we commomly call parallelogram (convex), and 'parallel' with more general cases (we permite degenerate cases). As the concept of convex is hard to deal with, we therefore won't use it to define directly. Instead, we will start with non_triv, where all sets of 3 points are not colinear.

-/

@[pp_dot]
structure Quadrilateral_nd.Parallelogram_non_triv {P : Type _} [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P) : Prop where
  not_colinear₁₂₃: ( ¬ colinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃)
  not_colinear₂₃₄: ( ¬ colinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄)
  not_colinear₃₄₁: ( ¬ colinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁)
  not_colinear₄₁₂: ( ¬ colinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂)

/-- A quadrilateral is called parallelogram if VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃.-/
@[pp_dot]
def Quadrilateral.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃

/-- A quadrilateral satisfies IsParallelogram_para if two sets of opposite sides are parallel respectively. -/
@[pp_dot]
def Quadrilateral_nd.IsParallelogram_para {P : Type _} [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P) : Prop := ( qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) ∧ (qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃)

/-- A quadrilateral satisfies IsParallelogram_nd if it satisfies both IsParallelogram_para and Parallelogram_non_triv. It is now what we commonly call parallelogram.-/
@[pp_dot]
def Quadrilateral_nd.IsParallelogram_nd {P : Type _} [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P) : Prop := qdr_nd.IsParallelogram_para ∧ qdr_nd.Parallelogram_non_triv

@[pp_dot]
def Quadrilateral.IsParallelogram_nd {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases h : qdr.IsND
  · exact (Quadrilateral_nd.mk_is_nd h).IsParallelogram_nd
  · exact False

scoped postfix : 50 "IsParallelogram_non_triv" => Quadrilateral_nd.Parallelogram_non_triv
scoped postfix : 50 "IsParallelogram" => Quadrilateral.IsParallelogram
scoped postfix : 50 "IsParallelogram_para" => Quadrilateral_nd.IsParallelogram_para
scoped postfix : 50 "IsParallelogram_nd" => Quadrilateral_nd.IsParallelogram_nd

/-- We define parallelogram as a structure.-/
@[ext]
structure Parallelogram (P : Type _) [EuclideanPlane P] extends Quadrilateral P where
  is_parallelogram : toQuadrilateral IsParallelogram

/-- We define parallelogram_nd as a structure.-/
@[ext]
structure Parallelogram_nd (P : Type _) [EuclideanPlane P] extends Quadrilateral_nd P, Parallelogram P where
  is_parallelogram_para : toQuadrilateral_nd IsParallelogram_para
  is_parallelogram_non_triv : toQuadrilateral_nd IsParallelogram_non_triv

/-- If qdr_nd is non-degenerate and is a parallelogram, and its 1st, 2nd and 3rd points are not colinear, then qdr_nd is a parallelogram_nd.-/
theorem Parallelogram_not_colinear₁₂₃ (P : Type _) [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P) (para: qdr_nd.1 IsParallelogram) (h: ¬ colinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃) : qdr_nd IsParallelogram_nd := by

   have hba : qdr_nd.1.2 ≠ qdr_nd.1.1 := by
     unfold colinear at h
     exact (ne_of_not_colinear h).2.2
   have hbc : qdr_nd.1.2 ≠ qdr_nd.1.3 :=by
     exact (ne_of_not_colinear h).1.symm
   have hca: qdr_nd.1.3 ≠ qdr_nd.1.1 :=by
     exact (ne_of_not_colinear h).2.1.symm

   have t : ¬ colinear qdr_nd.point₂ qdr_nd.point₁ qdr_nd.point₃ := by
     by_contra k
     simp [flip_colinear_fst_snd k] at h
   have x : ¬ colinear_of_nd hbc hba.symm := by
     unfold colinear at t
     simp [hbc,hba.symm,hca] at t
     simp [t]

   have s : ¬ qdr_nd.edge_nd₁₂.toProj = qdr_nd.edge_nd₂₃.toProj := by
     unfold colinear_of_nd at x
     sorry
   have v₁ : qdr_nd.edge_nd₁₂.toProj = qdr_nd.edge_nd₃₄.toProj := by sorry
   have v₂ : qdr_nd.edge_nd₂₃.toProj = qdr_nd.edge_nd₁₄.toProj := by sorry
   have s₁ : ¬ qdr_nd.edge_nd₁₂.toProj = qdr_nd.edge_nd₂₃.toProj := by sorry
   have s₂ : ¬ qdr_nd.edge_nd₂₃.toProj = qdr_nd.edge_nd₃₄.toProj := by sorry
   have s₃ : ¬ qdr_nd.edge_nd₃₄.toProj = qdr_nd.edge_nd₁₄.toProj := by sorry
   constructor
   sorry
   constructor
   sorry
   sorry
   sorry
   sorry

/-- If qdr_nd is non-degenerate and is a parallelogram, and its 2nd, 3rd and 4th points are not colinear, then qdr_nd is a parallelogram_nd.-/
theorem Parallelogram_not_colinear₂₃₄ (P : Type _) [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P) (para: qdr_nd.1 IsParallelogram) (h: ¬ colinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) : qdr_nd IsParallelogram_nd := by
  sorry

/-- If qdr_nd is non-degenerate and is a parallelogram, and its 3rd, 4th and 1st points are not colinear, then qdr_nd is a parallelogram_nd.-/
theorem Parallelogram_not_colinear₃₄₁ (P : Type _) [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P) (para: qdr_nd.1 IsParallelogram) (h: ¬ colinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁) : qdr_nd IsParallelogram_nd := by
  sorry

/-- If qdr_nd is non-degenerate and is a parallelogram, and its 4th, 1st and 2nd points are not colinear, then qdr_nd is a parallelogram_nd.-/
theorem Parallelogram_not_colinear₄₁₂ (P : Type _) [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P) (para: qdr_nd.1 IsParallelogram) (h: ¬ colinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂) : qdr_nd IsParallelogram_nd := by
  sorry

/-- Make a parallelogram with 4 points on a plane.-/
def Parallelogram.mk_pt_pt_pt_pt {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D) IsParallelogram) : Parallelogram P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h

/-- Make a parallelogram_nd with 4 points on a plane, and using condition non_colinear₁₂₃.-/
def Parallelogram_nd.mk_pt_pt_pt_pt₄ {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsParallelogram) (non_colinear₁₂₃: ¬ colinear A B C) : Parallelogram_nd P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h'
  nd := h
  is_parallelogram_para := sorry
  is_parallelogram_non_triv := sorry

/-- Make a parallelogram_nd with 4 points on a plane, and using condition non_colinear₂₃₄.-/
def Parallelogram_nd.mk_pt_pt_pt_pt₁ {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsParallelogram) (non_colinear₂₃₄: ¬ colinear B C D) : Parallelogram_nd P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h'
  nd := h
  is_parallelogram_para := sorry
  is_parallelogram_non_triv := sorry

/-- Make a parallelogram_nd with 4 points on a plane, and using condition non_colinear₃₄₁.-/
def Parallelogram_nd.mk_pt_pt_pt_pt₂ {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsParallelogram) (non_colinear₃₄₁: ¬ colinear C D A) : Parallelogram_nd P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h'
  nd := h
  is_parallelogram_para := sorry
  is_parallelogram_non_triv := sorry

/-- Make a parallelogram_nd with 4 points on a plane, and using condition non_colinear₄₁₂.-/
def Parallelogram_nd.mk_pt_pt_pt_pt₃ {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsParallelogram) (non_colinear₄₁₂: ¬ colinear D A B) : Parallelogram_nd P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h'
  nd := h
  is_parallelogram_para := sorry
  is_parallelogram_non_triv := sorry

/-- Make a parallelogram_nd with 4 points on a plane.-/
def Parallelogram_nd.mk_pt_pt_pt_pt {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsParallelogram) (non_colinear: (Quadrilateral_nd.mk_is_nd h) IsParallelogram_non_triv) : Parallelogram_nd P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h'
  nd := h
  is_parallelogram_para := sorry
  is_parallelogram_non_triv := non_colinear

scoped notation "PRG" => Parallelogram.mk_pt_pt_pt_pt
scoped notation "PRG_nd₁" => Parallelogram_nd.mk_pt_pt_pt_pt₁
scoped notation "PRG_nd₂" => Parallelogram_nd.mk_pt_pt_pt_pt₂
scoped notation "PRG_nd₃" => Parallelogram_nd.mk_pt_pt_pt_pt₃
scoped notation "PRG_nd₄" => Parallelogram_nd.mk_pt_pt_pt_pt₄
scoped notation "PRG_nd" => Parallelogram_nd.mk_pt_pt_pt_pt

/-- Make parallelogram with a quadrilateral.-/
def mk_parallelogram {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) : Parallelogram P where
  toQuadrilateral := qdr
  is_parallelogram := h

/-- Make parallelogram_nd with a quadrilateral, using condition non_colinear₁₂₃.-/
def mk_parallelogram_nd₄ {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h': qdr.IsND) (non_colinear₁₂₃: ¬ colinear qdr.1 qdr.2 qdr.3) : Parallelogram_nd P where
  toQuadrilateral := qdr
  is_parallelogram := h
  nd := h'
  is_parallelogram_para := sorry
  is_parallelogram_non_triv := sorry

/-- Make parallelogram_nd with a quadrilateral, using condition non_colinear₂₃₄.-/
def mk_parallelogram_nd₁ {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h': qdr.IsND) (non_colinear₂₃₄: ¬ colinear qdr.2 qdr.3 qdr.4) : Parallelogram_nd P where
  toQuadrilateral := qdr
  is_parallelogram := h
  nd := h'
  is_parallelogram_para := sorry
  is_parallelogram_non_triv := sorry

/-- Make parallelogram_nd with a quadrilateral, using condition non_colinear₃₁₄.-/
def mk_parallelogram_nd₂ {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h': qdr.IsND) (non_colinear₃₄₁: ¬ colinear qdr.3 qdr.4 qdr.1) : Parallelogram_nd P where
  toQuadrilateral := qdr
  is_parallelogram := h
  nd := h'
  is_parallelogram_para := sorry
  is_parallelogram_non_triv := sorry

/-- Make parallelogram_nd with a quadrilateral, using condition non_colinear₄₁₂.-/
def mk_parallelogram_nd₃ {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h': qdr.IsND) (non_colinear₄₁₂: ¬ colinear qdr.4 qdr.1 qdr.2) : Parallelogram_nd P where
  toQuadrilateral := qdr
  is_parallelogram := h
  nd := h'
  is_parallelogram_para := sorry
  is_parallelogram_non_triv := sorry

/-- Make parallelogram_nd with a quadrilateral.-/
def mk_parallelogram_nd {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h': qdr.IsND) (non_colinear: (Quadrilateral_nd.mk_is_nd h') IsParallelogram_non_triv) : Parallelogram_nd P where
  toQuadrilateral := qdr
  is_parallelogram := h
  nd := h'
  is_parallelogram_para := sorry
  is_parallelogram_non_triv := sorry

/-- Here is also a quite odd definition of a quadrilateral or parallelogram being parallelogram_nd, concerning angle being positive or negative. As it may be useful when discussing cclocks, it is reserved in form of the two theorems below.-/
theorem Quadrilateral.IsParallelogram_nd_redef {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) (h: qdr.IsND) (h': qdr IsParallelogram) (h': (((Quadrilateral_nd.mk_is_nd h).angle₁.value.IsPos ∧ (Quadrilateral_nd.mk_is_nd h).angle₃.value.IsPos) ∨ ((Quadrilateral_nd.mk_is_nd h).angle₁.value.IsNeg ∧ (Quadrilateral_nd.mk_is_nd h).angle₃.value.IsNeg) ∨ ((Quadrilateral_nd.mk_is_nd h).angle₂.value.IsPos ∧ (Quadrilateral_nd.mk_is_nd h).angle₄.value.IsPos) ∨ ((Quadrilateral_nd.mk_is_nd h).angle₂.value.IsNeg ∧ (Quadrilateral_nd.mk_is_nd h).angle₄.value.IsNeg))) : (Quadrilateral_nd.mk_is_nd h) IsParallelogram_nd := sorry

/--

One can notice that in this overall section we have already covered the route from parallelogram to parallelogram_nd. In this space here, we would like to introduce our plans for other routes and their status in the parallelogram system.

In Quadrilateral.lean we covered 3 types of common quadrilaterals: the most general qdr, more specific qdr_nd, and even better qdr_cvx. Bearing in mind that parallelogram_nds are in fact convex, we feel the need for repeating the discussion on convex quadrilaterals being parallelogram_nds (but not parallelograms, as this is pointless). This will make up the 1st part of the work below: convex quadrilaterals and parallelograms. And it will have two subsections: criteria and property. All other part shall follow in the same structure.

The route from qdr to parallelogram will not be seperated from the main discussion as there are no more to say other than the original definition. Also the route from qdr to parallelogram_nd, as this route either follows the former undiscussed route or the route from qdr to qdr_cvx, and that should be included in Quadrilateral.lean. So we are left with higher-class quadrilaterals qdr_nd, which can either be parallelogram (when colinear), or parallelogram_nd (as long as not all 4 points are colinear).

-/
@[pp_dot]
theorem Parallelogram.ParallelogramIs_nd_redef {P : Type _} [EuclideanPlane P] (qdr_para : Parallelogram P) (h': qdr_para.1.IsND) (k: ((Quadrilateral_nd.mk_is_nd h').angle₁.value.IsPos ∧ (Quadrilateral_nd.mk_is_nd h').angle₃.value.IsPos) ∨ ((Quadrilateral_nd.mk_is_nd h').angle₁.value.IsNeg ∧ (Quadrilateral_nd.mk_is_nd h').angle₃.value.IsNeg) ∨ ((Quadrilateral_nd.mk_is_nd h').angle₂.value.IsPos ∧ (Quadrilateral_nd.mk_is_nd h').angle₄.value.IsPos) ∨ ((Quadrilateral_nd.mk_is_nd h').angle₂.value.IsNeg ∧ (Quadrilateral_nd.mk_is_nd h').angle₄.value.IsNeg)) : (Quadrilateral_nd.mk_is_nd h') IsParallelogram_nd := sorry

variable {P : Type _} [EuclideanPlane P]

section criteria_prg_of_qdr_nd

variable {A B C D: P}
variable (nd : (QDR A B C D).IsND)
variable (cvx : (QDR A B C D).IsConvex)
variable {P : Type _} [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P)
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)

/-- Given Quadrilateral_nd qdr_nd, and qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄ and (qdr_nd.edge_nd₁₂).1.length = (qdr_nd.edge_nd₃₄).1.length, and qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃ and (qdr_nd.edge_nd₁₄).1.length = (qdr_nd.edge_nd₂₃).1.length, qdr_nd is a Parallelogram. -/
theorem qdr_nd_is_prg_of_para_eq_length_para_eq_length (h₁ : qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) (h₂ : qdr_nd.edge_nd₁₂.1.length = qdr_nd.edge_nd₃₄.1.length) (H₁ : qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃) (h₂ : qdr_nd.edge_nd₁₄.1.length = qdr_nd.edge_nd₂₃.1.length): qdr_nd.IsParallelogram := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AB ∥ CD and AB = CD, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_of_para_eq_length_para_eq_length_varient (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄)) (h₂ : (SEG A B).length = (SEG C D).length) (H₁ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃)) (H₂ : (SEG A D).length = (SEG B C).length): (Quadrilateral_nd.mk_is_nd nd).IsParallelogram := by
  sorry

/-- Given Quadrilateral_nd qdr_nd, and qdr_nd.diag₁₃.midpoint = qdr_nd.diag₂₄.midpoint, qdr_nd is a Parallelogram. -/
theorem qdr_nd_is_prg_nd_of_diag_inx_eq_mid_eq_mid (h' : (qdr_nd.diag₁₃).midpoint = (qdr_nd.diag₂₄).midpoint) : qdr_nd.IsParallelogram := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsND, and the midpoint of the diagonal AC and BD is the same, Quadrilateral ABCD is a Parallelogram. -/
theorem qdr_nd_is_prg_nd_of_diag_inx_eq_mid_eq_mid_variant (h' : (SEG A C).midpoint = (SEG B D).midpoint) : (Quadrilateral_nd.mk_is_nd nd).IsParallelogram := by
  sorry

end criteria_prg_of_qdr_nd

section criteria_prg_nd_of_qdr_cvx

variable {A B C D: P}
variable (nd : (QDR A B C D).IsND)
variable (cvx : (QDR A B C D).IsConvex)
variable {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P)
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)

/-- Given Quadrilateral_cvx qdr_cvx, qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄ and qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃, then qdr_cvx is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_para_para (h₁ : qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) (h₂ : qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃) : qdr_cvx.IsParallelogram_nd := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, AB ∥ CD and AD ∥ BC, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_para_para_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄)) (h₂ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃)) : (Quadrilateral_nd.mk_is_nd nd) IsParallelogram_nd := by
  sorry

/-- Given Quadrilateral_cvx qdr_cvx, and (qdr_cvx.edge_nd₁₂).1.length = (qdr_cvx.edge_nd₃₄).1.length and qdr_cvx.edge_nd₁₄.1.length = qdr_cvx.edge_nd₂₃.1.length, qdr_cvx is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_eq_length_eq_length (h₁ : (qdr_cvx.edge_nd₁₂).1.length = (qdr_cvx.edge_nd₃₄).1.length) (h₂ : qdr_cvx.edge_nd₁₄.1.length = qdr_cvx.edge_nd₂₃.1.length) : qdr_cvx.IsParallelogram_nd := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AB = CD and AD = BC, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_eq_length_eq_length_variant (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG A D).length = (SEG B C).length) : (Quadrilateral_nd.mk_is_nd nd) IsParallelogram_nd := by
  sorry

/-- Given Quadrilateral_cvx qdr_cvx, and qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄ and (qdr_cvx.edge_nd₁₂).1.length = (qdr_cvx.edge_nd₃₄).1.length, qdr_cvx is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_para_eq_length (h₁ : qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) (h₂ : qdr_cvx.edge_nd₁₂.1.length = qdr_cvx.edge_nd₃₄.1.length) : qdr_cvx.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AB ∥ CD and AB = CD, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_para_eq_length_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄)) (h₂ : (SEG A B).length = (SEG C D).length) : (Quadrilateral_nd.mk_is_nd nd) IsParallelogram_nd := by
  sorry

/-- Given Quadrilateral_cvx qdr_cvx, and qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃ and (qdr_cvx.edge_nd₁₄).1.length = (qdr_cvx.edge_nd₂₃).1.length, qdr_cvx is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_para_eq_length' (h₁ : qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃) (h₂ : qdr_cvx.edge_nd₁₄.1.length = qdr_cvx.edge_nd₂₃.1.length) : qdr_cvx.IsParallelogram_nd := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AD ∥ BC and AD = BC, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_para_eq_length'_variant (h₁ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃)) (h₂ : (SEG A D).length = (SEG B C).length) : (Quadrilateral_nd.mk_is_nd nd) IsParallelogram_nd := by
  sorry

/-- Given Quadrilateral_cvx qdr_cvx, and angle₁ = angle₃ and angle₂ = angle₄, qdr_cvx is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_eq_angle_value_eq_angle_value (h₁ : qdr_cvx.angle₁ = qdr_cvx.angle₃) (h₂ : qdr_cvx.angle₂ = qdr_cvx.angle₄) : qdr_cvx.IsParallelogram_nd := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and ∠DAB = ∠BCD and ∠ABC = ∠CDA, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_of_eq_angle_value_eq_angle_value_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄ (QDR_nd A B C D nd).nd₁₂) = (ANG B C D (QDR_nd A B C D nd).nd₂₃.symm (QDR_nd A B C D nd).nd₃₄)) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.symm (QDR_nd A B C D nd).nd₂₃) = (ANG C D A (QDR_nd A B C D nd).nd₃₄.symm (QDR_nd A B C D nd).nd₁₄.symm)) : (Quadrilateral_nd.mk_is_nd nd) IsParallelogram_nd := by
  sorry

/-- Given Quadrilateral_cvx qdr_cvx, and qdr_cvx.diag_nd₁₃.1.midpoint = qdr_cvx.diag_nd₂₄.1.midpoint, qdr_cvx is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_diag_inx_eq_mid_eq_mid (h' : qdr_cvx.diag_nd₁₃.1.midpoint = qdr_cvx.diag_nd₂₄.1.midpoint) : qdr_cvx.IsParallelogram_nd := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and the midpoint of the diagonal AC and BD is the same, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_of_diag_inx_eq_mid_eq_mid_variant (h' : (SEG A C).midpoint = (SEG B D).midpoint) : (Quadrilateral_nd.mk_is_nd nd) IsParallelogram_nd := by
  sorry

end criteria_prg_nd_of_qdr_cvx

section property
variable {A B C D : P}
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)

/-- Given Quadrilateral qdr IsPRG_nd, Quadrilateral qdr IsConvex. -/
theorem is_convex_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.IsConvex := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, Quadrilateral ABCD IsConvex. -/
theorem is_convex_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : (QDR A B C D) IsConvex := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₃ ≠ qdr.point₁. -/
theorem nd₁₃_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₃ ≠ qdr.point₁ := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, C ≠ A. -/
theorem nd₁₃_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : C ≠ A := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₄ ≠ qdr.point₂. -/
theorem nd₂₄_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₄ ≠ qdr.point₂ := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, D ≠ B. -/
theorem nd₂₄_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : D ≠ B := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₂ ≠ qdr.point₁. -/
theorem nd₁₂_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₂ ≠ qdr.point₁ := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, B ≠ A. -/
theorem nd₁₂_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : B ≠ A := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₃ ≠ qdr.point₂. -/
theorem nd₂₃_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₃ ≠ qdr.point₂ := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, C ≠ B. -/
theorem nd₂₃_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : C ≠ B := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₄ ≠ qdr.point₃. -/
theorem nd₃₄_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₄ ≠ qdr.point₃ := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, D ≠ C. -/
theorem nd₃₄_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : D ≠ C := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₄ ≠ qdr.point₁. -/
theorem nd₁₄_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₄ ≠ qdr.point₁ := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, D ≠ A. -/
theorem nd₁₄_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : D ≠ A := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are parallel namely (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_abstract qdr h)) ∥ (SEG_nd qdr.point₃ qdr.point₄ (nd₃₄_of_is_prg_abstract qdr h)). -/
theorem para_of_is_prg_nd (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_nd qdr h)) ∥ (SEG_nd qdr.point₃ qdr.point₄ (nd₃₄_of_is_prg_nd qdr h)):= by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are parallel namely AB ∥ CD. -/
theorem para_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ (SEG_nd C D (nd₃₄_of_is_prg_nd_variant h)) := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are parallel namely (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_abstract qdr h)) ∥ (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_abstract qdr h)). -/
theorem para_of_is_prg_nd' (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_nd qdr h)) ∥ (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_nd qdr h)):= by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are parallel namely AD ∥ BC. -/
theorem para_of_is_prg_nd'_variant (h : (QDR A B C D).IsParallelogram_nd) : (SEG_nd A D (nd₁₄_of_is_prg_nd_variant h)) ∥ SEG_nd B C (nd₂₃_of_is_prg_nd_variant h) := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are equal namely (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_abstract qdr h)).1.length = (SEG_nd qdr.point₃ qdr.point₄ (nd₁₂_of_is_prg_abstract qdr h)).1.length. -/
theorem eq_length_of_is_prg_nd (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_nd qdr h)).1.length = (SEG_nd qdr.point₃ qdr.point₄ (nd₃₄_of_is_prg_nd qdr h)).1.length := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are equal namely (SEG A B).length = (SEG C D).length. -/
theorem eq_length_of_is_prg_nd_variant  (h : (QDR A B C D).IsParallelogram_nd) : (SEG A B).length = (SEG C D).length := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are equal namely (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_abstract qdr h)).1.length = (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_abstract qdr h)).1.length. -/
theorem eq_length_of_is_prg_nd'  (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_nd qdr h)).1.length = (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_nd qdr h)).1.length := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are equal namely (SEG A D).length = (SEG B C).length. -/
theorem eq_length_of_is_prg_nd'_variant  (h : (QDR A B C D).IsParallelogram_nd) : (SEG A D).length = (SEG B C).length := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the opposite angles are equal namely ANG qdr.point₁ qdr.point₂ qdr.point₃ = ANG qdr.point₃ qdr.point₄ qdr.point₁. -/
theorem eq_angle_value_of_is_prg_nd (h : qdr.IsParallelogram_nd) : ANG qdr.point₁ qdr.point₂ qdr.point₃ ((nd₁₂_of_is_prg_nd qdr h).symm) (nd₂₃_of_is_prg_nd qdr h) = ANG qdr.point₃ qdr.point₄ qdr.point₁ ((nd₃₄_of_is_prg_nd qdr h).symm) ((nd₁₄_of_is_prg_nd qdr h).symm) := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite angles are equal namely ANG A B C = ANG C D A. -/
theorem eq_angle_value_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : ANG A B C ((nd₁₂_of_is_prg_nd_variant h).symm) (nd₂₃_of_is_prg_nd_variant h) = ANG C D A ((nd₃₄_of_is_prg_nd_variant h).symm) ((nd₁₄_of_is_prg_nd_variant h).symm) := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the opposite angles are equal namely ANG qdr.point₄ qdr.point₁ qdr.point₂ = ANG qdr.point₂ qdr.point₃ qdr.point₄. -/
theorem eq_angle_value_of_is_prg_nd' (h : qdr.IsParallelogram_nd) : ANG qdr.point₄ qdr.point₁ qdr.point₂ ((nd₁₄_of_is_prg_nd qdr h)) ((nd₁₂_of_is_prg_nd qdr h)) = ANG qdr.point₂ qdr.point₃ qdr.point₄ ((nd₂₃_of_is_prg_nd qdr h).symm) (nd₃₄_of_is_prg_nd qdr h):= by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite angles are equal namely ANG D A B = ANG B C D. -/
theorem eq_angle_value_of_is_prg_nd'_variant (h : (QDR A B C D).IsParallelogram_nd) : ANG D A B (nd₁₄_of_is_prg_nd_variant h) (nd₁₂_of_is_prg_nd_variant h) = ANG B C D ((nd₂₃_of_is_prg_nd_variant h).symm) (nd₃₄_of_is_prg_nd_variant h) := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ = (SEG qdr.point₁ qdr.point₃).midpoint.
theorem eq_midpt_of_diag_inx_of_is_prg_nd (h : qdr.IsParallelogram_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ (is_convex_of_is_prg_nd qdr h)) = (SEG qdr.point₁ qdr.point₃).midpoint :=
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx A B C D = (SEG A C).midpoint. -/
theorem eq_midpt_of_diag_inx_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg_nd_variant h)) = (SEG A C).midpoint :=
  have h : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ SEG_nd C D (nd₃₄_of_is_prg_nd_variant h) := para_of_is_prg_nd_variant h
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ = (SEG qdr.point₂ qdr.point₄).midpoint. -/
theorem eq_midpt_of_diag_inx_of_is_prg_nd' (h : qdr.IsParallelogram_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ (is_convex_of_is_prg_nd qdr h)) = (SEG qdr.point₂ qdr.point₄).midpoint :=
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx A B C D = (SEG B D).midpoint. -/
theorem eq_midpt_of_diag_inx_of_is_prg_nd'_variant (h : (QDR A B C D).IsParallelogram_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg_nd_variant h)) = (SEG B D).midpoint :=
  have h : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ SEG_nd C D (nd₃₄_of_is_prg_nd_variant h) := para_of_is_prg_nd_variant h
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the midpoints of the diagonals are the same. -/-/
theorem eq_midpt_of_diag_of_is_prg (h : qdr.IsParallelogram_nd) : (SEG qdr.point₁ qdr.point₃).midpoint = (SEG qdr.point₂ qdr.point₄).midpoint := by
  sorry

/-- Given four points A B C D and Quadrilateral ABCD IsPRG_nd, the midpoints of the diagonals are the same. -/
theorem eq_midpt_of_diag_of_is_prg_variant (h : (QDR A B C D).IsParallelogram_nd) : (SEG A C).midpoint = (SEG B D).midpoint := eq_midpt_of_diag_of_is_prg (QDR A B C D) h

/-- Given Quadrilateral qdr IsPRG_nd, then Quadrilateral IsPRG. -/
theorem prg_nd_is_prg (h : qdr.IsParallelogram_nd) : qdr.IsParallelogram := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, then Quadrilateral ABCD IsPRG. -/
theorem prg_nd_is_prg_variant (h : (QDR A B C D).IsParallelogram_nd) : (QDR A B C D).IsParallelogram := prg_nd_is_prg (QDR A B C D) h

/-- Given Quadrilateral qdr IsPRG_nd, then VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃. -/
theorem eq_vec_of_is_prg_nd (h : qdr.IsParallelogram_nd) : VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃ := prg_nd_is_prg qdr h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, then VEC A B = VEC D C. -/
theorem eq_vec_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : VEC A B = VEC D C := eq_vec_of_is_prg_nd (QDR A B C D) h

/-- Given Quadrilateral qdr IsPRG_nd, then VEC qdr.point₁ qdr.point₄ = VEC qdr.point₂ qdr.point₃. -/
theorem eq_vec_of_is_prg_nd' (h : qdr.IsParallelogram_nd) : VEC qdr.point₁ qdr.point₄ = VEC qdr.point₂ qdr.point₃ := by
  rw [← vec_add_vec qdr.point₁ qdr.point₂ qdr.point₄]
  rw [← vec_add_vec qdr.point₂ qdr.point₄ qdr.point₃]
  rw [eq_vec_of_is_prg_nd qdr h]
  exact add_comm (VEC qdr.point₄ qdr.point₃) (VEC qdr.point₂ qdr.point₄)

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, then VEC A D = VEC B C. -/
theorem eq_vec_of_is_prg_nd'_variant (h : (QDR A B C D).IsParallelogram_nd) : VEC A D = VEC B C := eq_vec_of_is_prg_nd' (QDR A B C D) h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the sum of the squares of each side equals to the sum of the squares of the diagonals namely 2 * (SEG qdr.point₁ qdr.point₂).length ^ 2 + 2 * (SEG qdr.point₂ qdr.point₃).length ^ 2 = (SEG qdr.point₁ qdr.point₃).length ^ 2 + (SEG qdr.point₂ qdr.point₄).length ^ 2. -/
theorem parallelogram_law (h : qdr.IsParallelogram) : 2 * (SEG qdr.point₁ qdr.point₂).length ^ 2 + 2 * (SEG qdr.point₂ qdr.point₃).length ^ 2 = (SEG qdr.point₁ qdr.point₃).length ^ 2 + (SEG qdr.point₂ qdr.point₄).length ^ 2 := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the sum of the squares of each side equals to the sum of the squares of the diagonals namely 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2. -/
theorem parallelogram_law_variant (h : (QDR A B C D).IsParallelogram) : 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2 := parallelogram_law (QDR A B C D) h

end property

section property_nd
variable {A B C D : P}
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)
variable {P : Type _} [EuclideanPlane P] (prg_nd : Parallelogram_nd P)

/-- Given Quadrilateral qdr IsPRG_nd, Quadrilateral qdr IsND. -/

theorem nd_is_nd_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.IsND := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, Quadrilateral ABCD IsND. -/
theorem nd_is_nd_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : (QDR A B C D).IsND := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, Quadrilateral qdr IsND.-/
theorem nd_is_nd_of_is_prg_nd_restated (h : qdr.IsParallelogram_nd) : (QDR qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄).IsND := nd_is_nd_of_is_prg_nd_variant h

theorem nd_is_nd_of_is_prg_nd_restated_variant (h : (QDR A B C D).IsParallelogram_nd) : (QDR A B C D).IsND := nd_is_nd_of_is_prg_nd_variant h

/-- Given Quadrilateral qdr IsPRG_nd, qdr IsConvex. -/
theorem nd_is_convex_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.IsConvex := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, Quadrilateral ABCD IsConvex. -/
theorem nd_is_convex_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : (QDR A B C D) IsConvex := is_convex_of_is_prg_nd_variant h

/-- Given Quadrilateral qdr IsPRG_nd, qdr IsConvex. -/
theorem nd_is_convex_of_is_prg_nd_restated (h : qdr.IsParallelogram_nd) : (Quadrilateral_nd.mk_is_nd (nd_is_nd_of_is_prg_nd_restated qdr h)) IsConvex := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, Quadrilateral ABCD IsConvex. -/
theorem nd_is_convex_of_is_prg_nd_restated_variant (h : (QDR A B C D).IsParallelogram_nd) : (Quadrilateral_nd.mk_is_nd (nd_is_nd_of_is_prg_nd_restated (QDR A B C D) h)) IsConvex := nd_is_convex_of_is_prg_nd_restated (QDR A B C D) h

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₃ ≠ qdr.point₁. -/
theorem nd_nd₁₃_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₃ ≠ qdr.point₁ := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, C ≠ A. -/
theorem nd_nd₁₃_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : C ≠ A := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₄ ≠ qdr.point₂. -/
theorem nd_nd₂₄_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₄ ≠ qdr.point₂ := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, D ≠ B. -/
theorem nd_nd₂₄_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : D ≠ B := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₂ ≠ qdr.point₁. -/
theorem nd_nd₁₂_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₂ ≠ qdr.point₁ := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, B ≠ A. -/
theorem nd_nd₁₂_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : B ≠ A := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₃ ≠ qdr.point₂. -/
theorem nd_nd₂₃_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₃ ≠ qdr.point₂ := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, C ≠ B. -/
theorem nd_nd₂₃_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : C ≠ B := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₄ ≠ qdr.point₃. -/
theorem nd_nd₃₄_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₄ ≠ qdr.point₃ := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, D ≠ C. -/
theorem nd_nd₃₄_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : D ≠ C := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₄ ≠ qdr.point₁. -/
theorem nd_nd₁₄_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₄ ≠ qdr.point₁ := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, D ≠ A. -/
theorem nd_nd₁₄_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : D ≠ A := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are parallel namely (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_abstract qdr h)) ∥ (SEG_nd qdr.point₃ qdr.point₄ (nd₃₄_of_is_prg_abstract qdr h)). -/
theorem nd_para_of_is_prg_nd (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_nd qdr h)) ∥ (SEG_nd qdr.point₃ qdr.point₄ (nd₃₄_of_is_prg_nd qdr h)):= by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are parallel namely AB ∥ CD. -/
theorem nd_para_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ (SEG_nd C D (nd₃₄_of_is_prg_nd_variant h)) := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are parallel namely (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_abstract qdr h)) ∥ (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_abstract qdr h)). -/
theorem nd_para_of_is_prg_nd' (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_nd qdr h)) ∥ (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_nd qdr h)):= by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are parallel namely AD ∥ BC. -/
theorem nd_para_of_is_prg_nd'_variant (h : (QDR A B C D).IsParallelogram_nd) : (SEG_nd A D (nd₁₄_of_is_prg_nd_variant h)) ∥ SEG_nd B C (nd₂₃_of_is_prg_nd_variant h) := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are equal namely (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_abstract qdr h)).1.length = (SEG_nd qdr.point₃ qdr.point₄ (nd₁₂_of_is_prg_abstract qdr h)).1.length. -/
theorem nd_eq_length_of_is_prg_nd (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_nd qdr h)).1.length = (SEG_nd qdr.point₃ qdr.point₄ (nd₃₄_of_is_prg_nd qdr h)).1.length := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are equal namely (SEG A B).length = (SEG C D).length. -/
theorem nd_eq_length_of_is_prg_nd_variant  (h : (QDR A B C D).IsParallelogram_nd) : (SEG A B).length = (SEG C D).length := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are equal namely (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_abstract qdr h)).1.length = (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_abstract qdr h)).1.length. -/
theorem nd_eq_length_of_is_prg_nd'  (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_nd qdr h)).1.length = (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_nd qdr h)).1.length := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are equal namely (SEG A D).length = (SEG B C).length. -/
theorem nd_eq_length_of_is_prg_nd'_variant  (h : (QDR A B C D).IsParallelogram_nd) : (SEG A D).length = (SEG B C).length := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the opposite angles are equal namely ANG qdr.point₁ qdr.point₂ qdr.point₃ = ANG qdr.point₃ qdr.point₄ qdr.point₁. -/
theorem nd_eq_angle_value_of_is_prg_nd (h : qdr.IsParallelogram_nd) : (ANG qdr.point₁ qdr.point₂ qdr.point₃ ((nd₁₂_of_is_prg_nd qdr h).symm) (nd₂₃_of_is_prg_nd qdr h)).value = (ANG qdr.point₃ qdr.point₄ qdr.point₁ ((nd₃₄_of_is_prg_nd qdr h).symm) ((nd₁₄_of_is_prg_nd qdr h).symm)).value := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite angles are equal namely ANG A B C = ANG C D A. -/
theorem nd_eq_angle_value_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : (ANG A B C ((nd₁₂_of_is_prg_nd_variant h).symm) (nd₂₃_of_is_prg_nd_variant h)).value = (ANG C D A ((nd₃₄_of_is_prg_nd_variant h).symm) ((nd₁₄_of_is_prg_nd_variant h).symm)).value := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the opposite angles are equal namely ANG qdr.point₄ qdr.point₁ qdr.point₂ = ANG qdr.point₂ qdr.point₃ qdr.point₄. -/
theorem nd_eq_angle_value_of_is_prg_nd' (h : qdr.IsParallelogram_nd) : (ANG qdr.point₄ qdr.point₁ qdr.point₂ ((nd₁₄_of_is_prg_nd qdr h)) ((nd₁₂_of_is_prg_nd qdr h))).value = (ANG qdr.point₂ qdr.point₃ qdr.point₄ ((nd₂₃_of_is_prg_nd qdr h).symm) (nd₃₄_of_is_prg_nd qdr h)).value:= by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite angles are equal namely ANG D A B = ANG B C D. -/
theorem nd_eq_angle_value_of_is_prg_nd'_variant (h : (QDR A B C D).IsParallelogram_nd) : (ANG D A B (nd₁₄_of_is_prg_nd_variant h) (nd₁₂_of_is_prg_nd_variant h)).value = (ANG B C D ((nd₂₃_of_is_prg_nd_variant h).symm) (nd₃₄_of_is_prg_nd_variant h)).value := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ = (SEG qdr.point₁ qdr.point₃).midpoint.-/
theorem nd_eq_midpt_of_diag_inx_of_is_prg_nd (h : qdr.IsParallelogram_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ (nd_is_nd_of_is_prg_nd_restated qdr h) (nd_is_convex_of_is_prg_nd_restated qdr h)) = (SEG qdr.point₁ qdr.point₃).midpoint :=
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx A B C D = (SEG A C).midpoint. -/
theorem nd_eq_midpt_of_diag_inx_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (nd_is_nd_of_is_prg_nd_restated (QDR A B C D) h) (nd_is_convex_of_is_prg_nd_restated (QDR A B C D) h)) = (SEG A C).midpoint :=
  have h : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ SEG_nd C D (nd₃₄_of_is_prg_nd_variant h) := para_of_is_prg_nd_variant h
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ = (SEG qdr.point₂ qdr.point₄).midpoint. -/
theorem nd_eq_midpt_of_diag_inx_of_is_prg_nd' (h : qdr.IsParallelogram_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ (nd_is_nd_of_is_prg_nd_restated qdr h) (nd_is_convex_of_is_prg_nd_restated qdr h)) = (SEG qdr.point₂ qdr.point₄).midpoint :=
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx A B C D = (SEG B D).midpoint. -/
theorem nd_eq_midpt_of_diag_inx_of_is_prg_nd'_variant (h : (QDR A B C D).IsParallelogram_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (nd_is_nd_of_is_prg_nd_restated (QDR A B C D) h) (nd_is_convex_of_is_prg_nd_restated (QDR A B C D) h)) = (SEG B D).midpoint :=
  have h : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ SEG_nd C D (nd₃₄_of_is_prg_nd_variant h) := para_of_is_prg_nd_variant h
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the midpoints of the diagonals are the same. -/
theorem nd_eq_midpt_of_diag_of_is_prg (h : qdr.IsParallelogram_nd) : (SEG qdr.point₁ qdr.point₃).midpoint = (SEG qdr.point₂ qdr.point₄).midpoint := by
  sorry

/-- Given four points A B C D and Quadrilateral ABCD IsPRG_nd, the midpoints of the diagonals are the same. -/
theorem nd_eq_midpt_of_diag_of_is_prg_variant (h : (QDR A B C D).IsParallelogram_nd) : (SEG A C).midpoint = (SEG B D).midpoint := eq_midpt_of_diag_of_is_prg (QDR A B C D) h

/-- Given Quadrilateral qdr IsPRG_nd, then Quadrilateral IsPRG. -/
theorem nd_prg_nd_is_prg (h : qdr.IsParallelogram_nd) : qdr.IsParallelogram := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, then Quadrilateral ABCD IsPRG. -/
theorem nd_prg_nd_is_prg_variant (h : (QDR A B C D).IsParallelogram_nd) : (QDR A B C D).IsParallelogram := prg_nd_is_prg (QDR A B C D) h

/-- Given Quadrilateral qdr IsPRG_nd, then VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃. -/
theorem nd_eq_vec_of_is_prg_nd (h : qdr.IsParallelogram_nd) : VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃ := prg_nd_is_prg qdr h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, then VEC A B = VEC D C. -/
theorem nd_eq_vec_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : VEC A B = VEC D C := eq_vec_of_is_prg_nd (QDR A B C D) h

/-- Given Quadrilateral qdr IsPRG_nd, then VEC qdr.point₁ qdr.point₄ = VEC qdr.point₂ qdr.point₃. -/
theorem nd_eq_vec_of_is_prg_nd' (h : qdr.IsParallelogram_nd) : VEC qdr.point₁ qdr.point₄ = VEC qdr.point₂ qdr.point₃ := by
  rw [← vec_add_vec qdr.point₁ qdr.point₂ qdr.point₄]
  rw [← vec_add_vec qdr.point₂ qdr.point₄ qdr.point₃]
  rw [eq_vec_of_is_prg_nd qdr h]
  exact add_comm (VEC qdr.point₄ qdr.point₃) (VEC qdr.point₂ qdr.point₄)

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, then VEC A D = VEC B C. -/
theorem nd_eq_vec_of_is_prg_nd'_variant (h : (QDR A B C D).IsParallelogram_nd) : VEC A D = VEC B C := eq_vec_of_is_prg_nd' (QDR A B C D) h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the sum of the squares of each side equals to the sum of the squares of the diagonals namely 2 * (SEG qdr.point₁ qdr.point₂).length ^ 2 + 2 * (SEG qdr.point₂ qdr.point₃).length ^ 2 = (SEG qdr.point₁ qdr.point₃).length ^ 2 + (SEG qdr.point₂ qdr.point₄).length ^ 2. -/
theorem nd_parallelogram_law (h : qdr.IsParallelogram_nd) : 2 * (SEG qdr.point₁ qdr.point₂).length ^ 2 + 2 * (SEG qdr.point₂ qdr.point₃).length ^ 2 = (SEG qdr.point₁ qdr.point₃).length ^ 2 + (SEG qdr.point₂ qdr.point₄).length ^ 2 := by
  repeat rw [Seg.length]
  repeat rw [seg_tovec_eq_vec]
  rw [(vec_add_vec qdr.point₁ qdr.point₂ qdr.point₃).symm]
  rw [(vec_add_vec qdr.point₂ qdr.point₃ qdr.point₄).symm]
  rw [← neg_vec qdr.point₄ qdr.point₃]
  rw [← eq_vec_of_is_prg_nd qdr h]
  rw [← sub_eq_add_neg (VEC qdr.point₂ qdr.point₃) (VEC qdr.point₁ qdr.point₂)]
  rw [add_comm (VEC qdr.point₁ qdr.point₂) (VEC qdr.point₂ qdr.point₃)]
  repeat rw [sq]
  rw [(parallelogram_law_with_norm ℝ (VEC qdr.point₂ qdr.point₃) (VEC qdr.point₁ qdr.point₂))]
  ring

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the sum of the squares of each side equals to the sum of the squares of the diagonals namely 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2. -/
theorem nd_parallelogram_law_variant (h : (QDR A B C D).IsParallelogram_nd) : 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2 := nd_parallelogram_law (QDR A B C D) h

end property_nd

end EuclidGeom
