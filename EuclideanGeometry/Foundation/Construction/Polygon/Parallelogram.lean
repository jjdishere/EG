import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral
import EuclideanGeometry.Foundation.Construction.Polygon.Trapezoid
import EuclideanGeometry.Foundation.Tactic.Congruence.Congruence
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel_trash

noncomputable section
namespace EuclidGeom

-- `Add class parallelogram and state every theorem in structure`

/-

Recall certain definitions concerning quadrilaterals:

A QDR consists of four points; it is the generalized quadrilateral formed by these four points.

A QDR_nd is QDR that the points that adjacent is not same, namely $point_2 ≠ point_1$, $point_3 ≠ point_2$, $point_4 ≠ point_3$, $point_1 ≠ point_4$.

A QDR_cvx is QDR_nd that convex, current the definition is four angle has the same sign, namely $$(angle_1.IsPos \wedge angle_1.IsPos \wedge angle_1.IsPos \wedge angle_1.IsPos) \vee (angle_1.IsNeg \wedge angle_1.IsNeg \wedge angle_1.IsNeg \wedge angle_1.IsNeg)$$.

While we have great benifit using QDR_cvx as the basis of discussion of parallelogram_nd (as we will show later, all parallelogram_nds are quadrilateral_cvxs), we do have practical difficulty in proving a quadrilateral being convex. Also, it is important (but not essential, as we will see) to keep the definition of parallelogram and parallelogram_nd being the same form (we will use this 'standardised' method as a theorem later on). So we would like to switch our attention to another type of quadrilaterals: quadrilateral_nds, about which we can discuss angles, but general enough to include the degenerating cases.

But we still find difficulties in organizing proofs, so we still use quadrilateral_cvx to define parallelogram_nd and finally we will prove some equivalent definitions.

In this section we define two types of parallelogram. 'parallel_nd' deals with those quadrilaterals we commomly call parallelogram (convex), and 'parallel' with more general cases (we permite degenerate cases). As the concept of convex is hard to deal with, we therefore won't use it to define directly. Instead, we will start with non_triv, where all sets of 3 points are not colinear.

-/

/-- A quadrilateral satisfies Parallelogram_non_triv if every 3 vertexes are not colinear. -/
@[pp_dot]
structure Quadrilateral.Parallelogram_non_triv {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop where
  not_colinear₁₂₃: ( ¬ colinear qdr.point₁ qdr.point₂ qdr.point₃)
  not_colinear₂₃₄: ( ¬ colinear qdr.point₂ qdr.point₃ qdr.point₄)
  not_colinear₃₄₁: ( ¬ colinear qdr.point₃ qdr.point₄ qdr.point₁)
  not_colinear₄₁₂: ( ¬ colinear qdr.point₄ qdr.point₁ qdr.point₂)

scoped postfix : 50 "IsParallelogram_non_triv" => Quadrilateral.Parallelogram_non_triv

/-- A quadrilateral_nd satisfies IsParallelogram_para if two sets of opposite sides are parallel respectively. -/
@[pp_dot]
def Quadrilateral_nd.IsParallelogram_para {P : Type _} [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P) : Prop := ( qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) ∧ (qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃)

scoped postfix : 50 "IsParallelogram_para" => Quadrilateral_nd.IsParallelogram_para

/-- A quadrilateral satisfies IsParallelogram_para if it is a quadrilateral_nd and satisfies IsParallelogram_para as a quadrilateral_nd. -/
@[pp_dot]
def Quadrilateral.IsParallelogram_para {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases h : qdr.IsND
  · exact (Quadrilateral_nd.mk_is_nd h).IsParallelogram_para
  · exact False

-- `do we really need this?`
-- scoped postfix : 50 "IsParallelogram_para_gen" => Quadrilateral.IsParallelogram_para

/-- A quadrilateral is called parallelogram if VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃.-/
@[pp_dot]
def Quadrilateral.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃

scoped postfix : 50 "IsParallelogram" => Quadrilateral.IsParallelogram

/-- A quadrilateral_nd is called parallelogram if VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃.-/
@[pp_dot]
def Quadrilateral_nd.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P) : Prop := VEC qdr_nd.point₁ qdr_nd.point₂ = VEC qdr_nd.point₄ qdr_nd.point₃

scoped postfix : 50 "nd_IsParallelogram" => Quadrilateral_nd.IsParallelogram

/-- We define parallelogram as a structure. -/
@[ext]
structure Parallelogram (P : Type _) [EuclideanPlane P] extends Quadrilateral P where
  is_parallelogram : toQuadrilateral IsParallelogram

/-- Make a parallelogram with 4 points on a plane, and using condition IsParallelogram. -/
def Parallelogram.mk_pt_pt_pt_pt {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D) IsParallelogram) : Parallelogram P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h

scoped notation "PRG" => Parallelogram.mk_pt_pt_pt_pt

/-- Make a parallelogram with a quadrilateral, and using condition IsParallelogram. -/
def mk_parallelogram {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) : Parallelogram P where
  toQuadrilateral := qdr
  is_parallelogram := h

/-- A parallelogram which satisfies Prallelogram_non_triv satisfies IsParallelogram_para. -/
theorem is_parallelogram_para_of_parallelogram_non_triv {P : Type _} [EuclideanPlane P] (prg : Parallelogram P) (non_triv: prg.Parallelogram_non_triv): prg.IsParallelogram_para:= by
  sorry

/-- A parallelogram which satisfies Prallelogram_non_triv is convex. -/
theorem is_convex_of_parallelogram_non_triv {P : Type _} [EuclideanPlane P] (prg : Parallelogram P) (non_triv: prg.Parallelogram_non_triv): prg.IsConvex:= by sorry

/-- We define parallelogram_nd as a structure. -/
@[ext]
structure ParallelogramND (P : Type _) [EuclideanPlane P] extends Quadrilateral_cvx P, Parallelogram P

@[pp_dot]
def Quadrilateral.IsParallelogramND {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := qdr IsConvex ∧ qdr IsParallelogram

scoped postfix : 50 "IsParallelogramND" => Quadrilateral.IsParallelogramND

@[pp_dot]
def Quadrilateral_nd.IsParallelogramND {P : Type _} [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P) : Prop := Quadrilateral.IsParallelogramND qdr_nd.toQuadrilateral

-- scoped postfix : 50 "nd_IsParallelogramND" => Quadrilateral_nd.IsParallelogramND

theorem parallelogram_non_triv_of_parallelogramND {P : Type _} [EuclideanPlane P] (prg_nd : ParallelogramND P) : prg_nd.Parallelogram_non_triv := by
  sorry

theorem parallelogram_para_of_parallelogramND {P : Type _} [EuclideanPlane P] (prg_nd : ParallelogramND P) : prg_nd.IsParallelogram_para := by
  sorry

def ParallelogramND.mk_pt_pt_pt_pt {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D) IsConvex) (h': (QDR A B C D) IsParallelogram) : ParallelogramND P where
  toQuadrilateral := (QDR A B C D)
  nd := h; convex := h
  is_parallelogram := h'

scoped notation "PRG_nd" => ParallelogramND.mk_pt_pt_pt_pt

/- `I think these criteria may should be theorems, instead of functions below.`-/
/- `besides these, we also need the make method from qdr and qdr_nd to prg_nd `-/
-- def ParallelogramND.mk_parallelogram_non_triv {P : Type _} [EuclideanPlane P] {prg : Parallelogram P} (non_triv: prg.Parallelogram_non_triv): ParallelogramND P where
--   toQuadrilateral := prg.toQuadrilateral
--   nd := sorry
--   convex := sorry
--   is_parallelogram := sorry

-- scoped notation "PRG_nd₁" => ParallelogramND.mk_parallelogram_non_triv

-- def ParallelogramND.mk_parallelogram_para {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsParallelogram) (para: (QDR_nd A B C D h).IsParallelogram_para): ParallelogramND P where
--   point₁ := A; point₂ := B; point₃ := C; point₄ := D
--   nd := h
--   convex := sorry
--   is_parallelogram := h'

-- scoped notation "PRG_nd₂" => ParallelogramND.mk_parallelogram_para

/- here is two theorem using first version of definition of PRG_nd, may not useful currently. -/
-- theorem Quadrilateral.IsParallelogram_nd_redef {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) (h: qdr.IsND) (h': qdr IsParallelogram) (h': (((Quadrilateral_nd.mk_is_nd h).angle₁.value.IsPos ∧ (Quadrilateral_nd.mk_is_nd h).angle₃.value.IsPos) ∨ ((Quadrilateral_nd.mk_is_nd h).angle₁.value.IsNeg ∧ (Quadrilateral_nd.mk_is_nd h).angle₃.value.IsNeg) ∨ ((Quadrilateral_nd.mk_is_nd h).angle₂.value.IsPos ∧ (Quadrilateral_nd.mk_is_nd h).angle₄.value.IsPos) ∨ ((Quadrilateral_nd.mk_is_nd h).angle₂.value.IsNeg ∧ (Quadrilateral_nd.mk_is_nd h).angle₄.value.IsNeg))) : (Quadrilateral_nd.mk_is_nd h).IsParallelogramND := sorry

-- theorem Parallelogram.parallelogramIs_nd_redef {P : Type _} [EuclideanPlane P] (qdr_para : Parallelogram P) (h': qdr_para.1.IsND) (k: ((Quadrilateral_nd.mk_is_nd h').angle₁.value.IsPos ∧ (Quadrilateral_nd.mk_is_nd h').angle₃.value.IsPos) ∨ ((Quadrilateral_nd.mk_is_nd h').angle₁.value.IsNeg ∧ (Quadrilateral_nd.mk_is_nd h').angle₃.value.IsNeg) ∨ ((Quadrilateral_nd.mk_is_nd h').angle₂.value.IsPos ∧ (Quadrilateral_nd.mk_is_nd h').angle₄.value.IsPos) ∨ ((Quadrilateral_nd.mk_is_nd h').angle₂.value.IsNeg ∧ (Quadrilateral_nd.mk_is_nd h').angle₄.value.IsNeg)) : (Quadrilateral_nd.mk_is_nd h').IsParallelogramND := sorry

section permute

variable {P : Type _} [EuclideanPlane P]
variable (qdr : Quadrilateral P)
variable (qdr_nd : Quadrilateral_nd P)
variable (qdr_cvx : Quadrilateral_cvx P)
variable (prg : Parallelogram P)

theorem qdr_is_parallelogram_permute_iff : (qdr.IsParallelogram) ↔ ((qdr.permute).IsParallelogram) := by
  unfold Quadrilateral.permute
  unfold Quadrilateral.IsParallelogram
  simp only
  unfold Vec.mkPtPt
  rw [eq_comm]
  refine (eq_iff_eq_of_sub_eq_sub ?H)
  rw [vsub_sub_vsub_comm]

theorem qdr_is_parallelogramND_permute_iff : (qdr.IsParallelogramND) ↔ ((qdr.permute).IsParallelogramND) := by
  sorry

theorem qdr_nd_is_parallelogram_permute_iff : (qdr_nd.IsParallelogram) ↔ ((qdr_nd.permute).IsParallelogram) := by
  sorry

theorem qdr_nd_is_parallelogram_nd_permute_iff : (qdr_nd.IsParallelogramND) ↔ ((qdr_nd.permute).IsParallelogramND) := by
  sorry

theorem qdr_cvx_is_parallelogram_nd_permute_iff : (qdr_cvx.IsParallelogramND) ↔ ((qdr_cvx.permute).IsParallelogramND) := by
  sorry

theorem prg_is_parallelogram_nd_permute_iff : (prg.IsParallelogramND) ↔ ((prg.permute).IsParallelogramND) := by
  sorry

end permute

section reflect

variable {P : Type _} [EuclideanPlane P]
variable (qdr : Quadrilateral P)
variable (qdr_nd : Quadrilateral_nd P)
variable (qdr_cvx : Quadrilateral_cvx P)
variable (prg : Parallelogram P)

theorem qdr_is_parallelogram_reflect_iff : (qdr.IsParallelogram) ↔ ((qdr.reflect).IsParallelogram) := by
  unfold Quadrilateral.reflect
  unfold Quadrilateral.IsParallelogram
  simp only
  unfold Vec.mkPtPt
  refine (eq_iff_eq_of_sub_eq_sub ?H)
  sorry

theorem qdr_is_parallelogramND_reflect_iff : (qdr.IsParallelogramND) ↔ ((qdr.reflect).IsParallelogramND) := by
  sorry

theorem qdr_nd_is_parallelogram_reflect_iff : (qdr_nd.IsParallelogram) ↔ ((qdr_nd.reflect).IsParallelogram) := by
  sorry

theorem qdr_nd_is_parallelogram_nd_reflect_iff : (qdr_nd.IsParallelogramND) ↔ ((qdr_nd.reflect).IsParallelogramND) := by
  sorry

theorem qdr_cvx_is_parallelogram_nd_reflect_iff : (qdr_cvx.IsParallelogramND) ↔ ((qdr_cvx.reflect).IsParallelogramND) := by
  sorry

theorem prg_is_parallelogram_nd_reflect_iff : (prg.IsParallelogramND) ↔ ((prg.reflect).IsParallelogramND) := by
  sorry

end reflect

section criteria_prg_nd_of_prg

variable {P : Type _} [EuclideanPlane P]
variable (qdr_nd : Quadrilateral_nd P)

/- `like above, I think functions in this section should be deleted` -/
theorem parallelogram_not_colinear₁_is_parallelogram_nd (para : qdr_nd.toQuadrilateral IsParallelogram) (h : ¬ colinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) : qdr_nd.IsParallelogramND := by
  sorry

-- def Parallelogram_nd.mk_pt_pt_pt_pt₁ {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h' : (QDR A B C D) IsParallelogram) (non_colinear₁ : ¬ colinear B C D) : ParallelogramND P where
--   point₁ := A; point₂ := B; point₃ := C; point₄ := D
--   nd := h; convex := sorry
--   is_parallelogram := h'

-- scoped notation "PRG_nd₁" => Parallelogram_nd.mk_pt_pt_pt_pt₁

-- def mk_parallelogram_nd₁ {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h' : qdr.IsND) (non_colinear₁ : ¬ colinear qdr.2 qdr.3 qdr.4) : ParallelogramND P where
--   point₁ := qdr.point₁; point₂ := qdr.point₂; point₃ := qdr.point₃; point₄ := qdr.point₄
--   nd := h'; convex := sorry
--   is_parallelogram := h

theorem parallelogram_not_colinear₂_is_parallelogram_nd (para: qdr_nd.toQuadrilateral IsParallelogram) (h: ¬ colinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁) : qdr_nd.IsParallelogramND := by
  sorry

-- def Parallelogram_nd.mk_pt_pt_pt_pt₂ {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsParallelogram) (non_colinear₂: ¬ colinear A C D) : ParallelogramND P where
--   point₁ := A; point₂ := B; point₃ := C; point₄ := D
--   nd := h; convex := sorry
--   is_parallelogram := h'

-- scoped notation "PRG_nd₂" => Parallelogram_nd.mk_pt_pt_pt_pt₂

-- def mk_parallelogram_nd₂ {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h': qdr.IsND) (non_colinear₂: ¬ colinear qdr.1 qdr.3 qdr.4) : ParallelogramND P where
--   point₁ := qdr.point₁; point₂ := qdr.point₂; point₃ := qdr.point₃; point₄ := qdr.point₄
--   nd := h'; convex := sorry
--   is_parallelogram := h

theorem parallelogram_not_colinear₃_is_parallelogram_nd (para: qdr_nd.toQuadrilateral IsParallelogram) (h: ¬ colinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂) : qdr_nd.IsParallelogramND := by
  sorry

-- def Parallelogram_nd.mk_pt_pt_pt_pt₃ {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsParallelogram) (non_colinear₃: ¬ colinear A B D) : ParallelogramND P where
--   point₁ := A; point₂ := B; point₃ := C; point₄ := D
--   nd := h; convex := sorry
--   is_parallelogram := h'

-- scoped notation "PRG_nd₃" => Parallelogram_nd.mk_pt_pt_pt_pt₃

-- def mk_parallelogram_nd₃ {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h': qdr.IsND) (non_colinear₃: ¬ colinear qdr.1 qdr.2 qdr.4) : ParallelogramND P where
--   point₁ := qdr.point₁; point₂ := qdr.point₂; point₃ := qdr.point₃; point₄ := qdr.point₄
--   nd := h'; convex := sorry
--   is_parallelogram := h

theorem parallelogram_not_colinear₄_is_parallelogram_nd (para: qdr_nd.toQuadrilateral IsParallelogram) (h: ¬ colinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃) : qdr_nd.IsParallelogramND := by
  sorry

-- def Parallelogram_nd.mk_pt_pt_pt_pt₄ {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsParallelogram) (non_colinear₄: ¬ colinear A B C) : ParallelogramND P where
--   point₁ := A; point₂ := B; point₃ := C; point₄ := D
--   nd := h; convex := sorry
--   is_parallelogram := h'

-- scoped notation "PRG_nd₄" => Parallelogram_nd.mk_pt_pt_pt_pt₄

-- def mk_parallelogram_nd₄ {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h': qdr.IsND) (non_colinear₄: ¬ colinear qdr.1 qdr.2 qdr.3) : ParallelogramND P where
--   point₁ := qdr.point₁; point₂ := qdr.point₂; point₃ := qdr.point₃; point₄ := qdr.point₄
--   nd := h'; convex := sorry
--   is_parallelogram := h

/- we left these four theorems as interface for user. -/
theorem is_parallelogramND_iff_not_colinear₁ : qdr_nd.IsParallelogramND ↔ (¬ colinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) := sorry

theorem is_parallelogramND_iff_not_colinear₂ : qdr_nd.IsParallelogramND ↔ (¬ colinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) := sorry

theorem is_parallelogramND_iff_not_colinear₃ : qdr_nd.IsParallelogramND ↔ (¬ colinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) := sorry

theorem is_parallelogramND_iff_not_colinear₄ : qdr_nd.IsParallelogramND ↔ (¬ colinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) := sorry

end criteria_prg_nd_of_prg

-- `the form of all the codes above needs more discussion`

section criteria_prg_nd_of_qdr_nd

variable {P : Type _} [EuclideanPlane P]
variable {A B C D : P} (nd : (QDR A B C D).IsND)
variable (qdr : Quadrilateral P) (qdr_nd : Quadrilateral_nd P)

theorem qdr_nd_is_prg_nd_of_para_para_not_colinear₄ (h₁ : qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) (h₂ : qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃) (notcolinear : ¬ colinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃) : qdr_nd.IsParallelogramND := by
  sorry

theorem qdr_nd_is_prg_nd_of_para_para_not_colinear₄_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂.out) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄.out)) (h₂ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄.out) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃.out)) (notcolinear : ¬ colinear A B C) : (QDR_nd A B C D nd).IsParallelogramND := qdr_nd_is_prg_nd_of_para_para_not_colinear₄ (QDR_nd A B C D nd) h₁ h₂ notcolinear

theorem qdr_nd_is_prg_nd_of_para_para_not_colinear₁ (h₁ : qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) (h₂ : qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃) (notcolinear : ¬ colinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) : qdr_nd.IsParallelogramND := (qdr_nd_is_parallelogram_nd_permute_iff qdr_nd).mpr (qdr_nd_is_prg_nd_of_para_para_not_colinear₄ qdr_nd.permute (SegND.para_rev_of_para h₂.symm) (SegND.para_rev_of_para h₁.symm).symm notcolinear)

theorem qdr_nd_is_prg_nd_of_para_para_not_colinear₁_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂.out) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄.out)) (h₂ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄.out) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃.out)) (notcolinear : ¬ colinear B C D) : (QDR_nd A B C D nd).IsParallelogramND := qdr_nd_is_prg_nd_of_para_para_not_colinear₁ (QDR_nd A B C D nd) h₁ h₂ notcolinear

theorem qdr_nd_is_prg_nd_of_para_para_not_colinear₂ (h₁ : qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) (h₂ : qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃) (notcolinear : ¬ colinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁) : qdr_nd.IsParallelogramND := (qdr_nd_is_parallelogram_nd_permute_iff qdr_nd).mpr (qdr_nd_is_prg_nd_of_para_para_not_colinear₁ qdr_nd.permute (SegND.para_rev_of_para h₂.symm) (SegND.para_rev_of_para h₁.symm).symm notcolinear)

theorem qdr_nd_is_prg_nd_of_para_para_not_colinear₂_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂.out) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄.out)) (h₂ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄.out) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃.out)) (notcolinear : ¬ colinear C D A) : (QDR_nd A B C D nd).IsParallelogramND := qdr_nd_is_prg_nd_of_para_para_not_colinear₂ (QDR_nd A B C D nd) h₁ h₂ notcolinear

theorem qdr_nd_is_prg_nd_of_para_para_not_colinear₃ (h₁ : qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) (h₂ : qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃) (notcolinear : ¬ colinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂) : qdr_nd.IsParallelogramND := (qdr_nd_is_parallelogram_nd_permute_iff qdr_nd).mpr (qdr_nd_is_prg_nd_of_para_para_not_colinear₂ qdr_nd.permute (SegND.para_rev_of_para h₂.symm) (SegND.para_rev_of_para h₁.symm).symm notcolinear)

theorem qdr_nd_is_prg_nd_of_para_para_not_colinear₄₁₂_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂.out) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄.out)) (h₂ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄.out) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃.out)) (notcolinear : ¬ colinear D A B) : (QDR_nd A B C D nd).IsParallelogramND := qdr_nd_is_prg_nd_of_para_para_not_colinear₃ (QDR_nd A B C D nd) h₁ h₂ notcolinear

theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₁₂₃ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcolinear : ¬ colinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃) : qdr_nd.IsParallelogramND := by
  sorry

theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₁₂₃_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄.out (QDR_nd A B C D nd).nd₁₂.out).value = (ANG B C D (QDR_nd A B C D nd).nd₂₃.out.symm (QDR_nd A B C D nd).nd₃₄.out).value) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.out.symm (QDR_nd A B C D nd).nd₂₃.out).value = (ANG C D A (QDR_nd A B C D nd).nd₃₄.out.symm (QDR_nd A B C D nd).nd₁₄.out.symm).value) (notcolinear : ¬ colinear A B C) : (QDR_nd A B C D nd).IsParallelogramND := qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₁₂₃ (QDR_nd A B C D nd) h₁ h₂ notcolinear

theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₂₃₄ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcolinear : ¬ colinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) : qdr_nd.IsParallelogramND := by sorry

theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₂₃₄_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄.out (QDR_nd A B C D nd).nd₁₂.out).value = (ANG B C D (QDR_nd A B C D nd).nd₂₃.out.symm (QDR_nd A B C D nd).nd₃₄.out).value) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.out.symm (QDR_nd A B C D nd).nd₂₃.out).value = (ANG C D A (QDR_nd A B C D nd).nd₃₄.out.symm (QDR_nd A B C D nd).nd₁₄.out.symm).value) (notcolinear : ¬ colinear B C D) : (QDR_nd A B C D nd).IsParallelogramND := qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₂₃₄ (QDR_nd A B C D nd) h₁ h₂ notcolinear

theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₃₄₁ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcolinear : ¬ colinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁) : qdr_nd.IsParallelogramND := by sorry

theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₃₄₁_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄.out (QDR_nd A B C D nd).nd₁₂.out).value = (ANG B C D (QDR_nd A B C D nd).nd₂₃.out.symm (QDR_nd A B C D nd).nd₃₄.out).value) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.out.symm (QDR_nd A B C D nd).nd₂₃.out).value = (ANG C D A (QDR_nd A B C D nd).nd₃₄.out.symm (QDR_nd A B C D nd).nd₁₄.out.symm).value) (notcolinear : ¬ colinear C D A) : (QDR_nd A B C D nd).IsParallelogramND := qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₃₄₁ (QDR_nd A B C D nd) h₁ h₂ notcolinear

theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₄₁₂ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcolinear : ¬ colinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂) : qdr_nd.IsParallelogramND := by sorry

theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₄₁₂_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄.out (QDR_nd A B C D nd).nd₁₂.out).value = (ANG B C D (QDR_nd A B C D nd).nd₂₃.out.symm (QDR_nd A B C D nd).nd₃₄.out).value) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.out.symm (QDR_nd A B C D nd).nd₂₃.out).value = (ANG C D A (QDR_nd A B C D nd).nd₃₄.out.symm (QDR_nd A B C D nd).nd₁₄.out.symm).value) (notcolinear : ¬ colinear D A B) : (QDR_nd A B C D nd).IsParallelogramND := qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₄₁₂ (QDR_nd A B C D nd) h₁ h₂ notcolinear

theorem qdr_nd_is_prg_nd_of_eq_length_eq_length_eq_angle_sign (h₁ : qdr_nd.edge_nd₁₂.length = qdr_nd.edge_nd₃₄.length) (h₂ : qdr_nd.edge_nd₁₄.length = qdr_nd.edge_nd₂₃.length) (h : (qdr_nd.angle₁.value.IsPos ∧ qdr_nd.angle₃.value.IsPos) ∨ (qdr_nd.angle₁.value.IsNeg ∧ qdr_nd.angle₃.value.IsNeg)) : qdr_nd.IsParallelogramND := by sorry

theorem qdr_nd_is_prg_nd_of_eq_length_eq_length_eq_angle_sign_variant (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG A D).length = (SEG B C).length) (h : ((ANG D A B (QDR_nd A B C D nd).nd₁₄.out (QDR_nd A B C D nd).nd₁₂.out).value.IsPos ∧ (ANG B C D (QDR_nd A B C D nd).nd₂₃.out.symm (QDR_nd A B C D nd).nd₃₄.out).value.IsPos) ∨ ((ANG D A B (QDR_nd A B C D nd).nd₁₄.out (QDR_nd A B C D nd).nd₁₂.out).value.IsNeg ∧ (ANG B C D (QDR_nd A B C D nd).nd₂₃.out.symm (QDR_nd A B C D nd).nd₃₄.out).value.IsNeg)) : (QDR_nd A B C D nd).IsParallelogramND := qdr_nd_is_prg_nd_of_eq_length_eq_length_eq_angle_sign (QDR_nd A B C D nd) h₁ h₂ h

theorem qdr_nd_is_prg_nd_of_eq_length_eq_length_eq_angle_sign' (h₁ : qdr_nd.edge_nd₁₂.length = qdr_nd.edge_nd₃₄.length) (h₂ : qdr_nd.edge_nd₁₄.length = qdr_nd.edge_nd₂₃.length) (h : (qdr_nd.angle₂.value.IsPos ∧ qdr_nd.angle₄.value.IsPos) ∨ (qdr_nd.angle₂.value.IsNeg ∧ qdr_nd.angle₄.value.IsNeg)) : qdr_nd.IsParallelogramND := by sorry

theorem qdr_nd_is_prg_nd_of_eq_length_eq_length_eq_angle_sign'_variant (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG A D).length = (SEG B C).length) (h : ((ANG A B C (QDR_nd A B C D nd).nd₁₂.out.symm (QDR_nd A B C D nd).nd₂₃.out).value.IsPos ∧ (ANG C D A (QDR_nd A B C D nd).nd₃₄.out.symm (QDR_nd A B C D nd).nd₁₄.out.symm).value.IsPos) ∨ ((ANG A B C (QDR_nd A B C D nd).nd₁₂.out.symm (QDR_nd A B C D nd).nd₂₃.out).value.IsNeg ∧ (ANG C D A (QDR_nd A B C D nd).nd₃₄.out.symm (QDR_nd A B C D nd).nd₁₄.out.symm).value.IsNeg)) : (QDR_nd A B C D nd).IsParallelogramND := qdr_nd_is_prg_nd_of_eq_length_eq_length_eq_angle_sign' (QDR_nd A B C D nd) h₁ h₂ h

end criteria_prg_nd_of_qdr_nd

section criteria_prg_of_qdr_nd

variable {P : Type _} [EuclideanPlane P]
variable {A B C D: P}
variable (nd : (QDR A B C D).IsND)
variable (cvx : (QDR A B C D).IsConvex)
variable {P : Type _} [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P)
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)

theorem qdr_nd_is_prg_of_para_eq_length_para_eq_length (h₁ : qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) (h₂ : qdr_nd.edge_nd₁₂.length = qdr_nd.edge_nd₃₄.length) (H₁ : qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃) (h₂ : qdr_nd.edge_nd₁₄.length = qdr_nd.edge_nd₂₃.length): qdr_nd.IsParallelogram := by
  sorry

theorem qdr_nd_is_prg_of_para_eq_length_para_eq_length_varient (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂.out) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄.out)) (h₂ : (SEG A B).length = (SEG C D).length) (H₁ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄.out) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃.out)) (H₂ : (SEG A D).length = (SEG B C).length): (Quadrilateral_nd.mk_is_nd nd).IsParallelogram := by
  sorry

theorem qdr_nd_is_prg_nd_of_diag_inx_eq_mid_eq_mid (h' : (qdr_nd.diag₁₃).midpoint = (qdr_nd.diag₂₄).midpoint) : qdr_nd.IsParallelogram := by
  sorry

theorem qdr_nd_is_prg_nd_of_diag_inx_eq_mid_eq_mid_variant (h' : (SEG A C).midpoint = (SEG B D).midpoint) : (Quadrilateral_nd.mk_is_nd nd).IsParallelogram := by
  sorry

end criteria_prg_of_qdr_nd

section criteria_prg_nd_of_qdr_cvx

variable {P : Type _} [EuclideanPlane P]
variable {A B C D : P}
variable (nd : (QDR A B C D).IsND)
variable (cvx : (QDR_nd A B C D nd).IsConvex)
variable {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P)
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)

theorem qdr_cvx_is_prg_nd_of_para_para (h₁ : qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) (h₂ : qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃) : qdr_cvx.IsParallelogramND := by
  sorry

theorem qdr_cvx_is_prg_nd_of_para_para_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂.out) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄.out)) (h₂ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄.out) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃.out)) : (Quadrilateral_nd.mk_is_nd nd).IsParallelogramND := by sorry

theorem qdr_cvx_is_prg_nd_of_eq_length_eq_length (h₁ : qdr_cvx.edge_nd₁₂.length = qdr_cvx.edge_nd₃₄.length) (h₂ : qdr_cvx.edge_nd₁₄.length = qdr_cvx.edge_nd₂₃.length) : qdr_cvx.IsParallelogramND := by sorry

theorem qdr_cvx_is_prg_nd_of_eq_length_eq_length_variant (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG A D).length = (SEG B C).length) : (Quadrilateral_nd.mk_is_nd nd).IsParallelogramND := by sorry

theorem qdr_cvx_is_prg_nd_of_para_eq_length (h₁ : qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) (h₂ : qdr_cvx.edge_nd₁₂.length = qdr_cvx.edge_nd₃₄.length) : qdr_cvx.IsParallelogramND := by sorry

theorem qdr_cvx_is_prg_nd_of_para_eq_length_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂.out) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄.out)) (h₂ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂.out).length = (SEG_nd C D (QDR_nd A B C D nd).nd₃₄.out).length) : (Quadrilateral_nd.mk_is_nd nd).IsParallelogramND := by sorry

theorem qdr_cvx_is_prg_nd_of_para_eq_length' (h₁ : qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃) (h₂ : qdr_cvx.edge_nd₁₄.length = qdr_cvx.edge_nd₂₃.length) : qdr_cvx.IsParallelogramND := by sorry

theorem qdr_cvx_is_prg_nd_of_para_eq_length'_variant (h₁ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄.out) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃.out)) (h₂ : (QDR_nd A B C D nd).edge_nd₁₄.length = (QDR_nd A B C D nd).edge_nd₂₃.length) : (Quadrilateral_nd.mk_is_nd nd).IsParallelogramND := by
  sorry

theorem qdr_cvx_is_prg_nd_of_eq_angle_value_eq_angle_value (h₁ : qdr_cvx.angle₁ = qdr_cvx.angle₃) (h₂ : qdr_cvx.angle₂ = qdr_cvx.angle₄) : qdr_cvx.IsParallelogramND := by sorry

theorem qdr_cvx_is_prg_of_eq_angle_value_eq_angle_value_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄.out (QDR_nd A B C D nd).nd₁₂.out) = (ANG B C D (QDR_nd A B C D nd).nd₂₃.out.symm (QDR_nd A B C D nd).nd₃₄.out)) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.out.symm (QDR_nd A B C D nd).nd₂₃.out) = (ANG C D A (QDR_nd A B C D nd).nd₃₄.out.symm (QDR_nd A B C D nd).nd₁₄.out.symm)) : (Quadrilateral_nd.mk_is_nd nd).IsParallelogramND := by sorry

theorem qdr_cvx_is_prg_nd_of_diag_inx_eq_mid_eq_mid (h' : qdr_cvx.diag_nd₁₃.midpoint = qdr_cvx.diag_nd₂₄.midpoint) : qdr_cvx.IsParallelogramND := by sorry

theorem qdr_cvx_is_prg_of_diag_inx_eq_mid_eq_mid_variant (h' : (SEG A C).midpoint = (SEG B D).midpoint) : (Quadrilateral_nd.mk_is_nd nd).IsParallelogramND := by
  sorry

end criteria_prg_nd_of_qdr_cvx

section property

variable {P : Type _} [EuclideanPlane P]
variable {A B C D : P}
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)
variable {P : Type _} [EuclideanPlane P] (prg : Parallelogram P)

theorem eq_length_of_is_prg_nd : (SEG prg.point₁ prg.point₂).length = (SEG prg.point₃ prg.point₄).length := by sorry

theorem eq_length_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram) : (SEG A B).length = (SEG C D).length := by sorry

theorem eq_length_of_is_prg_nd' (h : qdr.IsParallelogramND) : (SEG qdr.point₁ qdr.point₄).length = (SEG qdr.point₂ qdr.point₃).length := by sorry

theorem eq_length_of_is_prg_nd'_variant  (h : (QDR A B C D).IsParallelogram) : (SEG A D).length = (SEG B C).length := by sorry

theorem eq_midpt_of_diag_of_is_prg : (SEG prg.point₁ prg.point₃).midpoint = (SEG prg.point₂ prg.point₄).midpoint := by sorry

theorem eq_vec_of_is_prg_nd (h : qdr.IsParallelogram) : VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃ := h

theorem eq_vec_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram) : VEC A B = VEC D C := eq_vec_of_is_prg_nd (QDR A B C D) h

theorem eq_vec_of_is_prg_nd' (h : qdr.IsParallelogram) : VEC qdr.point₁ qdr.point₄ = VEC qdr.point₂ qdr.point₃ := by
  rw [← vec_add_vec qdr.point₁ qdr.point₂ qdr.point₄]
  rw [← vec_add_vec qdr.point₂ qdr.point₄ qdr.point₃]
  rw [eq_vec_of_is_prg_nd qdr h]
  exact add_comm (VEC qdr.point₄ qdr.point₃) (VEC qdr.point₂ qdr.point₄)

theorem eq_vec_of_is_prg_nd'_variant (h : (QDR A B C D).IsParallelogram) : VEC A D = VEC B C := eq_vec_of_is_prg_nd' (QDR A B C D) h

theorem parallelogram_law : 2 * (SEG prg.point₁ prg.point₂).length ^ 2 + 2 * (SEG prg.point₂ prg.point₃).length ^ 2 = (SEG prg.point₁ prg.point₃).length ^ 2 + (SEG prg.point₂ prg.point₄).length ^ 2 := by sorry

theorem nd_parallelogram_law_variant (h : (QDR A B C D).IsParallelogram) : 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2 := by sorry

end property

section property_nd

variable {P : Type _} [EuclideanPlane P]
variable {A B C D : P}
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)
variable {P : Type _} [EuclideanPlane P] (prg_nd : ParallelogramND P)

theorem nd_is_convex_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogramND) : (QDR A B C D) IsConvex := by sorry

theorem nd₁₂_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogramND) : B ≠ A := by
  have s : (QDR A B C D) IsConvex := by exact h.left
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₂.out

theorem nd₂₃_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogramND) : C ≠ B := by
  have s : (QDR A B C D) IsConvex := by exact h.left
  exact (Quadrilateral_cvx.mk_is_convex s).nd₂₃.out

theorem nd₃₄_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogramND) : D ≠ C := by
  have s : (QDR A B C D) IsConvex := by exact h.left
  exact (Quadrilateral_cvx.mk_is_convex s).nd₃₄.out

theorem nd₁₄_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogramND) : D ≠ A := by
  have s : (QDR A B C D) IsConvex := by exact h.left
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₄.out

theorem nd₁₃_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogramND) : C ≠ A := by
  have s : (QDR A B C D) IsConvex := by exact h.left
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₃.out

theorem nd₂₄_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogramND) : D ≠ B := by
  have s : (QDR A B C D) IsConvex := by exact h.left
  exact (Quadrilateral_cvx.mk_is_convex s).nd₂₄.out

theorem nd_para_of_is_prg_nd : (SEG_nd prg_nd.point₁ prg_nd.point₂ prg_nd.nd₁₂.out) ∥ (SEG_nd prg_nd.point₃ prg_nd.point₄ prg_nd.nd₃₄.out) := by sorry

theorem nd_para_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogramND) : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ (SEG_nd C D (nd₃₄_of_is_prg_nd_variant h)) := by sorry

theorem nd_para_of_is_prg_nd' : (SEG_nd prg_nd.point₁ prg_nd.point₄ prg_nd.nd₁₄.out) ∥ (SEG_nd prg_nd.point₂ prg_nd.point₃ prg_nd.nd₂₃.out):= by sorry

theorem nd_para_of_is_prg_nd'_variant (h : (QDR A B C D).IsParallelogramND) : SEG_nd A D (nd₁₄_of_is_prg_nd_variant h) ∥ SEG_nd B C (nd₂₃_of_is_prg_nd_variant h) := by sorry

theorem nd_eq_angle_value_of_is_prg_nd : ANG prg_nd.point₁ prg_nd.point₂ prg_nd.point₃ prg_nd.nd₁₂.out.symm prg_nd.nd₂₃.out = ANG prg_nd.point₃ prg_nd.point₄ prg_nd.point₁ prg_nd.nd₃₄.out.symm prg_nd.nd₁₄.out.symm := by sorry

theorem nd_eq_angle_value_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogramND) : ANG A B C ((nd₁₂_of_is_prg_nd_variant h).symm) (nd₂₃_of_is_prg_nd_variant h) = ANG C D A ((nd₃₄_of_is_prg_nd_variant h).symm) ((nd₁₄_of_is_prg_nd_variant h).symm) := by sorry

theorem nd_eq_angle_value_of_is_prg_nd' : ANG prg_nd.point₄ prg_nd.point₁ prg_nd.point₂ prg_nd.nd₁₄.out prg_nd.nd₁₂.out = ANG prg_nd.point₂ prg_nd.point₃ prg_nd.point₄ prg_nd.nd₂₃.out.symm prg_nd.nd₃₄.out := by sorry

theorem nd_eq_angle_value_of_is_prg_nd'_variant (h : (QDR A B C D).IsParallelogramND) : (ANG D A B (nd₁₄_of_is_prg_nd_variant h) (nd₁₂_of_is_prg_nd_variant h)).value = (ANG B C D ((nd₂₃_of_is_prg_nd_variant h).symm) (nd₃₄_of_is_prg_nd_variant h)).value := by sorry

theorem nd_eq_midpt_of_diag_inx_of_is_prg_nd : prg_nd.diag_inx = (SEG prg_nd.point₁ prg_nd.point₃).midpoint := by sorry

theorem nd_eq_midpt_of_diag_inx_of_is_prg_nd' : prg_nd.diag_inx = (SEG prg_nd.point₂ prg_nd.point₄).midpoint := by sorry

theorem nd_eq_midpt_of_diag_of_is_prg_variant (h : (QDR A B C D).IsParallelogramND) : (SEG A C).midpoint = (SEG B D).midpoint := by sorry

end property_nd
