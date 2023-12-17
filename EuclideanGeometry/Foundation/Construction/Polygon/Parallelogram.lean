import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral
import EuclideanGeometry.Foundation.Construction.Polygon.Trapezoid
import EuclideanGeometry.Foundation.Tactic.Congruence.Congruence
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Position.Angle
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
   have had : qdr_nd.1.1 ≠ qdr_nd.1.4 := by sorry
   have hbd : qdr_nd.1.2 ≠ qdr_nd.1.4 := by sorry
   have hcd : qdr_nd.1.3 ≠ qdr_nd.1.4 := by sorry

   have t : ¬ colinear qdr_nd.point₂ qdr_nd.point₁ qdr_nd.point₃ := by
     by_contra k
     simp only [flip_colinear_fst_snd k, not_true_eq_false] at h
   have x : ¬ colinear_of_nd hbc hba.symm := by
     unfold colinear at t
     simp only [hca, hbc, hba.symm, or_self, dite_false] at t
     simp only [t, not_false_eq_true]
   have l₁ : qdr_nd.edge_nd₁₂.toProj=VecND.toProj ⟨VEC qdr_nd.1.1 qdr_nd.1.2, _⟩ := by rfl
   have l₁' : qdr_nd.edge_nd₁₂.toProj=VecND.toProj ⟨VEC qdr_nd.1.2 qdr_nd.1.1, (ne_iff_vec_ne_zero _ _).mp hba.symm⟩ := by
     have y₁:VecND.toProj ⟨VEC qdr_nd.1.2 qdr_nd.1.1, (ne_iff_vec_ne_zero _ _).mp hba.symm⟩=VecND.toProj ⟨VEC qdr_nd.1.1 qdr_nd.1.2, (ne_iff_vec_ne_zero _ _).mp hba⟩ := by
       have z₁: VEC qdr_nd.1.2 qdr_nd.1.1 = (-1)•VEC qdr_nd.1.1 qdr_nd.1.2 := by sorry
       sorry
     simp only [l₁, ne_eq, y₁]
   have l₂ : qdr_nd.edge_nd₂₃.toProj=VecND.toProj ⟨VEC qdr_nd.1.2 qdr_nd.1.3, _⟩ := by rfl
   have l₂' : qdr_nd.edge_nd₂₃.toProj=VecND.toProj ⟨VEC qdr_nd.1.3 qdr_nd.1.2, (ne_iff_vec_ne_zero _ _).mp hbc⟩ := by sorry
   have l₃ : qdr_nd.edge_nd₃₄.toProj=VecND.toProj ⟨VEC qdr_nd.1.3 qdr_nd.1.4, _⟩ := by rfl
   have l₃' : qdr_nd.edge_nd₃₄.toProj=VecND.toProj ⟨VEC qdr_nd.1.4 qdr_nd.1.3, (ne_iff_vec_ne_zero _ _).mp hcd⟩ := by sorry
   have l₄ : qdr_nd.edge_nd₁₄.toProj=VecND.toProj ⟨VEC qdr_nd.1.1 qdr_nd.1.4, _⟩ := by rfl
   have l₄' : qdr_nd.edge_nd₁₄.toProj=VecND.toProj ⟨VEC qdr_nd.1.4 qdr_nd.1.1, (ne_iff_vec_ne_zero _ _).mp had⟩ := by sorry
   have s : ¬ qdr_nd.edge_nd₁₂.toProj = qdr_nd.edge_nd₂₃.toProj := by
     unfold colinear_of_nd at x
     simp only [l₁', ne_eq, l₂, x, not_false_eq_true]
     sorry
   have v₁ : qdr_nd.edge_nd₁₂.toProj = qdr_nd.edge_nd₃₄.toProj := by
     unfold Quadrilateral.IsParallelogram at para
     sorry
   have v₁₁ : toProj qdr_nd.edge_nd₁₂ = toProj qdr_nd.edge_nd₃₄ := by exact v₁
   have v₂ : qdr_nd.edge_nd₂₃.toProj = qdr_nd.edge_nd₁₄.toProj := by sorry
   have v₂₁ : toProj qdr_nd.edge_nd₂₃ = toProj qdr_nd.edge_nd₁₄ := by exact v₂
   have s₁ : ¬ qdr_nd.edge_nd₁₂.toProj = qdr_nd.edge_nd₂₃.toProj := by sorry
   have s₂ : ¬ qdr_nd.edge_nd₂₃.toProj = qdr_nd.edge_nd₃₄.toProj := by sorry
   have s₃ : ¬ qdr_nd.edge_nd₃₄.toProj = qdr_nd.edge_nd₁₄.toProj := by sorry
   have s₄ : ¬ qdr_nd.edge_nd₁₄.toProj = qdr_nd.edge_nd₁₂.toProj := by sorry
   constructor
   constructor
   unfold parallel
   simp only [v₁₁]
   unfold parallel
   simp only [v₂₁]
   constructor
   simp only [h, not_false_eq_true]
   by_contra m₃
   have m₂ :  ¬ colinear qdr_nd.point₃ qdr_nd.point₂ qdr_nd.point₄ := by
     by_contra k₁
     unfold colinear at k₁
     simp [hbd.symm,hcd,hbc] at k₁
     unfold colinear_of_nd at k₁
     have p₄:qdr_nd.edge_nd₂₃.toProj = qdr_nd.edge_nd₃₄.toProj  := by
       rw[l₂',l₃]
       exact k₁
     simp[p₄] at s₂
   simp [flip_colinear_fst_snd m₃] at m₂
   by_contra m₅
   have m₄ :  ¬ colinear qdr_nd.point₄ qdr_nd.point₃ qdr_nd.point₁ := by
     by_contra k₂
     unfold colinear at k₂
     simp [hca.symm,hcd,had.symm] at k₂
     unfold colinear_of_nd at k₂
     have p₅:qdr_nd.edge_nd₃₄.toProj = qdr_nd.edge_nd₁₄.toProj := by
       rw[l₄',l₃']
       exact k₂
     simp[p₅] at s₃

   simp [flip_colinear_fst_snd m₅] at m₄
   by_contra m₇
   have m₆ :  ¬ colinear qdr_nd.point₁ qdr_nd.point₄ qdr_nd.point₂ := by
     by_contra k₃
     unfold colinear at k₃
     simp [hbd,hba.symm,had.symm] at k₃
     unfold colinear_of_nd at k₃
     have p₆:qdr_nd.edge_nd₁₄.toProj = qdr_nd.edge_nd₁₂.toProj := by
       rw[l₄,l₁]
       exact k₃
     simp [p₆] at s₄
   simp [flip_colinear_fst_snd m₇] at m₆

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

section criteria_prg_nd_of_qdr_nd

variable {A B C D : P} (nd : (QDR A B C D).IsND) (cvx : (QDR A B C D).IsConvex)
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)
variable {P : Type _} [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P)
variable {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P)

/-- Given Quadrilateral_nd qdr_nd, qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄, qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃, and qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃ is not colinear, then qdr_nd is a Parallelogram_nd. -/
theorem is_prg_nd_of_para_para_not_colinear₁₂₃ (h₁ : qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) (h₂ : qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃) (notcolinear : ¬ colinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃) : qdr_nd.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, AB ∥ CD, AD ∥ BC, and A B C is not colinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_nd_of_para_para_not_colinear₁₂₃_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄)) (h₂ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃)) (notcolinear : ¬ colinear A B C) : (QDR_nd A B C D nd).IsParallelogram_nd := is_prg_nd_of_para_para_not_colinear₁₂₃ (QDR_nd A B C D nd) h₁ h₂ notcolinear

/-- Given Quadrilateral_nd qdr_nd, qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄, qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃, and qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄ is not colinear, then qdr_nd is a Parallelogram_nd. -/
theorem is_prg_nd_of_para_para_not_colinear₂₃₄ (h₁ : qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) (h₂ : qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃) (notcolinear : ¬ colinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) : qdr_nd.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, AB ∥ CD, AD ∥ BC, and B C D is not colinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_nd_of_para_para_not_colinear₂₃₄_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄)) (h₂ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃)) (notcolinear : ¬ colinear B C D) : (QDR_nd A B C D nd).IsParallelogram_nd := is_prg_nd_of_para_para_not_colinear₂₃₄ (QDR_nd A B C D nd) h₁ h₂ notcolinear

/-- Given Quadrilateral_nd qdr_nd, qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄, qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃, and qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁ is not colinear, then qdr_nd is a Parallelogram_nd. -/
theorem is_prg_nd_of_para_para_not_colinear₃₄₁ (h₁ : qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) (h₂ : qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃) (notcolinear : ¬ colinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁) : qdr_nd.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, AB ∥ CD, AD ∥ BC, and C D A is not colinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_nd_of_para_para_not_colinear₃₄₁_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄)) (h₂ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃)) (notcolinear : ¬ colinear C D A) : (QDR_nd A B C D nd).IsParallelogram_nd := is_prg_nd_of_para_para_not_colinear₃₄₁ (QDR_nd A B C D nd) h₁ h₂ notcolinear

/-- Given Quadrilateral_nd qdr_nd, qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄, qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃, and qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂ is not colinear, then qdr_nd is a Parallelogram_nd. -/
theorem is_prg_nd_of_para_para_not_colinear₄₁₂ (h₁ : qdr_nd.edge_nd₁₂ ∥ qdr_nd.edge_nd₃₄) (h₂ : qdr_nd.edge_nd₁₄ ∥ qdr_nd.edge_nd₂₃) (notcolinear : ¬ colinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂) : qdr_nd.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, AB ∥ CD, AD ∥ BC, and D A B is not colinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_nd_of_para_para_not_colinear₄₁₂_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄)) (h₂ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃)) (notcolinear : ¬ colinear D A B) : (QDR_nd A B C D nd).IsParallelogram_nd := is_prg_nd_of_para_para_not_colinear₄₁₂ (QDR_nd A B C D nd) h₁ h₂ notcolinear

/-- Given Quadrilateral_nd qdr_nd, qdr_nd.angle₁.value = qdr_nd.angle₃.value, qdr_nd.angle₂.value = qdr_nd.angle₄.value, and qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃ is not colinear, then qdr_nd is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₁₂₃ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcolinear : ¬ colinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃) : qdr_nd.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, ∠DAB = ∠BCD, ∠ABC = ∠CDA, and A B C is not colinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₁₂₃_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄ (QDR_nd A B C D nd).nd₁₂).value = (ANG B C D (QDR_nd A B C D nd).nd₂₃.symm (QDR_nd A B C D nd).nd₃₄).value) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.symm (QDR_nd A B C D nd).nd₂₃).value = (ANG C D A (QDR_nd A B C D nd).nd₃₄.symm (QDR_nd A B C D nd).nd₁₄.symm).value) (notcolinear : ¬ colinear A B C) : (QDR_nd A B C D nd).IsParallelogram_nd := is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₁₂₃ (QDR_nd A B C D nd) h₁ h₂ notcolinear

/-- Given Quadrilateral_nd qdr_nd, qdr_nd.angle₁.value = qdr_nd.angle₃.value, qdr_nd.angle₂.value = qdr_nd.angle₄.value, and qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄ is not colinear, then qdr_nd is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₂₃₄ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcolinear : ¬ colinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) : qdr_nd.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, ∠DAB = ∠BCD, ∠ABC = ∠CDA, and B C D is not colinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₂₃₄_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄ (QDR_nd A B C D nd).nd₁₂).value = (ANG B C D (QDR_nd A B C D nd).nd₂₃.symm (QDR_nd A B C D nd).nd₃₄).value) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.symm (QDR_nd A B C D nd).nd₂₃).value = (ANG C D A (QDR_nd A B C D nd).nd₃₄.symm (QDR_nd A B C D nd).nd₁₄.symm).value) (notcolinear : ¬ colinear B C D) : (QDR_nd A B C D nd).IsParallelogram_nd := is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₂₃₄ (QDR_nd A B C D nd) h₁ h₂ notcolinear

/-- Given Quadrilateral_nd qdr_nd, qdr_nd.angle₁.value = qdr_nd.angle₃.value, qdr_nd.angle₂.value = qdr_nd.angle₄.value, and qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁ is not colinear, then qdr_nd is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₃₄₁ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcolinear : ¬ colinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁) : qdr_nd.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, ∠DAB = ∠BCD, ∠ABC = ∠CDA, and C D A is not colinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₃₄₁_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄ (QDR_nd A B C D nd).nd₁₂).value = (ANG B C D (QDR_nd A B C D nd).nd₂₃.symm (QDR_nd A B C D nd).nd₃₄).value) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.symm (QDR_nd A B C D nd).nd₂₃).value = (ANG C D A (QDR_nd A B C D nd).nd₃₄.symm (QDR_nd A B C D nd).nd₁₄.symm).value) (notcolinear : ¬ colinear C D A) : (QDR_nd A B C D nd).IsParallelogram_nd := is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₃₄₁ (QDR_nd A B C D nd) h₁ h₂ notcolinear

/-- Given Quadrilateral_nd qdr_nd, qdr_nd.angle₁.value = qdr_nd.angle₃.value, qdr_nd.angle₂.value = qdr_nd.angle₄.value, and qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂ is not colinear, then qdr_nd is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₄₁₂ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcolinear : ¬ colinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂) : qdr_nd.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, ∠DAB = ∠BCD, ∠ABC = ∠CDA, and D A B is not colinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₄₁₂_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄ (QDR_nd A B C D nd).nd₁₂).value = (ANG B C D (QDR_nd A B C D nd).nd₂₃.symm (QDR_nd A B C D nd).nd₃₄).value) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.symm (QDR_nd A B C D nd).nd₂₃).value = (ANG C D A (QDR_nd A B C D nd).nd₃₄.symm (QDR_nd A B C D nd).nd₁₄.symm).value) (notcolinear : ¬ colinear D A B) : (QDR_nd A B C D nd).IsParallelogram_nd := is_prg_nd_of_eq_angle_value_eq_angle_value_not_colinear₄₁₂ (QDR_nd A B C D nd) h₁ h₂ notcolinear

/-- Given Quadrilateral_nd qdr_nd, qdr_nd.edge_nd₁₂.length = qdr_nd.edge_nd₃₄.length, qdr_nd.edge_nd₁₄.length = qdr_nd.edge_nd₂₃.length, the signs of qdr_nd.angle₁ and qdr_nd.angle₃ are equal, then qdr_nd is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_length_eq_length_eq_angle_sign (h₁ : qdr_nd.edge_nd₁₂.length = qdr_nd.edge_nd₃₄.length) (h₂ : qdr_nd.edge_nd₁₄.length = qdr_nd.edge_nd₂₃.length) (h : (qdr_nd.angle₁.value.IsPos ∧ qdr_nd.angle₃.value.IsPos) ∨ (qdr_nd.angle₁.value.IsNeg ∧ qdr_nd.angle₃.value.IsNeg)) : qdr_nd.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, AB = CD, AD = BC, the signs of ∠DAB and ∠BCD are equal, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_length_eq_length_eq_angle_sign_variant (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG A D).length = (SEG B C).length) (h : ((ANG D A B (QDR_nd A B C D nd).nd₁₄ (QDR_nd A B C D nd).nd₁₂).value.IsPos ∧ (ANG B C D (QDR_nd A B C D nd).nd₂₃.symm (QDR_nd A B C D nd).nd₃₄).value.IsPos) ∨ ((ANG D A B (QDR_nd A B C D nd).nd₁₄ (QDR_nd A B C D nd).nd₁₂).value.IsNeg ∧ (ANG B C D (QDR_nd A B C D nd).nd₂₃.symm (QDR_nd A B C D nd).nd₃₄).value.IsNeg)) : (QDR_nd A B C D nd).IsParallelogram_nd := is_prg_nd_of_eq_length_eq_length_eq_angle_sign (QDR_nd A B C D nd) h₁ h₂ h

/-- Given Quadrilateral_nd qdr_nd, qdr_nd.edge_nd₁₂.length = qdr_nd.edge_nd₃₄.length, qdr_nd.edge_nd₁₄.length = qdr_nd.edge_nd₂₃.length, the signs of qdr_nd.angle₂ and qdr_nd.angle₄ are equal, then qdr_nd is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_length_eq_length_eq_angle_sign' (h₁ : qdr_nd.edge_nd₁₂.length = qdr_nd.edge_nd₃₄.length) (h₂ : qdr_nd.edge_nd₁₄.length = qdr_nd.edge_nd₂₃.length) (h : (qdr_nd.angle₂.value.IsPos ∧ qdr_nd.angle₄.value.IsPos) ∨ (qdr_nd.angle₂.value.IsNeg ∧ qdr_nd.angle₄.value.IsNeg)) : qdr_nd.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, AB = CD, AD = BC, the signs of ∠ABC and ∠CDA are equal, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_length_eq_length_eq_angle_sign'_variant (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG A D).length = (SEG B C).length) (h : ((ANG A B C (QDR_nd A B C D nd).nd₁₂.symm (QDR_nd A B C D nd).nd₂₃).value.IsPos ∧ (ANG C D A (QDR_nd A B C D nd).nd₃₄.symm (QDR_nd A B C D nd).nd₁₄.symm).value.IsPos) ∨ ((ANG A B C (QDR_nd A B C D nd).nd₁₂.symm (QDR_nd A B C D nd).nd₂₃).value.IsNeg ∧ (ANG C D A (QDR_nd A B C D nd).nd₃₄.symm (QDR_nd A B C D nd).nd₁₄.symm).value.IsNeg)) : (QDR_nd A B C D nd).IsParallelogram_nd := is_prg_nd_of_eq_length_eq_length_eq_angle_sign' (QDR_nd A B C D nd) h₁ h₂ h

end criteria_prg_nd_of_qdr_nd

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

-- theorem is_prg_nd_of_eq_length_eq_length (h₁ : (qdr_cvx.edge_nd₁₂).1.length = (qdr_cvx.edge_nd₃₄).1.length) (h₂ : qdr_cvx.edge_nd₁₄.1.length = qdr_cvx.edge_nd₂₃.1.length) : qdr_cvx.IsParallelogram_nd := by
--   unfold Quadrilateral_cvx.IsParallelogram_nd
--   unfold Quadrilateral_cvx.edge_nd₁₂ at h₁
--   unfold Quadrilateral_cvx.edge_nd₃₄ at h₁
--   unfold Quadrilateral_cvx.edge_nd₁₄ at h₂
--   unfold Quadrilateral_cvx.edge_nd₂₃ at h₂
--   have prep₁: (qdr_cvx.triangle₁).1.edge₁ = SEG_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.nd₁₂ := rfl
--   have prep₂: (qdr_cvx.triangle₃).1.edge₁ = SEG_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.nd₃₄ := rfl
--   have t₁: (qdr_cvx.triangle₁).1.edge₁.length = (qdr_cvx.triangle₃).1.edge₁.length := by
--     rw [prep₁, prep₂]
--     exact h₁
--   have prep₃: (qdr_cvx.triangle₁).1.edge₂.length = (SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.nd₂₄).1.length := rfl
--   have prep₄: (qdr_cvx.triangle₃).1.edge₂.length = (SEG_nd qdr_cvx.point₄ qdr_cvx.point₂ qdr_cvx.nd₂₄.symm).1.length := rfl
--   have prep₅: (SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.nd₂₄).1.length = (SEG_nd qdr_cvx.point₄ qdr_cvx.point₂ qdr_cvx.nd₂₄.symm).1.length := by
--     apply SegND.length_of_rev_eq_length.symm
--   have prep₈: (SEG_nd qdr_cvx.point₁ qdr_cvx.point₄ qdr_cvx.nd₁₄).1.length = (SEG_nd qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.nd₁₄.symm).1.length := by
--     apply SegND.length_of_rev_eq_length.symm
--   have t₂: (qdr_cvx.triangle₁).1.edge₂.length = (qdr_cvx.triangle₃).1.edge₂.length := by
--     rw [prep₃, prep₄]
--     exact prep₅
--   have prep₆: (qdr_cvx.triangle₁).1.edge₃ = SEG_nd qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.nd₁₄.symm := rfl
--   have prep₇: (qdr_cvx.triangle₃).1.edge₃ = SEG_nd qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.nd₂₃ := rfl
--   have t₃: (qdr_cvx.triangle₁).1.edge₃.length = (qdr_cvx.triangle₃).1.edge₃.length := by
--     rw [prep₆, prep₇, prep₈.symm]
--     exact h₂
--   have u: qdr_cvx.triangle₁ ≅ qdr_cvx.triangle₃ := (Triangle_nd.congr_of_SSS_of_eq_orientation t₁ t₂ t₃ qdr_cvx.cclock_eq)
--   -- have A: qdr_cvx.triangle₁.1.is_nd ∧ qdr_cvx.triangle₃.1.is_nd := by
--   --     constructor
--   --     apply qdr_cvx.triangle₁.2
--   --     apply qdr_cvx.triangle₃.2
--   have prepa₁: qdr_cvx.triangle₁.angle₁.value = qdr_cvx.triangle₃.angle₁.value := by exact u.4

--   have prepa₂: qdr_cvx.triangle₁.angle₃.value = qdr_cvx.triangle₃.angle₃.value := by exact u.6
--   -- have rex: qdr_cvx.diag_nd₂₄.toRay.toDir = - (qdr_cvx.diag_nd₂₄).toRay.reverse.toDir := by
--   --   exact neg_eq_iff_eq_neg.mp rfl
--   have J: qdr_cvx.triangle₁.angle₁.end_ray = qdr_cvx.diag_nd₂₄.reverse.toRay := by rfl
--   have K: qdr_cvx.triangle₁.angle₃.start_ray = qdr_cvx.diag_nd₂₄.toRay := by rfl
--   have Q: qdr_cvx.triangle₃.angle₁.end_ray = qdr_cvx.diag_nd₂₄.toRay := by rfl
--   have joker: qdr_cvx.triangle₃.angle₃.start_ray = qdr_cvx.diag_nd₂₄.reverse.toRay := by rfl
--   have prepa₃: qdr_cvx.triangle₁.angle₃.start_ray.toDir = qdr_cvx.triangle₃.angle₃.start_ray.reverse.toDir := by
--     have JOKER: qdr_cvx.diag_nd₂₄.reverse.toRay.reverse.toDir = - qdr_cvx.diag_nd₂₄.reverse.toRay.toDir := qdr_cvx.diag_nd₂₄.reverse.toRay.toDir_of_rev_eq_neg_toDir
--     have SpadeA: qdr_cvx.diag_nd₂₄.reverse.toRay.toDir = - qdr_cvx.diag_nd₂₄.toRay.toDir := qdr_cvx.diag_nd₂₄.toDir_of_rev_eq_neg_toDir
--     rw [K, joker, JOKER, SpadeA]
--     simp only [neg_neg]
--   have prepa₄: qdr_cvx.triangle₁.angle₁.end_ray.toDir = qdr_cvx.triangle₃.angle₁.end_ray.reverse.toDir := by
--     have JOKER: qdr_cvx.diag_nd₂₄.reverse.toRay.toDir = - qdr_cvx.diag_nd₂₄.toRay.toDir := qdr_cvx.diag_nd₂₄.toDir_of_rev_eq_neg_toDir
--     have SpadeA: qdr_cvx.diag_nd₂₄.toRay.reverse.toDir = -qdr_cvx.diag_nd₂₄.toRay.toDir := qdr_cvx.diag_nd₂₄.toRay.toDir_of_rev_eq_neg_toDir
--     rw [J, Q, JOKER, SpadeA]
--   have near₁: qdr_cvx.triangle₁.angle₁.start_ray.toDir = - qdr_cvx.triangle₃.angle₁.start_ray.toDir := by
--     have prepar: qdr_cvx.triangle₁.angle₁.start_ray.toDir = qdr_cvx.triangle₃.angle₁.start_ray.reverse.toDir := start_ray_toDir_rev_toDir_of_ang_rev_ang prepa₄ prepa₁
--     have prepar': qdr_cvx.triangle₃.angle₁.start_ray.reverse.toDir = - qdr_cvx.triangle₃.angle₁.start_ray.toDir := qdr_cvx.triangle₃.angle₁.start_ray.toDir_of_rev_eq_neg_toDir
--     rw [prepar, prepar']
--   have near₂: qdr_cvx.triangle₁.angle₃.end_ray.toDir = - qdr_cvx.triangle₃.angle₃.end_ray.toDir := by
--     have prepar: qdr_cvx.triangle₁.angle₃.end_ray.toDir = qdr_cvx.triangle₃.angle₃.end_ray.reverse.toDir := end_ray_toDir_rev_toDir_of_ang_rev_ang prepa₃ prepa₂
--     have prepar': qdr_cvx.triangle₃.angle₃.end_ray.reverse.toDir = - qdr_cvx.triangle₃.angle₃.end_ray.toDir := qdr_cvx.triangle₃.angle₃.end_ray.toDir_of_rev_eq_neg_toDir
--     rw [prepar, prepar']
--   have very_near₁: qdr_cvx.triangle₁.angle₁.start_ray.toProj = qdr_cvx.triangle₃.angle₁.start_ray.toProj := by
--     apply Dir.toProj_eq_toProj_iff.mpr
--     right
--     exact near₁
--   have very_close₁: qdr_cvx.triangle₁.angle₁.start_ray ∥ qdr_cvx.triangle₃.angle₁.start_ray := very_near₁
--   have very_near₂: qdr_cvx.triangle₁.angle₃.end_ray.toProj = qdr_cvx.triangle₃.angle₃.end_ray.toProj := by
--     apply Dir.toProj_eq_toProj_iff.mpr
--     right
--     exact near₂
--   have very_close₂: qdr_cvx.triangle₁.angle₃.end_ray ∥ qdr_cvx.triangle₃.angle₃.end_ray := very_near₂
--   have close₁: qdr_cvx.edge_nd₁₄.toProj = qdr_cvx.triangle₁.angle₁.start_ray.toProj := by
--     have third: qdr_cvx.edge_nd₁₄.reverse.toProj = qdr_cvx.edge_nd₁₄.toProj := qdr_cvx.edge_nd₁₄.toProj_of_rev_eq_toProj
--     exact id third.symm
--   have close₂: qdr_cvx.edge_nd₂₃.toProj = qdr_cvx.triangle₃.angle₁.start_ray.toProj := by rfl
--   have close₃: qdr_cvx.edge_nd₁₂.toProj = qdr_cvx.triangle₁.angle₃.end_ray.toProj := by
--     have last: qdr_cvx.edge_nd₁₂.reverse.toRay = qdr_cvx.triangle₁.angle₃.end_ray := by rfl
--     have second: qdr_cvx.edge_nd₁₂.reverse.toProj = qdr_cvx.triangle₁.angle₃.end_ray.toProj := by rfl
--     have third: qdr_cvx.edge_nd₁₂.reverse.toProj = qdr_cvx.edge_nd₁₂.toProj := qdr_cvx.edge_nd₁₂.toProj_of_rev_eq_toProj
--     rw [third.symm, second, last.symm]
--   have close₄: qdr_cvx.edge_nd₃₄.toProj = qdr_cvx.triangle₃.angle₃.end_ray.toProj := by
--     have last: qdr_cvx.edge_nd₃₄.reverse.toRay = qdr_cvx.triangle₃.angle₃.end_ray := by rfl
--     have second: qdr_cvx.edge_nd₃₄.reverse.toProj = qdr_cvx.triangle₃.angle₃.end_ray.toProj := by rfl
--     have third: qdr_cvx.edge_nd₃₄.reverse.toProj = qdr_cvx.edge_nd₃₄.toProj := qdr_cvx.edge_nd₃₄.toProj_of_rev_eq_toProj
--     rw [third.symm, second, last.symm]
--   have win₁: qdr_cvx.edge_nd₁₂.toProj = qdr_cvx.edge_nd₃₄.toProj := by
--     rw [close₃, close₄]
--     exact very_close₂
--   have win₂: qdr_cvx.edge_nd₁₄.toProj = qdr_cvx.edge_nd₂₃.toProj := by
--     rw [close₁, close₂]
--     exact very_close₁
--   exact ⟨win₁, win₂⟩

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AB = CD and AD = BC, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_eq_length_eq_length_variant (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG A D).length = (SEG B C).length) : (Quadrilateral_nd.mk_is_nd nd) IsParallelogram_nd := by
  sorry

/-- Given Quadrilateral_cvx qdr_cvx, and qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄ and (qdr_cvx.edge_nd₁₂).1.length = (qdr_cvx.edge_nd₃₄).1.length, qdr_cvx is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_para_eq_length (h₁ : qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) (h₂ : qdr_cvx.edge_nd₁₂.1.length = qdr_cvx.edge_nd₃₄.1.length) : qdr_cvx.IsParallelogram_nd := by sorry

-- theorem is_prg_nd_of_para_eq_length (h₁ : qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) (h₂ : qdr_cvx.edge_nd₁₂.1.length = qdr_cvx.edge_nd₃₄.1.length) : qdr_cvx.IsParallelogram_nd := by
--   unfold Quadrilateral_cvx.IsParallelogram_nd
--   unfold Quadrilateral_cvx.edge_nd₁₂
--   unfold Quadrilateral_cvx.edge_nd₃₄
--   unfold Quadrilateral_cvx.edge_nd₁₄
--   unfold Quadrilateral_cvx.edge_nd₂₃
--   unfold parallel at h₁
--   have h: qdr_cvx.edge_nd₁₂.toDir = qdr_cvx.edge_nd₃₄.toDir ∨ qdr_cvx.edge_nd₁₂.toDir = - qdr_cvx.edge_nd₃₄.toDir := by
--     apply Dir.toProj_eq_toProj_iff.mp
--     exact h₁
--   have diag_ng_para: ¬ qdr_cvx.diag_nd₁₃.toProj = qdr_cvx.diag_nd₂₄.toProj := qdr_cvx.diag_not_para
--   rcases h with case_not_convex | case_convex
--   -- Case that is not convex, goal is prove contra
--   have angle₁_eq_angle₄: (ANG qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.nd₃₄.symm qdr_cvx.nd₁₄.symm).value = (ANG qdr_cvx.point₂ qdr_cvx.point₁ qdr_cvx.point₄ qdr_cvx.nd₁₂ qdr_cvx.nd₁₄).value := by
--     apply ang_eq_ang_of_toDir_rev_toDir
--     have ray₁₂_toDir_eq_Seg_nd₁₂_toDir: qdr_cvx.edge_nd₁₂.toDir = (ANG qdr_cvx.point₂ qdr_cvx.point₁ qdr_cvx.point₄ qdr_cvx.nd₁₂ qdr_cvx.nd₁₄).start_ray.toDir := by rfl
--     have ray₄₃_toDir_eq_Seg_nd₃₄_rev_toDir: qdr_cvx.edge_nd₃₄.reverse.toDir = (ANG qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.nd₃₄.symm qdr_cvx.nd₁₄.symm).start_ray.toDir := by rfl
--     have Seg_nd₄₃_toDir_neg_Seg_nd₃₄_rev_toDir: qdr_cvx.edge_nd₃₄.reverse.toDir = - qdr_cvx.edge_nd₃₄.toDir := by apply SegND.toDir_of_rev_eq_neg_toDir
--     rw [ray₁₂_toDir_eq_Seg_nd₁₂_toDir.symm, ray₄₃_toDir_eq_Seg_nd₃₄_rev_toDir.symm, Seg_nd₄₃_toDir_neg_Seg_nd₃₄_rev_toDir, case_not_convex]
--     exact qdr_cvx.edge_nd₁₄.toDir_of_rev_eq_neg_toDir
--   have IsCongrTo₁₄: TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁ IsCongrTo TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄ := by
--     have edge₂_eq: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).1.edge₂.length = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).1.edge₂.length := by apply length_of_rev_eq_length'
--     have edge₃_eq: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).1.edge₃.length = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).1.edge₃.length := by
--       have eq_length: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).1.edge₃.length = qdr_cvx.edge_nd₃₄.length := by apply length_of_rev_eq_length'
--       rw [eq_length]
--       exact h₂.symm
--     apply Triangle_nd.congr_of_SAS edge₂_eq angle₁_eq_angle₄ edge₃_eq
--   unfold Triangle_nd.IsCongr at IsCongrTo₁₄
--   have A: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).1.IsND ∧ (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).1.IsND := by
--       constructor
--       apply qdr_cvx.not_colinear₄₃₁
--       apply qdr_cvx.not_colinear₁₂₄
--   -- Use IsCongrTo to prove angle eq
--   have prepa₁: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).angle₃.value = (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.value := by
--     rcases IsCongrTo₁₄ with ⟨_, _, _, _, _, propf⟩
--     exact propf.symm
--   -- Use angle_eq to prove two diag para.
--   have prepa₂: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.start_ray.reverse.toDir = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).angle₃.start_ray.toDir := by
--     have prepaA: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.start_ray.reverse.toDir = - (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.start_ray.toDir := (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.start_ray.toDir_of_rev_eq_neg_toDir
--     have prepaB: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.start_ray.toDir = qdr_cvx.edge_nd₁₄.toDir := by rfl
--     have prepaC: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).angle₃.start_ray.toDir = qdr_cvx.edge_nd₁₄.reverse.toDir := by rfl
--     have prepaD: qdr_cvx.edge_nd₁₄.reverse.toDir = - qdr_cvx.edge_nd₁₄.toDir := qdr_cvx.edge_nd₁₄.toDir_of_rev_eq_neg_toDir
--     rw [prepaA, prepaB, prepaC, prepaD]
--   have prepa₃: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.end_ray.reverse.toDir = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).angle₃.end_ray.toDir := (end_ray_toDir_rev_toDir_of_ang_rev_ang prepa₂.symm prepa₁).symm
--   have prepa₄: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.end_ray.reverse.toDir = - (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.end_ray.toDir := by
--     apply (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.end_ray.toDir_of_rev_eq_neg_toDir
--   rw [prepa₄] at prepa₃
--   have very_nr₂: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.end_ray.toProj = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).angle₃.end_ray.toProj := by
--     apply Dir.toProj_eq_toProj_iff.mpr
--     right
--     exact neg_eq_iff_eq_neg.mp prepa₃
--   have prepa₅: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.end_ray.toProj = qdr_cvx.diag_nd₁₃.toProj := by rfl
--   have prepa₆: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).angle₃.end_ray.toProj = qdr_cvx.diag_nd₂₄.reverse.toProj := by rfl
--   have prepa₇: qdr_cvx.diag_nd₂₄.reverse.toProj = qdr_cvx.diag_nd₂₄.toProj := qdr_cvx.diag_nd₂₄.toProj_of_rev_eq_toProj
--   rw [prepa₇, very_nr₂.symm, prepa₅] at prepa₆
--   -- Two diags para, not allowed in a qdr_cvx
--   contradiction
--   -- Case that is convex, using para to prove angle eq
--   have angle₁_eq_angle₃: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).angle₁.value = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₁.value := by
--     apply ang_eq_ang_of_toDir_rev_toDir
--     exact case_convex
--     have K₁: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).angle₁.end_ray.toDir = qdr_cvx.diag_nd₁₃.toDir := by rfl
--     have K₂: (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₁.end_ray.toDir = qdr_cvx.diag_nd₁₃.reverse.toDir := by rfl
--     have K₃: qdr_cvx.diag_nd₁₃.reverse.toDir = - qdr_cvx.diag_nd₁₃.toDir := qdr_cvx.diag_nd₁₃.toDir_of_rev_eq_neg_toDir
--     rw [K₁.symm, K₂.symm] at K₃
--     exact neg_eq_iff_eq_neg.mp (id K₃.symm)
--   -- Prove IsCongrTo
--   have prepar₁: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).1.edge₂.length = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).1.edge₂.length := length_of_rev_eq_length'
--   have prepar₂: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).1.edge₃.length = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).1.edge₃.length := h₂
--   have IsCongrTo₁₃: TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃ IsCongrTo TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁ := Triangle_nd.congr_of_SAS prepar₁ angle₁_eq_angle₃ prepar₂
--   unfold Triangle_nd.IsCongr at IsCongrTo₁₃
--   have A: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).1.IsND ∧ (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).1.IsND := by
--       constructor
--       apply (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).2
--       apply (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).2
--   -- Use IsCongrTo to prove angle eq
--   have pr₁: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).angle₃.value = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.value := by
--     rcases IsCongrTo₁₃ with ⟨_, _, _, _, _, propf⟩
--     exact propf
--   -- Use angle eq to prove para, hope qdr_cvx becomes prg
--   have pr₂: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).angle₃.start_ray.toDir = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.start_ray.reverse.toDir := by
--     have K₄: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).angle₃.start_ray.toDir = qdr_cvx.diag_nd₁₃.reverse.toDir := by rfl
--     have K₅: (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.start_ray.toDir = qdr_cvx.diag_nd₁₃.toDir := by rfl
--     have K₆: qdr_cvx.diag_nd₁₃.reverse.toDir = - qdr_cvx.diag_nd₁₃.toDir := qdr_cvx.diag_nd₁₃.toDir_of_rev_eq_neg_toDir
--     rw [K₄.symm, K₅.symm] at K₆
--     exact K₆
--   have near: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).angle₃.end_ray.toDir = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.end_ray.reverse.toDir := end_ray_toDir_rev_toDir_of_ang_rev_ang pr₂ pr₁
--   have J₁: (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.end_ray.reverse.toDir = - (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.end_ray.toDir := (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.end_ray.toDir_of_rev_eq_neg_toDir
--   have J₂: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).angle₃.end_ray.toDir = qdr_cvx.edge_nd₂₃.reverse.toDir := by rfl
--   have J₃: (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.end_ray.toDir = qdr_cvx.edge_nd₁₄.toDir := by rfl
--   have J₄: qdr_cvx.edge_nd₂₃.reverse.toDir = - qdr_cvx.edge_nd₂₃.toDir := qdr_cvx.edge_nd₂₃.toDir_of_rev_eq_neg_toDir
--   rw [J₁, J₂, J₃, J₄] at near
--   simp only [neg_inj] at near
--   have close: qdr_cvx.edge_nd₂₃.toProj = qdr_cvx.edge_nd₁₄.toProj := by
--     apply Dir.toProj_eq_toProj_iff.mpr
--     left
--     exact near
--   constructor
--   exact h₁
--   exact close.symm
--   -- Done!

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AB ∥ CD and AB = CD, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_para_eq_length_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄)) (h₂ : (SEG A B).length = (SEG C D).length) : (Quadrilateral_nd.mk_is_nd nd) IsParallelogram_nd := by
  sorry

/-- Given Quadrilateral_cvx qdr_cvx, and qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃ and (qdr_cvx.edge_nd₁₄).1.length = (qdr_cvx.edge_nd₂₃).1.length, qdr_cvx is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_para_eq_length' (h₁ : qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃) (h₂ : qdr_cvx.edge_nd₁₄.1.length = qdr_cvx.edge_nd₂₃.1.length) : qdr_cvx.IsParallelogram_nd := by
  sorry

-- theorem is_prg_nd_of_para_eq_length' (h₁ : qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃) (h₂ : qdr_cvx.edge_nd₁₄.1.length = qdr_cvx.edge_nd₂₃.1.length) : qdr_cvx.IsParallelogram_nd := by
--   let permute_convex := Quadrilateral_cvx.mk_is_convex qdr_cvx.permute_is_convex
--   have K₁: permute_convex.edge_nd₁₂.toProj = qdr_cvx.edge_nd₂₃.toProj := by rfl
--   have K₂: permute_convex.edge_nd₁₂.1.length = qdr_cvx.edge_nd₂₃.1.length := by rfl
--   have j₂: permute_convex.edge_nd₃₄ = qdr_cvx.edge_nd₁₄.reverse := by rfl
--   have K₃: permute_convex.edge_nd₃₄.toProj = qdr_cvx.edge_nd₁₄.toProj := by
--     rw [j₂]
--     apply SegND.toProj_of_rev_eq_toProj
--   have K₄: permute_convex.edge_nd₃₄.1.length = qdr_cvx.edge_nd₁₄.1.length := by
--     rw [j₂]
--     apply SegND.length_of_rev_eq_length
--   have H₁: permute_convex.edge_nd₁₂.toProj = permute_convex.edge_nd₃₄.toProj := by
--     rw [K₁, K₃]
--     unfold parallel at h₁
--     exact h₁.symm
--   have H₂: permute_convex.edge_nd₁₂.1.length = permute_convex.edge_nd₃₄.1.length := by
--     rw [K₂, K₄]
--     exact h₂.symm
--   have H: permute_convex.IsParallelogram_nd := is_prg_nd_of_para_eq_length permute_convex H₁ H₂
--   unfold Quadrilateral_cvx.IsParallelogram_nd
--   unfold Quadrilateral_cvx.IsParallelogram_nd at H
--   rcases H with ⟨_,b⟩
--   constructor
--   have P₁: permute_convex.edge_nd₂₃ = qdr_cvx.edge_nd₃₄ := by rfl
--   have p₂: permute_convex.edge_nd₁₄ = qdr_cvx.edge_nd₁₂.reverse := by rfl
--   have p₃: permute_convex.edge_nd₃₄ = qdr_cvx.edge_nd₁₄.reverse := by rfl
--   have P₂: permute_convex.edge_nd₁₄.reverse.toProj = permute_convex.edge_nd₁₄.toProj := by apply permute_convex.edge_nd₁₄.toProj_of_rev_eq_toProj
--   rw [P₁, p₂] at b
--   have b': qdr_cvx.edge_nd₃₄∥qdr_cvx.edge_nd₁₂.reverse := b.symm
--   apply SegND.para_rev_of_para at b'
--   -- constructor
--   exact b'.symm
--   exact h₁

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
  dsimp
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
