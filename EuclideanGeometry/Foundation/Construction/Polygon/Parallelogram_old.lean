/-
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

While we have great benifit using QDR_cvx as the basis of discussion of parallelogram_nd (as we will show later, all parallelogram_nds are quadrilateral_cvxs), we do have practical difficulty in proving a quadrilateral being convex. Also, it is important (but not essential, as we will see) to keep the definition of parallelogram and parallelogram_nd being the same form (we will use this 'standardised' method as a theorem later on). So we would like to switch our attention to another type of quadrilaterals: QuadrilateralNDs, about which we can discuss angles, but general enough to include the degenerating cases.

In this section we define two types of parallelogram. 'parallel_nd' deals with those quadrilaterals we commomly call parallelogram (convex), and 'parallel' with more general cases (we permite degenerate cases). As the concept of convex is hard to deal with, we therefore won't use it to define directly. Instead, we will start with GPt, where all sets of 3 points are not collinear.

-/

@[pp_dot]
structure Quadrilateral_nd.Parallelogram_GPt {P : Type*} [EuclideanPlane P] (qdr_nd : Quadrilateral_nd P) : Prop where
  not_collinear₁₂₃: ( ¬ Collinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃)
  not_collinear₂₃₄: ( ¬ Collinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄)
  not_collinear₃₄₁: ( ¬ Collinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁)
  not_collinear₄₁₂: ( ¬ Collinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂)

/-- A quadrilateral is called parallelogram if VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃.-/
@[pp_dot]
def Quadrilateral.IsParallelogram {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃

/-- A quadrilateral satisfies IsParallelogram_para if two sets of opposite sides are parallel respectively. -/
@[pp_dot]
def QuadrilateralND.IsParallelogram_para {P : Type*} [EuclideanPlane P] (qdr_nd : QuadrilateralND P) : Prop := ( qdr_nd.edgeND₁₂ ∥ qdr_nd.edgeND₃₄) ∧ (qdr_nd.edgeND₁₄ ∥ qdr_nd.edgeND₂₃)

/-- A quadrilateral satisfies IsParallelogram_nd if it satisfies both IsParallelogram_para and Parallelogram_GPt. It is now what we commonly call parallelogram.-/
@[pp_dot]
def QuadrilateralND.IsParallelogram_nd {P : Type*} [EuclideanPlane P] (qdr_nd : QuadrilateralND P) : Prop := qdr_nd.IsParallelogram_para ∧ qdr_nd.Parallelogram_non_triv

@[pp_dot]
def Quadrilateral.IsParallelogram_nd {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases h : qdr.IsND
  · exact (QuadrilateralND.mk_nd h).IsParallelogram_nd
  · exact False

scoped postfix : 50 "IsParallelogram_GPt" => Quadrilateral_nd.Parallelogram_GPt
scoped postfix : 50 "IsParallelogram" => Quadrilateral.IsParallelogram
scoped postfix : 50 "IsParallelogram_para" => QuadrilateralND.IsParallelogram_para
scoped postfix : 50 "IsParallelogram_nd" => QuadrilateralND.IsParallelogram_nd

/-- We define parallelogram as a structure.-/
@[ext]
structure Parallelogram (P : Type*) [EuclideanPlane P] extends Quadrilateral P where
  is_parallelogram : toQuadrilateral IsParallelogram

/-- We define parallelogram_nd as a structure.-/
@[ext]
structure Parallelogram_nd (P : Type*) [EuclideanPlane P] extends Quadrilateral_nd P, Parallelogram P where
  is_parallelogram_para : toQuadrilateral_nd IsParallelogram_para
  is_parallelogram_GPt : toQuadrilateral_nd IsParallelogram_GPt

/-- We would also like to introduce a shortcut in proving statements concerning parallelograms - that is perm, the same technique used in Quadrilateral.lean. If qdr IsParallelogram, then its perm also IsParallelogram. -/
theorem qdr_is_parallelogram_perm_iff (P : Type*) [EuclideanPlane P] (qdr : Quadrilateral P) :(qdr.IsParallelogram) ↔ ((qdr.perm).IsParallelogram) := by
  sorry

/-- If qdr IsParallelogram_nd, then its perm also IsParallelogram_nd. -/
theorem qdr_is_parallelogram_nd_perm_iff (P : Type*) [EuclideanPlane P] (qdr : Quadrilateral P) :(qdr.IsParallelogram_nd) ↔ ((qdr.perm).IsParallelogram_nd) := by
  sorry

/-- If qdr_nd IsParallelogram, then its perm also IsParallelogram. -/
theorem qdr_nd_is_parallelogram_perm_iff (P : Type*) [EuclideanPlane P] (qdr_nd : QuadrilateralND P) :(qdr_nd.IsParallelogram) ↔ ((qdr_nd.perm).IsParallelogram) := by sorry

/-- If qdr_nd IsParallelogram_nd, then its perm also IsParallelogram. -/
theorem qdr_nd_is_parallelogram_nd_perm_iff (P : Type*) [EuclideanPlane P] (qdr_nd : QuadrilateralND P) :(qdr_nd.IsParallelogram_nd) ↔ ((qdr_nd.perm).IsParallelogram_nd) := by
  constructor
  intro h
  unfold QuadrilateralND.IsParallelogram_nd
  unfold QuadrilateralND.IsParallelogram_nd at h
  rcases h with ⟨a,b⟩
  unfold QuadrilateralND.IsParallelogram_para
  unfold QuadrilateralND.IsParallelogram_para at a
  rcases a with ⟨k,q⟩
  unfold parallel
  unfold parallel at k q
  have K₁: qdr_nd.perm.edgeND₁₂.toProj = qdr_nd.edgeND₂₃.toProj := by rfl
  have K₂: qdr_nd.perm.edgeND₃₄.toProj = qdr_nd.edgeND₁₄.reverse.toProj := by rfl
  have K₃: qdr_nd.edgeND₁₄.reverse.toProj = qdr_nd.edgeND₁₄.toProj := by apply SegND.toProj_of_rev_eq_toProj
  rw [K₃] at K₂
  have K₄: qdr_nd.perm.edgeND₁₂.toProj = qdr_nd.perm.edgeND₃₄.toProj := by
    rw [K₁, K₂]
    exact q.symm
  have K₅: qdr_nd.perm.edgeND₁₄.toProj = qdr_nd.edgeND₁₂.reverse.toProj := by rfl
  have K₆: qdr_nd.edgeND₁₂.reverse.toProj = qdr_nd.edgeND₁₂.toProj := by apply SegND.toProj_of_rev_eq_toProj
  rw [K₆] at K₅
  have K₇: qdr_nd.perm.edgeND₂₃.toProj = qdr_nd.edgeND₃₄.toProj := by rfl
  have K₈: qdr_nd.perm.edgeND₁₄.toProj = qdr_nd.perm.edgeND₂₃.toProj := by
    rw [K₅, K₇]
    exact k
  constructor
  constructor
  exact K₄
  exact K₈
  rcases b with ⟨x,y,z,t⟩
  constructor
  exact y
  exact z
  exact t
  exact x
  intro h
  unfold QuadrilateralND.IsParallelogram_nd
  unfold QuadrilateralND.IsParallelogram_nd at h
  rcases h with ⟨a,b⟩
  unfold QuadrilateralND.IsParallelogram_para
  unfold QuadrilateralND.IsParallelogram_para at a
  rcases a with ⟨k,q⟩
  unfold parallel
  unfold parallel at k q
  have K₂: qdr_nd.perm.edgeND₃₄.toProj = qdr_nd.edgeND₁₄.reverse.toProj := by rfl
  have K₃: qdr_nd.edgeND₁₄.reverse.toProj = qdr_nd.edgeND₁₄.toProj := by apply SegND.toProj_of_rev_eq_toProj
  rw [K₃] at K₂
  have K₅: qdr_nd.perm.edgeND₁₄.toProj = qdr_nd.edgeND₁₂.reverse.toProj := by rfl
  have K₆: qdr_nd.edgeND₁₂.reverse.toProj = qdr_nd.edgeND₁₂.toProj := by apply SegND.toProj_of_rev_eq_toProj
  rw [K₆] at K₅
  have K₇: qdr_nd.perm.edgeND₂₃.toProj = qdr_nd.edgeND₃₄.toProj := by rfl
  constructor
  constructor
  exact (Eq.congr (id K₅.symm) K₇).mpr q
  exact (Eq.congr (id K₂.symm) k).mpr rfl
  rcases b with ⟨x,y,z,t⟩
  constructor
  exact t
  exact x
  exact y
  exact z

/-- If prg IsParallelogram_nd, then its perm also IsParallelogram_nd. -/
theorem prg_is_parallelogram_nd_perm_iff (P : Type*) [EuclideanPlane P] (prg : Parallelogram P) :(prg.IsParallelogram_nd) ↔ ((prg.perm).IsParallelogram_nd) := by
  sorry

/-- If qdr_nd is non-degenerate and is a parallelogram, and its 1st, 2nd and 3rd points are not collinear, then qdr_nd is a parallelogram_nd.-/
theorem Parallelogram_not_collinear₁₂₃ (P : Type*) [EuclideanPlane P] (qdr_nd : QuadrilateralND P) (para: qdr_nd.1 IsParallelogram) (h: ¬ Collinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃) : qdr_nd IsParallelogram_nd := by

   have hba : qdr_nd.point₂ ≠ qdr_nd.point₁ := by
     unfold collinear at h
     exact (ne_of_not_collinear h).2.2
   have hbc : qdr_nd.point₂ ≠ qdr_nd.point₃ :=by
     exact (ne_of_not_collinear h).1.symm
   have hca: qdr_nd.point₃ ≠ qdr_nd.point₁ :=by
     exact (ne_of_not_collinear h).2.1.symm
   have had : qdr_nd.point₁ ≠ qdr_nd.point₄ := by
     by_contra k
     unfold Quadrilateral.IsParallelogram at para
     have o : VEC qdr_nd.point₁ qdr_nd.point₂ = VEC qdr_nd.point₁ qdr_nd.point₃ := by
       simp only [para, k.symm]
     rw [EuclidGeom.Vec.mkPtPt] at o
     rw [EuclidGeom.Vec.mkPtPt] at o
     have oo : qdr_nd.point₂= qdr_nd.point₃ := by
       exact vsub_left_cancel o
     exact hbc oo

   have hbd : qdr_nd.point₂ ≠ qdr_nd.point₄ := by
     by_contra k₁
     unfold Quadrilateral.IsParallelogram at para
     have o: VEC qdr_nd.point₁ qdr_nd.point₂ = VEC qdr_nd.point₂ qdr_nd.point₃ := by
       simp[para,k₁.symm]
     have oo: collinear qdr_nd.point₂ qdr_nd.point₁ qdr_nd.point₃ := by
       have ooo:∃ t : ℝ,VEC qdr_nd.point₂ qdr_nd.point₃ = t • VEC qdr_nd.point₂ qdr_nd.point₁ := by
         use -1
         simp only [neg_smul, one_smul, neg_vec]
         rw[o]
       exact collinear_of_vec_eq_smul_vec' ooo
     simp only [Collinear.perm₂₁₃ oo, not_true_eq_false] at h
   have hcd : qdr_nd.point₃ ≠ qdr_nd.point₄ := by
     by_contra k₂
     have k₂₂ : VEC qdr_nd.point₄ qdr_nd.point₃=0 := by
       simp only [k₂, vec_same_eq_zero]
     unfold Quadrilateral.IsParallelogram at para
     have k₂₃: qdr_nd.point₁=qdr_nd.point₂ :=by
       rw [k₂₂] at para
       simp only [para, eq_iff_vec_eq_zero.mpr, vec_same_eq_zero]
     simp only [k₂₃.symm, ne_eq, not_true_eq_false] at hba
   have t : ¬ Collinear qdr_nd.point₂ qdr_nd.point₁ qdr_nd.point₃ := by
     by_contra k
     simp only [Collinear.perm₂₁₃ k, not_true_eq_false] at h
   have x : ¬ collinear_of_nd (A := qdr_nd.point₂) (B := qdr_nd.point₁) (C := qdr_nd.point₃) := by
     unfold collinear at t
     simp only [hca, hbc, hba.symm, or_self, dite_false] at t
     simp only [t, not_false_eq_true]
   have l₁ : qdr_nd.edgeND₁₂.toProj=VecND.toProj ⟨VEC qdr_nd.point₁ qdr_nd.point₂, _⟩ := by rfl
   have l₁' : qdr_nd.edgeND₁₂.toProj=VecND.toProj ⟨VEC qdr_nd.point₂ qdr_nd.point₁, ne_iff_vec_ne_zero.mp hba.symm⟩ := by
     have y₁:VecND.toProj ⟨VEC qdr_nd.point₂ qdr_nd.point₁, ne_iff_vec_ne_zero.mp hba.symm⟩=VecND.toProj ⟨VEC qdr_nd.point₁ qdr_nd.point₂, ne_iff_vec_ne_zero.mp hba⟩ := by
       have z₁: VEC qdr_nd.point₂ qdr_nd.point₁ =- VEC qdr_nd.point₁ qdr_nd.point₂ := by
         simp only [neg_vec]
       simp only [ne_eq, z₁, VecND.mk_neg', VecND.neg_toProj]
     simp only [l₁, ne_eq, y₁]
   have l₂ : qdr_nd.edgeND₂₃.toProj=VecND.toProj ⟨VEC qdr_nd.point₂ qdr_nd.point₃, _⟩ := by rfl
   have l₂' : qdr_nd.edgeND₂₃.toProj=VecND.toProj ⟨VEC qdr_nd.point₃ qdr_nd.point₂, ne_iff_vec_ne_zero.mp hbc⟩ := by
     have y₂:VecND.toProj ⟨VEC qdr_nd.point₃ qdr_nd.point₂, ne_iff_vec_ne_zero.mp hbc⟩=VecND.toProj ⟨VEC qdr_nd.point₂ qdr_nd.point₃, ne_iff_vec_ne_zero.mp hbc.symm⟩ := by
       have z₂: VEC qdr_nd.point₃ qdr_nd.point₂ =- VEC qdr_nd.point₂ qdr_nd.point₃ := by
         simp only[neg_vec]
       simp only [ne_eq, z₂, VecND.mk_neg', VecND.neg_toProj]
     simp only [l₂, ne_eq, y₂]
   have l₃ : qdr_nd.edgeND₃₄.toProj=VecND.toProj ⟨VEC qdr_nd.point₃ qdr_nd.point₄, _⟩ := by rfl
   have l₃' : qdr_nd.edgeND₃₄.toProj=VecND.toProj ⟨VEC qdr_nd.point₄ qdr_nd.point₃, ne_iff_vec_ne_zero.mp hcd⟩ := by
     have y₃:VecND.toProj ⟨VEC qdr_nd.point₄ qdr_nd.point₃, ne_iff_vec_ne_zero.mp hcd⟩=VecND.toProj ⟨VEC qdr_nd.point₃ qdr_nd.point₄, ne_iff_vec_ne_zero.mp hcd.symm⟩ := by
       have z₃: VEC qdr_nd.point₄ qdr_nd.point₃ =- VEC qdr_nd.point₃ qdr_nd.point₄ := by
         simp only [neg_vec]
       simp only [ne_eq, z₃, VecND.mk_neg', VecND.neg_toProj]
     simp only [l₃, ne_eq, y₃]
   have l₄ : qdr_nd.edgeND₁₄.toProj=VecND.toProj ⟨VEC qdr_nd.point₁ qdr_nd.point₄, _⟩ := by rfl
   have l₄' : qdr_nd.edgeND₁₄.toProj=VecND.toProj ⟨VEC qdr_nd.point₄ qdr_nd.point₁, ne_iff_vec_ne_zero.mp had⟩ := by
     have y₄:VecND.toProj ⟨VEC qdr_nd.point₄ qdr_nd.point₁, ne_iff_vec_ne_zero.mp had⟩=VecND.toProj ⟨VEC qdr_nd.point₁ qdr_nd.point₄, ne_iff_vec_ne_zero.mp had.symm⟩ := by
       have z₄: VEC qdr_nd.point₄ qdr_nd.point₁ =- VEC qdr_nd.point₁ qdr_nd.point₄ := by
         simp [neg_vec]
       simp only [ne_eq, z₄, VecND.mk_neg', VecND.neg_toProj]
     simp only [l₄, ne_eq, y₄]
   have s : ¬ qdr_nd.edgeND₁₂.toProj = qdr_nd.edgeND₂₃.toProj := by
     unfold collinear_of_nd at x
     simp only [l₁', ne_eq, l₂]
     exact x
   have v₁ : qdr_nd.edgeND₁₂.toProj = qdr_nd.edgeND₃₄.toProj := by
     unfold Quadrilateral.IsParallelogram at para
     have v₁₁₁:VecND.toProj ⟨VEC qdr_nd.point₁ qdr_nd.point₂, ne_iff_vec_ne_zero.mp hba⟩ = VecND.toProj ⟨VEC qdr_nd.point₄ qdr_nd.point₃, ne_iff_vec_ne_zero.mp hcd⟩ := by
       simp only [ne_eq, para]
     simp only [l₁, ne_eq, v₁₁₁, l₃']
   have v₁₁ : toProj qdr_nd.edgeND₁₂ = toProj qdr_nd.edgeND₃₄ := by exact v₁
   have v₂ : qdr_nd.edgeND₂₃.toProj = qdr_nd.edgeND₁₄.toProj := by
     unfold Quadrilateral.IsParallelogram at para
     have v₂₂: VEC qdr_nd.point₁ qdr_nd.point₄ = VEC qdr_nd.point₂ qdr_nd.point₃ := by
       rw [← vec_add_vec qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₄]
       rw [← vec_add_vec qdr_nd.point₂ qdr_nd.point₄ qdr_nd.point₃]
       rw [para]
       exact add_comm (VEC qdr_nd.point₄ qdr_nd.point₃) (VEC qdr_nd.point₂ qdr_nd.point₄)
     simp only [l₂, ne_eq, v₂₂, l₄]
   have v₂₁ : toProj qdr_nd.edgeND₂₃ = toProj qdr_nd.edgeND₁₄ := by exact v₂
   have s₁ : ¬ qdr_nd.edgeND₁₂.toProj = qdr_nd.edgeND₂₃.toProj := by
     by_contra k₃
     have k₃₃: collinear_of_nd (A := qdr_nd.point₂) (B := qdr_nd.point₁) (C := qdr_nd.point₃) := by
        rw[l₁',l₂] at k₃
        exact k₃
     have k₃₄: collinear qdr_nd.point₂ qdr_nd.point₁ qdr_nd.point₃ := by
       unfold collinear
       simp only [hca, hbc, hba.symm, or_self, k₃₃, dite_eq_ite, ite_self]
     simp only [k₃₄, not_true_eq_false] at t
   have s₂ : ¬ qdr_nd.edgeND₂₃.toProj = qdr_nd.edgeND₃₄.toProj := by
     rw [v₁.symm]
     by_contra k
     exact s k.symm
   have s₃ : ¬ qdr_nd.edgeND₃₄.toProj = qdr_nd.edgeND₁₄.toProj := by
     rw [v₂.symm]
     by_contra k
     exact s₂ k.symm
   have s₄ : ¬ qdr_nd.edgeND₁₄.toProj = qdr_nd.edgeND₁₂.toProj := by
     rw[v₁]
     by_contra k
     exact s₃ k.symm
   constructor
   constructor
   unfold parallel
   simp only [v₁₁]
   unfold parallel
   simp only [v₂₁]
   constructor
   simp only [h, not_false_eq_true]
   by_contra m₃
   have m₂ :  ¬ Collinear qdr_nd.point₃ qdr_nd.point₂ qdr_nd.point₄ := by
     by_contra k₁
     unfold collinear at k₁
     simp [hbd.symm,hcd,hbc] at k₁
     unfold collinear_of_nd at k₁
     have p₄:qdr_nd.edgeND₂₃.toProj = qdr_nd.edgeND₃₄.toProj  := by
       rw[l₂',l₃]
       exact k₁
     simp[p₄] at s₂
   simp [Collinear.perm₂₁₃ m₃] at m₂
   by_contra m₅
   have m₄ :  ¬ Collinear qdr_nd.point₄ qdr_nd.point₃ qdr_nd.point₁ := by
     by_contra k₂
     unfold collinear at k₂
     simp [hca.symm,hcd,had.symm] at k₂
     unfold collinear_of_nd at k₂
     have p₅:qdr_nd.edgeND₃₄.toProj = qdr_nd.edgeND₁₄.toProj := by
       rw[l₄',l₃']
       exact k₂
     simp[p₅] at s₃
   simp [Collinear.perm₂₁₃ m₅] at m₄
   by_contra m₇
   have m₆ :  ¬ Collinear qdr_nd.point₁ qdr_nd.point₄ qdr_nd.point₂ := by
     by_contra k₃
     unfold collinear at k₃
     simp [hbd,hba.symm,had.symm] at k₃
     unfold collinear_of_nd at k₃
     have p₆:qdr_nd.edgeND₁₄.toProj = qdr_nd.edgeND₁₂.toProj := by
       rw[l₄,l₁]
       exact k₃
     simp [p₆] at s₄
   simp [Collinear.perm₂₁₃ m₇] at m₆

/-- If qdr_nd is non-degenerate and is a parallelogram, and its 2nd, 3rd and 4th points are not collinear, then qdr_nd is a parallelogram_nd.-/
theorem Parallelogram_not_collinear₂₃₄ (P : Type*) [EuclideanPlane P] (qdr_nd : QuadrilateralND P) (para: qdr_nd.1 IsParallelogram) (h: ¬ Collinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) : qdr_nd IsParallelogram_nd := by
  sorry

/-- If qdr_nd is non-degenerate and is a parallelogram, and its 3rd, 4th and 1st points are not collinear, then qdr_nd is a parallelogram_nd.-/
theorem Parallelogram_not_collinear₃₄₁ (P : Type*) [EuclideanPlane P] (qdr_nd : QuadrilateralND P) (para: qdr_nd.1 IsParallelogram) (h: ¬ Collinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁) : qdr_nd IsParallelogram_nd := by
  sorry

/-- If qdr_nd is non-degenerate and is a parallelogram, and its 4th, 1st and 2nd points are not collinear, then qdr_nd is a parallelogram_nd.-/
theorem Parallelogram_not_collinear₄₁₂ (P : Type*) [EuclideanPlane P] (qdr_nd : QuadrilateralND P) (para: qdr_nd.1 IsParallelogram) (h: ¬ Collinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂) : qdr_nd IsParallelogram_nd := by
  sorry

/-- Make a parallelogram with 4 points on a plane.-/
def Parallelogram.mk_pt_pt_pt_pt {P : Type*} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D) IsParallelogram) : Parallelogram P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h

/-- Make a parallelogram_nd with 4 points on a plane, and using condition non_collinear₁₂₃.-/
def Parallelogram_nd.mk_pt_pt_pt_pt₄ {P : Type*} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsParallelogram) (non_collinear₁₂₃: ¬ Collinear A B C) : Parallelogram_nd P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h'
  nd := h
  is_parallelogram_para := sorry
  is_parallelogram_GPt := sorry

/-- Make a parallelogram_nd with 4 points on a plane, and using condition non_collinear₂₃₄.-/
def Parallelogram_nd.mk_pt_pt_pt_pt₁ {P : Type*} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsParallelogram) (non_collinear₂₃₄: ¬ Collinear B C D) : Parallelogram_nd P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h'
  nd := h
  is_parallelogram_para := sorry
  is_parallelogram_GPt := sorry

/-- Make a parallelogram_nd with 4 points on a plane, and using condition non_collinear₃₄₁.-/
def Parallelogram_nd.mk_pt_pt_pt_pt₂ {P : Type*} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsParallelogram) (non_collinear₃₄₁: ¬ Collinear C D A) : Parallelogram_nd P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h'
  nd := h
  is_parallelogram_para := sorry
  is_parallelogram_GPt := sorry

/-- Make a parallelogram_nd with 4 points on a plane, and using condition non_collinear₄₁₂.-/
def Parallelogram_nd.mk_pt_pt_pt_pt₃ {P : Type*} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsParallelogram) (non_collinear₄₁₂: ¬ Collinear D A B) : Parallelogram_nd P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h'
  nd := h
  is_parallelogram_para := sorry
  is_parallelogram_GPt := sorry

/-- Make a parallelogram_nd with 4 points on a plane.-/
def Parallelogram_nd.mk_pt_pt_pt_pt {P : Type*} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsParallelogram) (non_collinear: (QuadrilateralND.mk_nd h) IsParallelogram_non_triv) : Parallelogram_nd P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h'
  nd := h
  is_parallelogram_para := sorry
  is_parallelogram_GPt := non_collinear

scoped notation "PRG" => Parallelogram.mk_pt_pt_pt_pt
scoped notation "PRG_nd₁" => Parallelogram_nd.mk_pt_pt_pt_pt₁
scoped notation "PRG_nd₂" => Parallelogram_nd.mk_pt_pt_pt_pt₂
scoped notation "PRG_nd₃" => Parallelogram_nd.mk_pt_pt_pt_pt₃
scoped notation "PRG_nd₄" => Parallelogram_nd.mk_pt_pt_pt_pt₄
scoped notation "PRG_nd" => Parallelogram_nd.mk_pt_pt_pt_pt

/-- Make parallelogram with a quadrilateral.-/
def mk_parallelogram {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) : Parallelogram P where
  toQuadrilateral := qdr
  is_parallelogram := h

/-- Make parallelogram_nd with a quadrilateral, using condition non_collinear₁₂₃.-/
def mk_parallelogram_nd₄ {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h': qdr.IsND) (non_collinear₁₂₃: ¬ Collinear qdr.1 qdr.2 qdr.3) : Parallelogram_nd P where
  toQuadrilateral := qdr
  is_parallelogram := h
  nd := h'
  is_parallelogram_para := sorry
  is_parallelogram_GPt := sorry

/-- Make parallelogram_nd with a quadrilateral, using condition non_collinear₂₃₄.-/
def mk_parallelogram_nd₁ {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h': qdr.IsND) (non_collinear₂₃₄: ¬ Collinear qdr.2 qdr.3 qdr.4) : Parallelogram_nd P where
  toQuadrilateral := qdr
  is_parallelogram := h
  nd := h'
  is_parallelogram_para := sorry
  is_parallelogram_GPt := sorry

/-- Make parallelogram_nd with a quadrilateral, using condition non_collinear₃₁₄.-/
def mk_parallelogram_nd₂ {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h': qdr.IsND) (non_collinear₃₄₁: ¬ Collinear qdr.3 qdr.4 qdr.1) : Parallelogram_nd P where
  toQuadrilateral := qdr
  is_parallelogram := h
  nd := h'
  is_parallelogram_para := sorry
  is_parallelogram_GPt := sorry

/-- Make parallelogram_nd with a quadrilateral, using condition non_collinear₄₁₂.-/
def mk_parallelogram_nd₃ {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h': qdr.IsND) (non_collinear₄₁₂: ¬ Collinear qdr.4 qdr.1 qdr.2) : Parallelogram_nd P where
  toQuadrilateral := qdr
  is_parallelogram := h
  nd := h'
  is_parallelogram_para := sorry
  is_parallelogram_GPt := sorry

/-- Make parallelogram_nd with a quadrilateral.-/
def mk_parallelogram_nd {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h': qdr.IsND) (non_collinear: (QuadrilateralND.mk_nd h') IsParallelogram_non_triv) : Parallelogram_nd P where
  toQuadrilateral := qdr
  is_parallelogram := h
  nd := h'
  is_parallelogram_para := sorry
  is_parallelogram_GPt := sorry

/-- Here is also a quite odd definition of a quadrilateral or parallelogram being parallelogram_nd, concerning angle being positive or negative. As it may be useful when discussing cclocks, it is reserved in form of the two theorems below.-/
theorem Quadrilateral.IsParallelogram_nd_redef {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P) (h: qdr.IsND) (h': qdr IsParallelogram) (h': (((QuadrilateralND.mk_nd h).angle₁.value.IsPos ∧ (QuadrilateralND.mk_nd h).angle₃.value.IsPos) ∨ ((QuadrilateralND.mk_nd h).angle₁.value.IsNeg ∧ (QuadrilateralND.mk_nd h).angle₃.value.IsNeg) ∨ ((QuadrilateralND.mk_nd h).angle₂.value.IsPos ∧ (QuadrilateralND.mk_nd h).angle₄.value.IsPos) ∨ ((QuadrilateralND.mk_nd h).angle₂.value.IsNeg ∧ (QuadrilateralND.mk_nd h).angle₄.value.IsNeg))) : (QuadrilateralND.mk_nd h) IsParallelogram_nd := sorry

/--

One can notice that in this overall section we have already covered the route from parallelogram to parallelogram_nd. In this space here, we would like to introduce our plans for other routes and their status in the parallelogram system.

In Quadrilateral.lean we covered 3 types of common quadrilaterals: the most general qdr, more specific qdr_nd, and even better qdr_cvx. Bearing in mind that parallelogram_nds are in fact convex, we feel the need for repeating the discussion on convex quadrilaterals being parallelogram_nds (but not parallelograms, as this is pointless). This will make up the 1st part of the work below: convex quadrilaterals and parallelograms. And it will have two subsections: criteria and property. All other part shall follow in the same structure.

The route from qdr to parallelogram will not be seperated from the main discussion as there are no more to say other than the original definition. Also the route from qdr to parallelogram_nd, as this route either follows the former undiscussed route or the route from qdr to qdr_cvx, and that should be included in Quadrilateral.lean. So we are left with higher-class quadrilaterals qdr_nd, which can either be parallelogram (when collinear), or parallelogram_nd (as long as not all 4 points are collinear).

-/
@[pp_dot]
theorem Parallelogram.ParallelogramIs_nd_redef {P : Type*} [EuclideanPlane P] (qdr_para : Parallelogram P) (h': qdr_para.1.IsND) (k: ((QuadrilateralND.mk_nd h').angle₁.value.IsPos ∧ (QuadrilateralND.mk_nd h').angle₃.value.IsPos) ∨ ((QuadrilateralND.mk_nd h').angle₁.value.IsNeg ∧ (QuadrilateralND.mk_nd h').angle₃.value.IsNeg) ∨ ((QuadrilateralND.mk_nd h').angle₂.value.IsPos ∧ (QuadrilateralND.mk_nd h').angle₄.value.IsPos) ∨ ((QuadrilateralND.mk_nd h').angle₂.value.IsNeg ∧ (QuadrilateralND.mk_nd h').angle₄.value.IsNeg)) : (QuadrilateralND.mk_nd h') IsParallelogram_nd := sorry

variable {P : Type*} [EuclideanPlane P]

section criteria_prg_nd_of_qdr_nd

variable {P : Type*} [EuclideanPlane P]
variable {A B C D : P} (nd : (QDR A B C D).IsND) (cvx : (QDR A B C D).IsConvex)
variable (qdr : Quadrilateral P) (qdr_nd : QuadrilateralND P) (qdr_cvx : Quadrilateral_cvx P)

/-- Given QuadrilateralND qdr_nd, qdr_nd.edgeND₁₂ ∥ qdr_nd.edgeND₃₄, qdr_nd.edgeND₁₄ ∥ qdr_nd.edgeND₂₃, and qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃ is not collinear, then qdr_nd is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_para_para_not_collinear₁₂₃ (h₁ : qdr_nd.edgeND₁₂ ∥ qdr_nd.edgeND₃₄) (h₂ : qdr_nd.edgeND₁₄ ∥ qdr_nd.edgeND₂₃) (notcollinear : ¬ Collinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃) : qdr_nd.IsParallelogram_nd := by
  have para_vec (Vec1 Vec2 : VecND) (para : Vec1 ∥ Vec2) : ∃ c : ℝ , (Vec1 : Vec) = c • (Vec2 : Vec) := by
        apply VecND.toProj_eq_toProj_iff.mp
        exact para
  constructor
  · exact { left := h₁, right := h₂ }
  constructor
  · exact notcollinear
  · by_contra iscollinear
    rw [collinear_iff_eq_smul_vec_of_ne] at iscollinear
    rcases iscollinear with ⟨r,eq⟩
    apply notcollinear
    have para : qdr_nd.edgeND₁₄.toVecND ∥ qdr_nd.edgeND₂₃.toVecND := by sorry
    rw [collinear_iff_eq_smul_vec_of_ne]
    rcases (para_vec qdr_nd.edgeND₁₄.toVecND qdr_nd.edgeND₂₃.toVecND para) with ⟨c,eq'⟩
    have eq'' : (VEC qdr_nd.point₁ qdr_nd.point₄) = c • (VEC qdr_nd.point₂ qdr_nd.point₃) := eq'
    have l₁ : (VEC qdr_nd.point₁ qdr_nd.point₂) = (c - r) • (VEC qdr_nd.point₂ qdr_nd.point₃) := by
      rw [(vec_sub_vec' qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂).symm]
      rw [eq,eq'']
      exact (sub_smul c r (VEC qdr_nd.point₂ qdr_nd.point₃)).symm
    have l₂ : (VEC qdr_nd.point₁ qdr_nd.point₃) = (c + 1 - r) • (VEC qdr_nd.point₂ qdr_nd.point₃) := by
      rw [(vec_add_vec qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃).symm,l₁,add_sub_right_comm,add_smul (c - r) 1 (VEC qdr_nd.point₂ qdr_nd.point₃)]
      simp only [one_smul]
    have ne_zero : c - r ≠ 0 := by
      by_contra is_zero
      rw [is_zero] at l₁
      have not_nd₁₂ : qdr_nd.point₂ = qdr_nd.point₁ := by
        apply eq_iff_vec_eq_zero.mpr
        rw [l₁]
        exact zero_smul ℝ (VEC qdr_nd.point₂ qdr_nd.point₃)
      exact qdr_nd.nd₁₂.out not_nd₁₂
    use (c + 1 - r)/(c - r)
    rw [l₁,l₂,smul_smul,div_mul_cancel_of_imp]
    intro t
    by_contra
    exact ne_zero t
  · by_contra iscollinear
    apply notcollinear
    rw [collinear_iff_eq_smul_vec_of_ne]
    rw [collinear_iff_eq_smul_vec_of_ne] at iscollinear
    rcases iscollinear with ⟨r,eq⟩
    have para : qdr_nd.edgeND₃₄.toVecND ∥ qdr_nd.edgeND₁₂.toVecND := by sorry
    rcases (para_vec qdr_nd.edgeND₃₄.toVecND qdr_nd.edgeND₁₂.toVecND para) with ⟨c,eq'⟩
    have eq'' : (VEC qdr_nd.point₃ qdr_nd.point₄) = c • (VEC qdr_nd.point₁ qdr_nd.point₂) := eq'
    use - r * c
    rw [(smul_smul (- r) c (VEC qdr_nd.point₁ qdr_nd.point₂)).symm,eq''.symm,neg_smul,eq.symm]
    exact (neg_vec qdr_nd.point₃ qdr_nd.point₁).symm
  by_contra iscollinear
  apply Collinear.perm₃₂₁ at iscollinear
  rw [collinear_iff_eq_smul_vec_of_ne] at iscollinear
  rcases iscollinear with ⟨r,eq⟩
  apply notcollinear
  have para : qdr_nd.edgeND₃₄.toVecND ∥ qdr_nd.edgeND₁₂.toVecND := by sorry
  apply Collinear.perm₃₂₁
  rw [collinear_iff_eq_smul_vec_of_ne]
  rcases (para_vec qdr_nd.edgeND₃₄.toVecND qdr_nd.edgeND₁₂.toVecND para) with ⟨c,eq'⟩
  have eq'' : (VEC qdr_nd.point₃ qdr_nd.point₄) = c • (VEC qdr_nd.point₁ qdr_nd.point₂) := eq'
  have l₁ : (VEC qdr_nd.point₃ qdr_nd.point₂) = (r + c) • (VEC qdr_nd.point₁ qdr_nd.point₂) := by
    rw [(vec_sub_vec' qdr_nd.point₄ qdr_nd.point₃ qdr_nd.point₂).symm]
    rw [eq,eq'']
    rw [(neg_vec qdr_nd.point₁ qdr_nd.point₂).symm,smul_neg,sub_neg_eq_add,add_comm,(add_smul r c (VEC qdr_nd.point₁ qdr_nd.point₂)).symm]
  have l₂ : (VEC qdr_nd.point₃ qdr_nd.point₁) = (r + c - 1) • (VEC qdr_nd.point₁ qdr_nd.point₂) := by
    rw [(vec_sub_vec' qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₁).symm,l₁]
    rw [(sub_smul (r + c) 1 (VEC qdr_nd.point₁ qdr_nd.point₂))]
    simp only [one_smul]
  have ne_zero : r + c ≠ 0 := by
    by_contra is_zero
    rw [is_zero] at l₁
    have not_nd₂₃ : qdr_nd.point₂ = qdr_nd.point₃ := by
      apply eq_iff_vec_eq_zero.mpr
      rw [l₁]
      exact zero_smul ℝ (VEC qdr_nd.point₁ qdr_nd.point₂)
    exact qdr_nd.nd₂₃.out not_nd₂₃.symm
  use (r + c - 1)/(r + c)
  rw [l₁,l₂,smul_smul,div_mul_cancel_of_imp]
  intro t
  by_contra
  exact ne_zero t

/-- Given four points ABCD and Quadrilateral ABCD IsNd, AB ∥ CD, AD ∥ BC, and A B C is not collinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_para_para_not_collinear₁₂₃_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂.out) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄.out)) (h₂ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄.out) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃.out)) (notcollinear : ¬ Collinear A B C) : (QDR_nd A B C D nd).IsParallelogram_nd := qdr_nd_is_prg_nd_of_para_para_not_collinear₁₂₃ (QDR_nd A B C D nd) h₁ h₂ notcollinear

/-- Given QuadrilateralND qdr_nd, qdr_nd.edgeND₁₂ ∥ qdr_nd.edgeND₃₄, qdr_nd.edgeND₁₄ ∥ qdr_nd.edgeND₂₃, and qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄ is not collinear, then qdr_nd is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_para_para_not_collinear₂₃₄ (h₁ : qdr_nd.edgeND₁₂ ∥ qdr_nd.edgeND₃₄) (h₂ : qdr_nd.edgeND₁₄ ∥ qdr_nd.edgeND₂₃) (notcollinear : ¬ Collinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) : qdr_nd.IsParallelogram_nd := (qdr_nd_is_parallelogram_nd_perm_iff P qdr_nd).mpr (qdr_nd_is_prg_nd_of_para_para_not_collinear₁₂₃ qdr_nd.perm (SegND.para_rev_of_para h₂.symm) (SegND.para_rev_of_para h₁.symm).symm notcollinear)

/-- Given four points ABCD and Quadrilateral ABCD IsNd, AB ∥ CD, AD ∥ BC, and B C D is not collinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_para_para_not_collinear₂₃₄_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂.out) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄.out)) (h₂ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄.out) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃.out)) (notcollinear : ¬ Collinear B C D) : (QDR_nd A B C D nd).IsParallelogram_nd := qdr_nd_is_prg_nd_of_para_para_not_collinear₂₃₄ (QDR_nd A B C D nd) h₁ h₂ notcollinear

/-- Given QuadrilateralND qdr_nd, qdr_nd.edgeND₁₂ ∥ qdr_nd.edgeND₃₄, qdr_nd.edgeND₁₄ ∥ qdr_nd.edgeND₂₃, and qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁ is not collinear, then qdr_nd is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_para_para_not_collinear₃₄₁ (h₁ : qdr_nd.edgeND₁₂ ∥ qdr_nd.edgeND₃₄) (h₂ : qdr_nd.edgeND₁₄ ∥ qdr_nd.edgeND₂₃) (notcollinear : ¬ Collinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁) : qdr_nd.IsParallelogram_nd := (qdr_nd_is_parallelogram_nd_perm_iff P qdr_nd).mpr (qdr_nd_is_prg_nd_of_para_para_not_collinear₂₃₄ qdr_nd.perm (SegND.para_rev_of_para h₂.symm) (SegND.para_rev_of_para h₁.symm).symm notcollinear)

/-- Given four points ABCD and Quadrilateral ABCD IsNd, AB ∥ CD, AD ∥ BC, and C D A is not collinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_para_para_not_collinear₃₄₁_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂.out) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄.out)) (h₂ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄.out) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃.out)) (notcollinear : ¬ Collinear C D A) : (QDR_nd A B C D nd).IsParallelogram_nd := qdr_nd_is_prg_nd_of_para_para_not_collinear₃₄₁ (QDR_nd A B C D nd) h₁ h₂ notcollinear

/-- Given QuadrilateralND qdr_nd, qdr_nd.edgeND₁₂ ∥ qdr_nd.edgeND₃₄, qdr_nd.edgeND₁₄ ∥ qdr_nd.edgeND₂₃, and qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂ is not collinear, then qdr_nd is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_para_para_not_collinear₄₁₂ (h₁ : qdr_nd.edgeND₁₂ ∥ qdr_nd.edgeND₃₄) (h₂ : qdr_nd.edgeND₁₄ ∥ qdr_nd.edgeND₂₃) (notcollinear : ¬ Collinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂) : qdr_nd.IsParallelogram_nd := (qdr_nd_is_parallelogram_nd_perm_iff P qdr_nd).mpr (qdr_nd_is_prg_nd_of_para_para_not_collinear₃₄₁ qdr_nd.perm (SegND.para_rev_of_para h₂.symm) (SegND.para_rev_of_para h₁.symm).symm notcollinear)

/-- Given four points ABCD and Quadrilateral ABCD IsNd, AB ∥ CD, AD ∥ BC, and D A B is not collinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_para_para_not_collinear₄₁₂_variant (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂.out) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄.out)) (h₂ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄.out) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃.out)) (notcollinear : ¬ Collinear D A B) : (QDR_nd A B C D nd).IsParallelogram_nd := qdr_nd_is_prg_nd_of_para_para_not_collinear₄₁₂ (QDR_nd A B C D nd) h₁ h₂ notcollinear

/-- Given QuadrilateralND qdr_nd, qdr_nd.angle₁.value = qdr_nd.angle₃.value, qdr_nd.angle₂.value = qdr_nd.angle₄.value, and qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃ is not collinear, then qdr_nd is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_collinear₁₂₃ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcollinear : ¬ Collinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃) : qdr_nd.IsParallelogram_nd := by
  apply qdr_nd_is_prg_nd_of_para_para_not_collinear₁₂₃
  sorry
  sorry
  exact notcollinear

/-- Given four points ABCD and Quadrilateral ABCD IsNd, ∠DAB = ∠BCD, ∠ABC = ∠CDA, and A B C is not collinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_collinear₁₂₃_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄.out (QDR_nd A B C D nd).nd₁₂.out).value = (ANG B C D (QDR_nd A B C D nd).nd₂₃.out.symm (QDR_nd A B C D nd).nd₃₄.out).value) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.out.symm (QDR_nd A B C D nd).nd₂₃.out).value = (ANG C D A (QDR_nd A B C D nd).nd₃₄.out.symm (QDR_nd A B C D nd).nd₁₄.out.symm).value) (notcollinear : ¬ Collinear A B C) : (QDR_nd A B C D nd).IsParallelogram_nd := qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_collinear₁₂₃ (QDR_nd A B C D nd) h₁ h₂ notcollinear

/-- Given QuadrilateralND qdr_nd, qdr_nd.angle₁.value = qdr_nd.angle₃.value, qdr_nd.angle₂.value = qdr_nd.angle₄.value, and qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄ is not collinear, then qdr_nd is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_collinear₂₃₄ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcollinear : ¬ Collinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) : qdr_nd.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, ∠DAB = ∠BCD, ∠ABC = ∠CDA, and B C D is not collinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_collinear₂₃₄_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄.out (QDR_nd A B C D nd).nd₁₂.out).value = (ANG B C D (QDR_nd A B C D nd).nd₂₃.out.symm (QDR_nd A B C D nd).nd₃₄.out).value) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.out.symm (QDR_nd A B C D nd).nd₂₃.out).value = (ANG C D A (QDR_nd A B C D nd).nd₃₄.out.symm (QDR_nd A B C D nd).nd₁₄.out.symm).value) (notcollinear : ¬ Collinear B C D) : (QDR_nd A B C D nd).IsParallelogram_nd := qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_collinear₂₃₄ (QDR_nd A B C D nd) h₁ h₂ notcollinear

/-- Given QuadrilateralND qdr_nd, qdr_nd.angle₁.value = qdr_nd.angle₃.value, qdr_nd.angle₂.value = qdr_nd.angle₄.value, and qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁ is not collinear, then qdr_nd is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_collinear₃₄₁ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcollinear : ¬ Collinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁) : qdr_nd.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, ∠DAB = ∠BCD, ∠ABC = ∠CDA, and C D A is not collinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_collinear₃₄₁_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄.out (QDR_nd A B C D nd).nd₁₂.out).value = (ANG B C D (QDR_nd A B C D nd).nd₂₃.out.symm (QDR_nd A B C D nd).nd₃₄.out).value) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.out.symm (QDR_nd A B C D nd).nd₂₃.out).value = (ANG C D A (QDR_nd A B C D nd).nd₃₄.out.symm (QDR_nd A B C D nd).nd₁₄.out.symm).value) (notcollinear : ¬ Collinear C D A) : (QDR_nd A B C D nd).IsParallelogram_nd := qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_collinear₃₄₁ (QDR_nd A B C D nd) h₁ h₂ notcollinear

/-- Given QuadrilateralND qdr_nd, qdr_nd.angle₁.value = qdr_nd.angle₃.value, qdr_nd.angle₂.value = qdr_nd.angle₄.value, and qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂ is not collinear, then qdr_nd is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_collinear₄₁₂ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcollinear : ¬ Collinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂) : qdr_nd.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, ∠DAB = ∠BCD, ∠ABC = ∠CDA, and D A B is not collinear, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_collinear₄₁₂_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄.out (QDR_nd A B C D nd).nd₁₂.out).value = (ANG B C D (QDR_nd A B C D nd).nd₂₃.out.symm (QDR_nd A B C D nd).nd₃₄.out).value) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.out.symm (QDR_nd A B C D nd).nd₂₃.out).value = (ANG C D A (QDR_nd A B C D nd).nd₃₄.out.symm (QDR_nd A B C D nd).nd₁₄.out.symm).value) (notcollinear : ¬ Collinear D A B) : (QDR_nd A B C D nd).IsParallelogram_nd := qdr_nd_is_prg_nd_of_eq_angle_value_eq_angle_value_not_collinear₄₁₂ (QDR_nd A B C D nd) h₁ h₂ notcollinear

/-- Given QuadrilateralND qdr_nd, qdr_nd.edgeND₁₂.length = qdr_nd.edgeND₃₄.length, qdr_nd.edgeND₁₄.length = qdr_nd.edgeND₂₃.length, the signs of qdr_nd.angle₁ and qdr_nd.angle₃ are equal, then qdr_nd is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_eq_length_eq_length_eq_angle_sign (h₁ : qdr_nd.edgeND₁₂.length = qdr_nd.edgeND₃₄.length) (h₂ : qdr_nd.edgeND₁₄.length = qdr_nd.edgeND₂₃.length) (h : (qdr_nd.angle₁.value.IsPos ∧ qdr_nd.angle₃.value.IsPos) ∨ (qdr_nd.angle₁.value.IsNeg ∧ qdr_nd.angle₃.value.IsNeg)) : qdr_nd.IsParallelogram_nd := by
  have nontriv₄₁₂ : ¬ Collinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂ := by sorry
  have nontriv₂₃₄ : ¬ Collinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄ := by sorry
  have nd₂₄ : qdr_nd.point₄ ≠ qdr_nd.point₂ := by sorry
  have tr_nd₁ : TriangleND P := (TRI_nd qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂ nontriv₄₁₂)
  have tr_nd₂ : TriangleND P := (TRI_nd qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄ nontriv₂₃₄)
  have e₁ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length := sorry
  have e₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length := by
    have l₁ : tr_nd₁.edge₂ = (SEG qdr_nd.point₂ qdr_nd.point₄) := by sorry
    have l₂ : tr_nd₂.edge₂ = (SEG qdr_nd.point₄ qdr_nd.point₂) := by sorry
    rw [l₁,l₂]
    exact ((SEG qdr_nd.point₂ qdr_nd.point₄).length_of_rev_eq_length).symm
  have e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length := by sorry
  have Congr_or_ACongr : tr_nd₁ ≅ tr_nd₂ ∨ tr_nd₁ ≅ₐ tr_nd₂ := TriangleND.congr_or_acongr_of_SSS e₁ e₂ e₃
  rcases Congr_or_ACongr with ⟨Congr,ACongr⟩
  · apply qdr_nd_is_prg_nd_of_para_para_not_collinear₄₁₂
    · sorry
    · sorry
    exact nontriv₄₁₂
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, AB = CD, AD = BC, the signs of ∠DAB and ∠BCD are equal, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_eq_length_eq_length_eq_angle_sign_variant (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG A D).length = (SEG B C).length) (h : ((ANG D A B (QDR_nd A B C D nd).nd₁₄.out (QDR_nd A B C D nd).nd₁₂.out).value.IsPos ∧ (ANG B C D (QDR_nd A B C D nd).nd₂₃.out.symm (QDR_nd A B C D nd).nd₃₄.out).value.IsPos) ∨ ((ANG D A B (QDR_nd A B C D nd).nd₁₄.out (QDR_nd A B C D nd).nd₁₂.out).value.IsNeg ∧ (ANG B C D (QDR_nd A B C D nd).nd₂₃.out.symm (QDR_nd A B C D nd).nd₃₄.out).value.IsNeg)) : (QDR_nd A B C D nd).IsParallelogram_nd := qdr_nd_is_prg_nd_of_eq_length_eq_length_eq_angle_sign (QDR_nd A B C D nd) h₁ h₂ h

/-- Given QuadrilateralND qdr_nd, qdr_nd.edgeND₁₂.length = qdr_nd.edgeND₃₄.length, qdr_nd.edgeND₁₄.length = qdr_nd.edgeND₂₃.length, the signs of qdr_nd.angle₂ and qdr_nd.angle₄ are equal, then qdr_nd is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_eq_length_eq_length_eq_angle_sign' (h₁ : qdr_nd.edgeND₁₂.length = qdr_nd.edgeND₃₄.length) (h₂ : qdr_nd.edgeND₁₄.length = qdr_nd.edgeND₂₃.length) (h : (qdr_nd.angle₂.value.IsPos ∧ qdr_nd.angle₄.value.IsPos) ∨ (qdr_nd.angle₂.value.IsNeg ∧ qdr_nd.angle₄.value.IsNeg)) : qdr_nd.IsParallelogram_nd := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsNd, AB = CD, AD = BC, the signs of ∠ABC and ∠CDA are equal, then Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_nd_of_eq_length_eq_length_eq_angle_sign'_variant (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG A D).length = (SEG B C).length) (h : ((ANG A B C (QDR_nd A B C D nd).nd₁₂.out.symm (QDR_nd A B C D nd).nd₂₃.out).value.IsPos ∧ (ANG C D A (QDR_nd A B C D nd).nd₃₄.out.symm (QDR_nd A B C D nd).nd₁₄.out.symm).value.IsPos) ∨ ((ANG A B C (QDR_nd A B C D nd).nd₁₂.out.symm (QDR_nd A B C D nd).nd₂₃.out).value.IsNeg ∧ (ANG C D A (QDR_nd A B C D nd).nd₃₄.out.symm (QDR_nd A B C D nd).nd₁₄.out.symm).value.IsNeg)) : (QDR_nd A B C D nd).IsParallelogram_nd := qdr_nd_is_prg_nd_of_eq_length_eq_length_eq_angle_sign' (QDR_nd A B C D nd) h₁ h₂ h

end criteria_prg_nd_of_qdr_nd

section criteria_prg_of_qdr_nd

variable {A B C D: P}
variable (nd : (QDR A B C D).IsND)
variable (cvx : (QDR A B C D).IsConvex)
variable {P : Type*} [EuclideanPlane P] (qdr_nd : QuadrilateralND P)
variable {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P)

/-- Given QuadrilateralND qdr_nd, and qdr_nd.edgeND₁₂ ∥ qdr_nd.edgeND₃₄ and (qdr_nd.edgeND₁₂).length = (qdr_nd.edgeND₃₄).length, and qdr_nd.edgeND₁₄ ∥ qdr_nd.edgeND₂₃ and (qdr_nd.edgeND₁₄).length = (qdr_nd.edgeND₂₃).length, qdr_nd is a Parallelogram. -/
theorem qdr_nd_is_prg_of_para_eq_length_para_eq_length (h₁ : qdr_nd.edgeND₁₂ ∥ qdr_nd.edgeND₃₄) (h₂ : qdr_nd.edgeND₁₂.length = qdr_nd.edgeND₃₄.length) (H₁ : qdr_nd.edgeND₁₄ ∥ qdr_nd.edgeND₂₃) (h₂ : qdr_nd.edgeND₁₄.length = qdr_nd.edgeND₂₃.length): qdr_nd.IsParallelogram := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AB ∥ CD and AB = CD, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_nd_is_prg_of_para_eq_length_para_eq_length_varient (h₁ : (SEG_nd A B (QDR_nd A B C D nd).nd₁₂.out) ∥ (SEG_nd C D (QDR_nd A B C D nd).nd₃₄.out)) (h₂ : (SEG A B).length = (SEG C D).length) (H₁ : (SEG_nd A D (QDR_nd A B C D nd).nd₁₄.out) ∥ (SEG_nd B C (QDR_nd A B C D nd).nd₂₃.out)) (H₂ : (SEG A D).length = (SEG B C).length): (QuadrilateralND.mk_nd nd).IsParallelogram := by
  sorry

/-- Given QuadrilateralND qdr_nd, and qdr_nd.diag₁₃.midpoint = qdr_nd.diag₂₄.midpoint, qdr_nd is a Parallelogram. -/
theorem qdr_nd_is_prg_nd_of_diag_inx_eq_mid_eq_mid (h' : (qdr_nd.diag₁₃).midpoint = (qdr_nd.diag₂₄).midpoint) : qdr_nd.IsParallelogram := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsND, and the midpoint of the diagonal AC and BD is the same, Quadrilateral ABCD is a Parallelogram. -/
theorem qdr_nd_is_prg_nd_of_diag_inx_eq_mid_eq_mid_variant (h' : (SEG A C).midpoint = (SEG B D).midpoint) : (QuadrilateralND.mk_nd nd).IsParallelogram := by
  sorry

end criteria_prg_of_qdr_nd

section criteria_prg_nd_of_qdr_cvx

variable {A B C D: P}
variable (nd : (QDR A B C D).IsND)
variable (cvx : (QDR_nd A B C D nd).IsConvex)
variable {P : Type*} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P)
variable {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P)

/-- Given Quadrilateral_cvx qdr_cvx, qdr_cvx.edgeND₁₂ ∥ qdr_cvx.edgeND₃₄ and qdr_cvx.edgeND₁₄ ∥ qdr_cvx.edgeND₂₃, then qdr_cvx is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_para_para (h₁ : qdr_cvx.edgeND₁₂ ∥ qdr_cvx.edgeND₃₄) (h₂ : qdr_cvx.edgeND₁₄ ∥ qdr_cvx.edgeND₂₃) : qdr_cvx.IsParallelogram_nd := by
  unfold QuadrilateralND.IsParallelogram_nd
  constructor
  constructor
  exact h₁
  exact h₂
  sorry
  -- constructor
  -- exact qdr_cvx.not_collinear₁₂₃
  -- exact qdr_cvx.not_collinear₂₃₄
  -- exact qdr_cvx.not_collinear₃₄₁
  -- exact qdr_cvx.not_collinear₄₁₂

/-- Given Quadrilateral_cvx qdr_cvx, and (qdr_cvx.edgeND₁₂).length = (qdr_cvx.edgeND₃₄).length and qdr_cvx.edgeND₁₄.length = qdr_cvx.edgeND₂₃.length, qdr_cvx is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_eq_length_eq_length (h₁ : qdr_cvx.edgeND₁₂.length = qdr_cvx.edgeND₃₄.length) (h₂ : qdr_cvx.edgeND₁₄.length = qdr_cvx.edgeND₂₃.length) : qdr_cvx.IsParallelogram_nd := by
  unfold QuadrilateralND.IsParallelogram_nd
  constructor
  have heq₁: qdr_cvx.edgeND₁₄.length = qdr_cvx.edgeND₁₄.reverse.length := qdr_cvx.edgeND₁₄.reverse.length_of_rev_eq_length
  have eq₁: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.not_collinear₄₁₂).edge₁.length = (TRI_nd qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.not_collinear₂₃₄).edge₁.length := h₁
  have eq₂: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.not_collinear₄₁₂).edge₂.length = (TRI_nd qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.not_collinear₂₃₄).edge₂.length := (TRI_nd qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.not_collinear₂₃₄).edge₂.length_of_rev_eq_length
  have eq₃: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.not_collinear₄₁₂).edge₃.length = (TRI_nd qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.not_collinear₂₃₄).edge₃.length := by
    rw [heq₁] at h₂
    exact h₂
  have congrto: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.not_collinear₄₁₂) IsCongrTo (TRI_nd qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.not_collinear₂₃₄) := TriangleND.congr_of_SSS_of_eq_orientation eq₁ eq₂ eq₃ qdr_cvx.cclock_eq
  rcases congrto with ⟨_,_,_,d,_,f⟩
  have eq_angle₁: (ANG qdr_cvx.point₄ qdr_cvx.point₂ qdr_cvx.point₁).value = (ANG qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.point₃).value := f
  have eq_angle₂: (ANG qdr_cvx.point₁ qdr_cvx.point₄ qdr_cvx.point₂).value = (ANG qdr_cvx.point₃ qdr_cvx.point₂ qdr_cvx.point₄).value := d
  have J: qdr_cvx.triangle_nd₁.angle₁.end_ray = qdr_cvx.diag_nd₂₄.reverse.toRay := by rfl
  have K: qdr_cvx.triangle_nd₁.angle₃.start_ray = qdr_cvx.diag_nd₂₄.toRay := by rfl
  have Q: qdr_cvx.triangle_nd₃.angle₁.end_ray = qdr_cvx.diag_nd₂₄.toRay := by rfl
  have joker: qdr_cvx.triangle_nd₃.angle₃.start_ray = qdr_cvx.diag_nd₂₄.reverse.toRay := by rfl
  have prepa₃: qdr_cvx.triangle_nd₁.angle₃.start_ray.toDir = qdr_cvx.triangle_nd₃.angle₃.start_ray.reverse.toDir := by
    have JOKER: qdr_cvx.diag_nd₂₄.reverse.toRay.reverse.toDir = - qdr_cvx.diag_nd₂₄.reverse.toRay.toDir := qdr_cvx.diag_nd₂₄.reverse.toRay.toDir_of_rev_eq_neg_toDir
    have SpadeA: qdr_cvx.diag_nd₂₄.reverse.toRay.toDir = - qdr_cvx.diag_nd₂₄.toRay.toDir := qdr_cvx.diag_nd₂₄.toDir_of_rev_eq_neg_toDir
    rw [K, joker, JOKER, SpadeA]
    simp only [neg_neg]
  have prepa₄: qdr_cvx.triangle_nd₁.angle₁.end_ray.toDir = qdr_cvx.triangle_nd₃.angle₁.end_ray.reverse.toDir := by
    have JOKER: qdr_cvx.diag_nd₂₄.reverse.toRay.toDir = - qdr_cvx.diag_nd₂₄.toRay.toDir := qdr_cvx.diag_nd₂₄.toDir_of_rev_eq_neg_toDir
    have SpadeA: qdr_cvx.diag_nd₂₄.toRay.reverse.toDir = -qdr_cvx.diag_nd₂₄.toRay.toDir := qdr_cvx.diag_nd₂₄.toRay.toDir_of_rev_eq_neg_toDir
    rw [J, Q, JOKER, SpadeA]
  have near₁: qdr_cvx.triangle_nd₁.angle₁.start_ray.toDir = - qdr_cvx.triangle_nd₃.angle₁.start_ray.toDir := by
    have prepar: qdr_cvx.triangle_nd₁.angle₁.start_ray.toDir = qdr_cvx.triangle_nd₃.angle₁.start_ray.reverse.toDir := start_ray_toDir_rev_toDir_of_ang_rev_ang prepa₄ eq_angle₂
    have prepar': qdr_cvx.triangle_nd₃.angle₁.start_ray.reverse.toDir = - qdr_cvx.triangle_nd₃.angle₁.start_ray.toDir := qdr_cvx.triangle_nd₃.angle₁.start_ray.toDir_of_rev_eq_neg_toDir
    rw [prepar, prepar']
  have near₂: qdr_cvx.triangle_nd₁.angle₃.end_ray.toDir = - qdr_cvx.triangle_nd₃.angle₃.end_ray.toDir := by
    have prepar: qdr_cvx.triangle_nd₁.angle₃.end_ray.toDir = qdr_cvx.triangle_nd₃.angle₃.end_ray.reverse.toDir := end_ray_toDir_rev_toDir_of_ang_rev_ang prepa₃ eq_angle₁
    have prepar': qdr_cvx.triangle_nd₃.angle₃.end_ray.reverse.toDir = - qdr_cvx.triangle_nd₃.angle₃.end_ray.toDir := qdr_cvx.triangle_nd₃.angle₃.end_ray.toDir_of_rev_eq_neg_toDir
    rw [prepar, prepar']
  have very_near₁: qdr_cvx.triangle_nd₁.angle₁.start_ray.toProj = qdr_cvx.triangle_nd₃.angle₁.start_ray.toProj := by
    apply Dir.toProj_eq_toProj_iff.mpr
    right
    exact near₁
  have very_close₁: qdr_cvx.triangle_nd₁.angle₁.start_ray ∥ qdr_cvx.triangle_nd₃.angle₁.start_ray := very_near₁
  have very_near₂: qdr_cvx.triangle_nd₁.angle₃.end_ray.toProj = qdr_cvx.triangle_nd₃.angle₃.end_ray.toProj := by
    apply Dir.toProj_eq_toProj_iff.mpr
    right
    exact near₂
  have very_close₂: qdr_cvx.triangle_nd₁.angle₃.end_ray ∥ qdr_cvx.triangle_nd₃.angle₃.end_ray := very_near₂
  have close₁: qdr_cvx.edgeND₁₄.toProj = qdr_cvx.triangle_nd₁.angle₁.start_ray.toProj := by
    have third: qdr_cvx.edgeND₁₄.reverse.toProj = qdr_cvx.edgeND₁₄.toProj := qdr_cvx.edgeND₁₄.toProj_of_rev_eq_toProj
    exact id third.symm
  have close₂: qdr_cvx.edgeND₂₃.toProj = qdr_cvx.triangle_nd₃.angle₁.start_ray.toProj := by rfl
  have close₃: qdr_cvx.edgeND₁₂.toProj = qdr_cvx.triangle_nd₁.angle₃.end_ray.toProj := by
    have last: qdr_cvx.edgeND₁₂.reverse.toRay = qdr_cvx.triangle_nd₁.angle₃.end_ray := by rfl
    have second: qdr_cvx.edgeND₁₂.reverse.toProj = qdr_cvx.triangle_nd₁.angle₃.end_ray.toProj := by rfl
    have third: qdr_cvx.edgeND₁₂.reverse.toProj = qdr_cvx.edgeND₁₂.toProj := qdr_cvx.edgeND₁₂.toProj_of_rev_eq_toProj
    rw [third.symm, second, last.symm]
  have close₄: qdr_cvx.edgeND₃₄.toProj = qdr_cvx.triangle_nd₃.angle₃.end_ray.toProj := by
    have last: qdr_cvx.edgeND₃₄.reverse.toRay = qdr_cvx.triangle_nd₃.angle₃.end_ray := by rfl
    have second: qdr_cvx.edgeND₃₄.reverse.toProj = qdr_cvx.triangle_nd₃.angle₃.end_ray.toProj := by rfl
    have third: qdr_cvx.edgeND₃₄.reverse.toProj = qdr_cvx.edgeND₃₄.toProj := qdr_cvx.edgeND₃₄.toProj_of_rev_eq_toProj
    rw [third.symm, second, last.symm]
  have win₁: qdr_cvx.edgeND₁₂.toProj = qdr_cvx.edgeND₃₄.toProj := by
    rw [close₃, close₄]
    exact very_close₂
  have win₂: qdr_cvx.edgeND₁₄.toProj = qdr_cvx.edgeND₂₃.toProj := by
    rw [close₁, close₂]
    exact very_close₁
  exact ⟨win₁, win₂⟩
  constructor
  exact qdr_cvx.not_collinear₁₂₃
  exact qdr_cvx.not_collinear₂₃₄
  exact qdr_cvx.not_collinear₃₄₁
  exact qdr_cvx.not_collinear₄₁₂

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AB = CD and AD = BC, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_eq_length_eq_length_variant (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG A D).length = (SEG B C).length) : (QuadrilateralND.mk_nd nd) IsParallelogram_nd := by
  sorry
  -- unfold QuadrilateralND.IsParallelogram_nd
  -- constructor
  -- have heq₁: (SEG A D).length = (QDR_cvx A B C D nd cvx).edgeND₁₄.reverse.length := (QDR_cvx A B C D nd cvx).edgeND₁₄.reverse.length_of_rev_eq_length
  -- have eq₁: (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).not_collinear₄₁₂).edge₁.length = (TRI_nd (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).not_collinear₂₃₄).edge₁.length := h₁
  -- have eq₂: (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).not_collinear₄₁₂).edge₂.length = (TRI_nd (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).not_collinear₂₃₄).edge₂.length := (TRI_nd (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).not_collinear₂₃₄).edge₂.length_of_rev_eq_length
  -- have eq₃: (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).not_collinear₄₁₂).edge₃.length = (TRI_nd (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).not_collinear₂₃₄).edge₃.length := by
  --   rw [heq₁] at h₂
  --   exact h₂
  -- have congrto: (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).not_collinear₄₁₂) IsCongrTo (TRI_nd (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).not_collinear₂₃₄) := TriangleND.congr_of_SSS_of_eq_orientation eq₁ eq₂ eq₃ (QDR_cvx A B C D nd cvx).cclock_eq
  -- rcases congrto with ⟨_,_,_,d,_,f⟩
  -- have eq_angle₁: (ANG (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).nd₂₄.out (QDR_cvx A B C D nd cvx).nd₁₂.out.symm).value = (ANG (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).nd₂₄.out.symm (QDR_cvx A B C D nd cvx).nd₃₄.out.symm).value := f
  -- have eq_angle₂: (ANG (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).nd₁₄.out.symm (QDR_cvx A B C D nd cvx).nd₂₄.out.symm).value = (ANG (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).nd₂₃.out (QDR_cvx A B C D nd cvx).nd₂₄.out).value := d
  -- have J: (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₁.end_ray = (QDR_cvx A B C D nd cvx).diag_nd₂₄.reverse.toRay := by rfl
  -- have K: (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₃.start_ray = (QDR_cvx A B C D nd cvx).diag_nd₂₄.toRay := by rfl
  -- have Q: (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₁.end_ray = (QDR_cvx A B C D nd cvx).diag_nd₂₄.toRay := by rfl
  -- have joker: (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₃.start_ray = (QDR_cvx A B C D nd cvx).diag_nd₂₄.reverse.toRay := by rfl
  -- have prepa₃: (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₃.start_ray.toDir = (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₃.start_ray.reverse.toDir := by
  --   have JOKER: (QDR_cvx A B C D nd cvx).diag_nd₂₄.reverse.toRay.reverse.toDir = - (QDR_cvx A B C D nd cvx).diag_nd₂₄.reverse.toRay.toDir := (QDR_cvx A B C D nd cvx).diag_nd₂₄.reverse.toRay.toDir_of_rev_eq_neg_toDir
  --   have SpadeA: (QDR_cvx A B C D nd cvx).diag_nd₂₄.reverse.toRay.toDir = - (QDR_cvx A B C D nd cvx).diag_nd₂₄.toRay.toDir := (QDR_cvx A B C D nd cvx).diag_nd₂₄.toDir_of_rev_eq_neg_toDir
  --   rw [K, joker, JOKER, SpadeA]
  --   simp only [neg_neg]
  -- have prepa₄: (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₁.end_ray.toDir = (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₁.end_ray.reverse.toDir := by
  --   have JOKER: (QDR_cvx A B C D nd cvx).diag_nd₂₄.reverse.toRay.toDir = - (QDR_cvx A B C D nd cvx).diag_nd₂₄.toRay.toDir := (QDR_cvx A B C D nd cvx).diag_nd₂₄.toDir_of_rev_eq_neg_toDir
  --   have SpadeA: (QDR_cvx A B C D nd cvx).diag_nd₂₄.toRay.reverse.toDir = - (QDR_cvx A B C D nd cvx).diag_nd₂₄.toRay.toDir := (QDR_cvx A B C D nd cvx).diag_nd₂₄.toRay.toDir_of_rev_eq_neg_toDir
  --   rw [J, Q, JOKER, SpadeA]
  -- have near₁: (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₁.start_ray.toDir = - (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₁.start_ray.toDir := by
  --   have prepar: (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₁.start_ray.toDir = (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₁.start_ray.reverse.toDir := start_ray_toDir_rev_toDir_of_ang_rev_ang prepa₄ eq_angle₂
  --   have prepar': (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₁.start_ray.reverse.toDir = - (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₁.start_ray.toDir := (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₁.start_ray.toDir_of_rev_eq_neg_toDir
  --   rw [prepar, prepar']
  -- have near₂: (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₃.end_ray.toDir = - (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₃.end_ray.toDir := by
  --   have prepar: (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₃.end_ray.toDir = (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₃.end_ray.reverse.toDir := end_ray_toDir_rev_toDir_of_ang_rev_ang prepa₃ eq_angle₁
  --   have prepar': (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₃.end_ray.reverse.toDir = - (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₃.end_ray.toDir := (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₃.end_ray.toDir_of_rev_eq_neg_toDir
  --   rw [prepar, prepar']
  -- have very_near₁: (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₁.start_ray.toProj = (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₁.start_ray.toProj := by
  --   apply Dir.toProj_eq_toProj_iff.mpr
  --   right
  --   exact near₁
  -- have very_close₁: (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₁.start_ray ∥ (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₁.start_ray := very_near₁
  -- have very_near₂: (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₃.end_ray.toProj = (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₃.end_ray.toProj := by
  --   apply Dir.toProj_eq_toProj_iff.mpr
  --   right
  --   exact near₂
  -- have very_close₂: (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₃.end_ray ∥ (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₃.end_ray := very_near₂
  -- have close₁: (QDR_cvx A B C D nd cvx).edgeND₁₄.toProj = (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₁.start_ray.toProj := by
  --   have third: (QDR_cvx A B C D nd cvx).edgeND₁₄.reverse.toProj = (QDR_cvx A B C D nd cvx).edgeND₁₄.toProj := (QDR_cvx A B C D nd cvx).edgeND₁₄.toProj_of_rev_eq_toProj
  --   exact id third.symm
  -- have close₂: (QDR_cvx A B C D nd cvx).edgeND₂₃.toProj = (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₁.start_ray.toProj := by rfl
  -- have close₃: (QDR_cvx A B C D nd cvx).edgeND₁₂.toProj = (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₃.end_ray.toProj := by
  --   have last: (QDR_cvx A B C D nd cvx).edgeND₁₂.reverse.toRay = (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₃.end_ray := by rfl
  --   have second: (QDR_cvx A B C D nd cvx).edgeND₁₂.reverse.toProj = (QDR_cvx A B C D nd cvx).triangle_nd₁.angle₃.end_ray.toProj := by rfl
  --   have third: (QDR_cvx A B C D nd cvx).edgeND₁₂.reverse.toProj = (QDR_cvx A B C D nd cvx).edgeND₁₂.toProj := (QDR_cvx A B C D nd cvx).edgeND₁₂.toProj_of_rev_eq_toProj
  --   rw [third.symm, second, last.symm]
  -- have close₄: (QDR_cvx A B C D nd cvx).edgeND₃₄.toProj = (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₃.end_ray.toProj := by
  --   have last: (QDR_cvx A B C D nd cvx).edgeND₃₄.reverse.toRay = (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₃.end_ray := by rfl
  --   have second: (QDR_cvx A B C D nd cvx).edgeND₃₄.reverse.toProj = (QDR_cvx A B C D nd cvx).triangle_nd₃.angle₃.end_ray.toProj := by rfl
  --   have third: (QDR_cvx A B C D nd cvx).edgeND₃₄.reverse.toProj = (QDR_cvx A B C D nd cvx).edgeND₃₄.toProj := (QDR_cvx A B C D nd cvx).edgeND₃₄.toProj_of_rev_eq_toProj
  --   rw [third.symm, second, last.symm]
  -- have win₁: (QDR_cvx A B C D nd cvx).edgeND₁₂.toProj = (QDR_cvx A B C D nd cvx).edgeND₃₄.toProj := by
  --   rw [close₃, close₄]
  --   exact very_close₂
  -- have win₂: (QDR_cvx A B C D nd cvx).edgeND₁₄.toProj = (QDR_cvx A B C D nd cvx).edgeND₂₃.toProj := by
  --   rw [close₁, close₂]
  --   exact very_close₁
  -- exact ⟨win₁, win₂⟩
  -- constructor
  -- exact (QDR_cvx A B C D nd cvx).not_collinear₁₂₃
  -- exact (QDR_cvx A B C D nd cvx).not_collinear₂₃₄
  -- exact (QDR_cvx A B C D nd cvx).not_collinear₃₄₁
  -- exact (QDR_cvx A B C D nd cvx).not_collinear₄₁₂

/-- Given Quadrilateral_cvx qdr_cvx, and qdr_cvx.edgeND₁₂ ∥ qdr_cvx.edgeND₃₄ and (qdr_cvx.edgeND₁₂).length = (qdr_cvx.edgeND₃₄).length, qdr_cvx is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_para_eq_length (h₁ : qdr_cvx.edgeND₁₂ ∥ qdr_cvx.edgeND₃₄) (h₂ : qdr_cvx.edgeND₁₂.length = qdr_cvx.edgeND₃₄.length) : qdr_cvx.IsParallelogram_nd := by
  unfold QuadrilateralND.IsParallelogram_nd
  constructor
  unfold parallel at h₁
  have h: qdr_cvx.edgeND₁₂.toDir = qdr_cvx.edgeND₃₄.toDir ∨ qdr_cvx.edgeND₁₂.toDir = - qdr_cvx.edgeND₃₄.toDir := by
    apply Dir.toProj_eq_toProj_iff.1
    exact h₁
  have diag_ng_para: ¬ qdr_cvx.diag_nd₁₃.toProj = qdr_cvx.diag_nd₂₄.toProj := qdr_cvx.diag_not_para
  rcases h with case_not_convex | case_convex
  -- Case that is not convex, goal is prove contra
  have angle₁_eq_angle₄: (ANG qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁).value = (ANG qdr_cvx.point₂ qdr_cvx.point₁ qdr_cvx.point₄).value := by
    apply ang_eq_ang_of_toDir_rev_toDir
    have ray₁₂_toDir_eq_SegND₁₂_toDir: qdr_cvx.edgeND₁₂.toDir = (ANG qdr_cvx.point₂ qdr_cvx.point₁ qdr_cvx.point₄).start_ray.toDir := by rfl
    have ray₄₃_toDir_eq_SegND₃₄_rev_toDir: qdr_cvx.edgeND₃₄.reverse.toDir = (ANG qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁).start_ray.toDir := by rfl
    have SegND₄₃_toDir_neg_SegND₃₄_rev_toDir: qdr_cvx.edgeND₃₄.reverse.toDir = - qdr_cvx.edgeND₃₄.toDir := by apply SegND.toDir_of_rev_eq_neg_toDir
    rw [ray₁₂_toDir_eq_SegND₁₂_toDir.symm, ray₄₃_toDir_eq_SegND₃₄_rev_toDir.symm, SegND₄₃_toDir_neg_SegND₃₄_rev_toDir, case_not_convex]
    exact qdr_cvx.edgeND₁₄.toDir_of_rev_eq_neg_toDir
  have IsCongrTo₁₄: TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁ IsCongrTo TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄ := by
    have edge₂_eq: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).1.edge₂.length = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).1.edge₂.length := by apply length_of_rev_eq_length'
    have edge₃_eq: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).1.edge₃.length = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).1.edge₃.length := by
      have eq_length: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).1.edge₃.length = qdr_cvx.edgeND₃₄.length := by apply length_of_rev_eq_length'
      rw [eq_length]
      exact h₂.symm
    apply TriangleND.congr_of_SAS edge₂_eq angle₁_eq_angle₄ edge₃_eq
  unfold TriangleND.IsCongr at IsCongrTo₁₄
  -- Use IsCongrTo to prove angle eq
  have prepa₁: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).angle₃.value = (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.value := by
    rcases IsCongrTo₁₄ with ⟨_, _, _, _, _, propf⟩
    exact propf.symm
  -- Use angle_eq to prove two diag para.
  have prepa₂: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.start_ray.reverse.toDir = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).angle₃.start_ray.toDir := by
    have prepaA: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.start_ray.reverse.toDir = - (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.start_ray.toDir := (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.start_ray.toDir_of_rev_eq_neg_toDir
    have prepaB: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.start_ray.toDir = qdr_cvx.edgeND₁₄.toDir := by rfl
    have prepaC: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).angle₃.start_ray.toDir = qdr_cvx.edgeND₁₄.reverse.toDir := by rfl
    have prepaD: qdr_cvx.edgeND₁₄.reverse.toDir = - qdr_cvx.edgeND₁₄.toDir := qdr_cvx.edgeND₁₄.toDir_of_rev_eq_neg_toDir
    rw [prepaA, prepaB, prepaC, prepaD]
  have prepa₃: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.end_ray.reverse.toDir = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).angle₃.end_ray.toDir := (end_ray_toDir_rev_toDir_of_ang_rev_ang prepa₂.symm prepa₁).symm
  have prepa₄: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.end_ray.reverse.toDir = - (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.end_ray.toDir := by
    apply (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.end_ray.toDir_of_rev_eq_neg_toDir
  rw [prepa₄] at prepa₃
  have very_nr₂: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.end_ray.toProj = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).angle₃.end_ray.toProj := by
    apply Dir.toProj_eq_toProj_iff.mpr
    right
    exact neg_eq_iff_eq_neg.mp prepa₃
  have prepa₅: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_collinear₄₃₁).angle₃.end_ray.toProj = qdr_cvx.diag_nd₁₃.toProj := by rfl
  have prepa₆: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_collinear₁₂₄).angle₃.end_ray.toProj = qdr_cvx.diag_nd₂₄.reverse.toProj := by rfl
  have prepa₇: qdr_cvx.diag_nd₂₄.reverse.toProj = qdr_cvx.diag_nd₂₄.toProj := qdr_cvx.diag_nd₂₄.toProj_of_rev_eq_toProj
  rw [prepa₇, very_nr₂.symm, prepa₅] at prepa₆
  -- Two diags para, not allowed in a qdr_cvx
  contradiction
  -- Case that is convex, using para to prove angle eq
  have angle₁_eq_angle₃: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_collinear₁₂₃).angle₁.value = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_collinear₃₄₁).angle₁.value := by
    apply ang_eq_ang_of_toDir_rev_toDir
    exact case_convex
    have K₁: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_collinear₁₂₃).angle₁.end_ray.toDir = qdr_cvx.diag_nd₁₃.toDir := by rfl
    have K₂: (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_collinear₃₄₁).angle₁.end_ray.toDir = qdr_cvx.diag_nd₁₃.reverse.toDir := by rfl
    have K₃: qdr_cvx.diag_nd₁₃.reverse.toDir = - qdr_cvx.diag_nd₁₃.toDir := qdr_cvx.diag_nd₁₃.toDir_of_rev_eq_neg_toDir
    rw [K₁.symm, K₂.symm] at K₃
    exact neg_eq_iff_eq_neg.mp (id K₃.symm)
  -- Prove IsCongrTo
  have prepar₁: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_collinear₁₂₃).1.edge₂.length = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_collinear₃₄₁).1.edge₂.length := length_of_rev_eq_length'
  have prepar₂: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_collinear₁₂₃).1.edge₃.length = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_collinear₃₄₁).1.edge₃.length := h₂
  have IsCongrTo₁₃: TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_collinear₁₂₃ IsCongrTo TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_collinear₃₄₁ := TriangleND.congr_of_SAS prepar₁ angle₁_eq_angle₃ prepar₂
  unfold TriangleND.IsCongr at IsCongrTo₁₃
  -- Use IsCongrTo to prove angle eq
  have pr₁: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_collinear₁₂₃).angle₃.value = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_collinear₃₄₁).angle₃.value := by
    rcases IsCongrTo₁₃ with ⟨_, _, _, _, _, propf⟩
    exact propf
  -- Use angle eq to prove para, hope qdr_cvx becomes prg
  have pr₂: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_collinear₁₂₃).angle₃.start_ray.toDir = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_collinear₃₄₁).angle₃.start_ray.reverse.toDir := by
    have K₄: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_collinear₁₂₃).angle₃.start_ray.toDir = qdr_cvx.diag_nd₁₃.reverse.toDir := by rfl
    have K₅: (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_collinear₃₄₁).angle₃.start_ray.toDir = qdr_cvx.diag_nd₁₃.toDir := by rfl
    have K₆: qdr_cvx.diag_nd₁₃.reverse.toDir = - qdr_cvx.diag_nd₁₃.toDir := qdr_cvx.diag_nd₁₃.toDir_of_rev_eq_neg_toDir
    rw [K₄.symm, K₅.symm] at K₆
    exact K₆
  have near: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_collinear₁₂₃).angle₃.end_ray.toDir = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_collinear₃₄₁).angle₃.end_ray.reverse.toDir := end_ray_toDir_rev_toDir_of_ang_rev_ang pr₂ pr₁
  have J₁: (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_collinear₃₄₁).angle₃.end_ray.reverse.toDir = - (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_collinear₃₄₁).angle₃.end_ray.toDir := (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_collinear₃₄₁).angle₃.end_ray.toDir_of_rev_eq_neg_toDir
  have J₂: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_collinear₁₂₃).angle₃.end_ray.toDir = qdr_cvx.edgeND₂₃.reverse.toDir := by rfl
  have J₃: (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_collinear₃₄₁).angle₃.end_ray.toDir = qdr_cvx.edgeND₁₄.toDir := by rfl
  have J₄: qdr_cvx.edgeND₂₃.reverse.toDir = - qdr_cvx.edgeND₂₃.toDir := qdr_cvx.edgeND₂₃.toDir_of_rev_eq_neg_toDir
  rw [J₁, J₂, J₃, J₄] at near
  simp only [neg_inj] at near
  have close: qdr_cvx.edgeND₂₃.toProj = qdr_cvx.edgeND₁₄.toProj := by
    apply Dir.toProj_eq_toProj_iff.mpr
    left
    exact near
  constructor
  exact h₁
  exact close.symm
  -- Done!
  constructor
  exact qdr_cvx.not_collinear₁₂₃
  exact qdr_cvx.not_collinear₂₃₄
  exact qdr_cvx.not_collinear₃₄₁
  exact qdr_cvx.not_collinear₄₁₂

/- Given four points ABCD and Quadrilateral ABCD IsConvex, and AB ∥ CD and AB = CD, Quadrilateral ABCD is a Parallelogram_nd. -/
-- theorem qdr_cvx_is_prg_nd_of_para_eq_length_variant (h₁ : (SEG_nd A B (QDR_cvx A B C D nd cvx).nd₁₂.out) ∥ (SEG_nd C D (QDR_cvx A B C D nd cvx).nd₃₄.out)) (h₂ : (SEG_nd A B (QDR_cvx A B C D nd cvx).nd₁₂.out).length = (SEG_nd C D (QDR_cvx A B C D nd cvx).nd₃₄.out).length) : (QuadrilateralND.mk_nd nd) IsParallelogram_nd := by
  --  unfold QuadrilateralND.IsParallelogram_nd
  --  constructor
  --  unfold parallel at h₁
  --  have h: (QDR_cvx A B C D nd cvx).edgeND₁₂.toDir = (QDR_cvx A B C D nd cvx).edgeND₃₄.toDir ∨ (QDR_cvx A B C D nd cvx).edgeND₁₂.toDir = - (QDR_cvx A B C D nd cvx).edgeND₃₄.toDir := by
  --    apply Dir.toProj_eq_toProj_iff.1
  --    exact h₁
  --  have diag_ng_para: ¬ (QDR_cvx A B C D nd cvx).diag_nd₁₃.toProj = (QDR_cvx A B C D nd cvx).diag_nd₂₄.toProj := (QDR_cvx A B C D nd cvx).diag_not_para
  --  rcases h with case_not_convex | case_convex
  --  -- Case that is not convex, goal is prove contra
  --  have angle₁_eq_angle₄: (ANG (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).nd₃₄.out.symm (QDR_cvx A B C D nd cvx).nd₁₄.out.symm).value = (ANG (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).nd₁₂.out (QDR_cvx A B C D nd cvx).nd₁₄.out).value := by
  --    apply ang_eq_ang_of_toDir_rev_toDir
  --    have ray₁₂_toDir_eq_Seg_nd₁₂_toDir: (QDR_cvx A B C D nd cvx).edgeND₁₂.toDir = (ANG (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).nd₁₂.out (QDR_cvx A B C D nd cvx).nd₁₄.out).start_ray.toDir := by rfl
  --    have ray₄₃_toDir_eq_Seg_nd₃₄_rev_toDir: (QDR_cvx A B C D nd cvx).edgeND₃₄.reverse.toDir = (ANG (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).nd₃₄.out.symm (QDR_cvx A B C D nd cvx).nd₁₄.out.symm).start_ray.toDir := by rfl
  --    have Seg_nd₄₃_toDir_neg_Seg_nd₃₄_rev_toDir: (QDR_cvx A B C D nd cvx).edgeND₃₄.reverse.toDir = - (QDR_cvx A B C D nd cvx).edgeND₃₄.toDir := by apply SegND.toDir_of_rev_eq_neg_toDir
  --    rw [ray₁₂_toDir_eq_Seg_nd₁₂_toDir.symm, ray₄₃_toDir_eq_Seg_nd₃₄_rev_toDir.symm, Seg_nd₄₃_toDir_neg_Seg_nd₃₄_rev_toDir, case_not_convex]
  --    exact (QDR_cvx A B C D nd cvx).edgeND₁₄.toDir_of_rev_eq_neg_toDir
  --  have IsCongrTo₁₄: TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁ IsCongrTo TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).not_collinear₁₂₄ := by
  --    have edge₂_eq: (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).1.edge₂.length = (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).not_collinear₁₂₄).1.edge₂.length := by apply length_of_rev_eq_length'
  --    have edge₃_eq: (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).1.edge₃.length = (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).not_collinear₁₂₄).1.edge₃.length := by
  --      have eq_length: (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).1.edge₃.length = (QDR_cvx A B C D nd cvx).edgeND₃₄.length := by apply length_of_rev_eq_length'
  --      rw [eq_length]
  --      exact h₂.symm
  --    apply TriangleND.congr_of_SAS edge₂_eq angle₁_eq_angle₄ edge₃_eq
  --  unfold TriangleND.IsCongr at IsCongrTo₁₄
  --  -- Use IsCongrTo to prove angle eq
  --  have prepa₁: (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).not_collinear₁₂₄).angle₃.value = (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).angle₃.value := by
  --    rcases IsCongrTo₁₄ with ⟨_, _, _, _, _, propf⟩
  --    exact propf.symm
  --  -- Use angle_eq to prove two diag para.
  --  have prepa₂: (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).angle₃.start_ray.reverse.toDir = (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).not_collinear₁₂₄).angle₃.start_ray.toDir := by
  --    have prepaA: (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).angle₃.start_ray.reverse.toDir = - (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).angle₃.start_ray.toDir := (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).angle₃.start_ray.toDir_of_rev_eq_neg_toDir
  --    have prepaB: (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).angle₃.start_ray.toDir = (QDR_cvx A B C D nd cvx).edgeND₁₄.toDir := by rfl
  --    have prepaC: (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).not_collinear₁₂₄).angle₃.start_ray.toDir = (QDR_cvx A B C D nd cvx).edgeND₁₄.reverse.toDir := by rfl
  --    have prepaD: (QDR_cvx A B C D nd cvx).edgeND₁₄.reverse.toDir = - (QDR_cvx A B C D nd cvx).edgeND₁₄.toDir := (QDR_cvx A B C D nd cvx).edgeND₁₄.toDir_of_rev_eq_neg_toDir
  --    rw [prepaA, prepaB, prepaC, prepaD]
  --  have prepa₃: (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).angle₃.end_ray.reverse.toDir = (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).not_collinear₁₂₄).angle₃.end_ray.toDir := (end_ray_toDir_rev_toDir_of_ang_rev_ang prepa₂.symm prepa₁).symm
  --  have prepa₄: (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).angle₃.end_ray.reverse.toDir = - (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).angle₃.end_ray.toDir := by
  --    apply (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).angle₃.end_ray.toDir_of_rev_eq_neg_toDir
  --  rw [prepa₄] at prepa₃
  --  have very_nr₂: (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).angle₃.end_ray.toProj = (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).not_collinear₁₂₄).angle₃.end_ray.toProj := by
  --    apply Dir.toProj_eq_toProj_iff.mpr
  --    right
  --    exact neg_eq_iff_eq_neg.mp prepa₃
  --  have prepa₅: (TRI_nd (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₄₃₁).angle₃.end_ray.toProj = (QDR_cvx A B C D nd cvx).diag_nd₁₃.toProj := by rfl
  --  have prepa₆: (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).not_collinear₁₂₄).angle₃.end_ray.toProj = (QDR_cvx A B C D nd cvx).diag_nd₂₄.reverse.toProj := by rfl
  --  have prepa₇: (QDR_cvx A B C D nd cvx).diag_nd₂₄.reverse.toProj = (QDR_cvx A B C D nd cvx).diag_nd₂₄.toProj := (QDR_cvx A B C D nd cvx).diag_nd₂₄.toProj_of_rev_eq_toProj
  --  rw [prepa₇, very_nr₂.symm, prepa₅] at prepa₆
  --  -- Two diags para, not allowed in a qdr_cvx
  --  contradiction
  --  -- Case that is convex, using para to prove angle eq
  --  have angle₁_eq_angle₃: (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).not_collinear₁₂₃).angle₁.value = (TRI_nd (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₃₄₁).angle₁.value := by
  --    apply ang_eq_ang_of_toDir_rev_toDir
  --    exact case_convex
  --    have K₁: (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).not_collinear₁₂₃).angle₁.end_ray.toDir = (QDR_cvx A B C D nd cvx).diag_nd₁₃.toDir := by rfl
  --    have K₂: (TRI_nd (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₃₄₁).angle₁.end_ray.toDir = (QDR_cvx A B C D nd cvx).diag_nd₁₃.reverse.toDir := by rfl
  --    have K₃: (QDR_cvx A B C D nd cvx).diag_nd₁₃.reverse.toDir = - (QDR_cvx A B C D nd cvx).diag_nd₁₃.toDir := (QDR_cvx A B C D nd cvx).diag_nd₁₃.toDir_of_rev_eq_neg_toDir
  --    rw [K₁.symm, K₂.symm] at K₃
  --    exact neg_eq_iff_eq_neg.mp (id K₃.symm)
  --  -- Prove IsCongrTo
  --  have prepar₁: (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).not_collinear₁₂₃).1.edge₂.length = (TRI_nd (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₃₄₁).1.edge₂.length := length_of_rev_eq_length'
  --  have prepar₂: (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).not_collinear₁₂₃).1.edge₃.length = (TRI_nd (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₃₄₁).1.edge₃.length := h₂
  --  have IsCongrTo₁₃: TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).not_collinear₁₂₃ IsCongrTo TRI_nd (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₃₄₁ := TriangleND.congr_of_SAS prepar₁ angle₁_eq_angle₃ prepar₂
  --  unfold TriangleND.IsCongr at IsCongrTo₁₃
  --  -- Use IsCongrTo to prove angle eq
  --  have pr₁: (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).not_collinear₁₂₃).angle₃.value = (TRI_nd (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₃₄₁).angle₃.value := by
  --    rcases IsCongrTo₁₃ with ⟨_, _, _, _, _, propf⟩
  --    exact propf
  --  -- Use angle eq to prove para, hope qdr_cvx becomes prg
  --  have pr₂: (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).not_collinear₁₂₃).angle₃.start_ray.toDir = (TRI_nd (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₃₄₁).angle₃.start_ray.reverse.toDir := by
  --    have K₄: (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).not_collinear₁₂₃).angle₃.start_ray.toDir = (QDR_cvx A B C D nd cvx).diag_nd₁₃.reverse.toDir := by rfl
  --    have K₅: (TRI_nd (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₃₄₁).angle₃.start_ray.toDir = (QDR_cvx A B C D nd cvx).diag_nd₁₃.toDir := by rfl
  --    have K₆: (QDR_cvx A B C D nd cvx).diag_nd₁₃.reverse.toDir = - (QDR_cvx A B C D nd cvx).diag_nd₁₃.toDir := (QDR_cvx A B C D nd cvx).diag_nd₁₃.toDir_of_rev_eq_neg_toDir
  --    rw [K₄.symm, K₅.symm] at K₆
  --    exact K₆
  --  have near: (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂ (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).not_collinear₁₂₃).angle₃.end_ray.toDir = (TRI_nd (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₃₄₁).angle₃.end_ray.reverse.toDir := end_ray_toDir_rev_toDir_of_ang_rev_ang pr₂ pr₁
  --  have J₁: (TRI_nd (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₃₄₁).angle₃.end_ray.reverse.toDir = - (TRI_nd (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₃₄₁).angle₃.end_ray.toDir := (TRI_nd (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₃₄₁).angle₃.end_ray.toDir_of_rev_eq_neg_toDir
  --  have J₂: (TRI_nd (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).point₂(QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).not_collinear₁₂₃).angle₃.end_ray.toDir = (QDR_cvx A B C D nd cvx).edgeND₂₃.reverse.toDir := by rfl
  --  have J₃: (TRI_nd (QDR_cvx A B C D nd cvx).point₃ (QDR_cvx A B C D nd cvx).point₄ (QDR_cvx A B C D nd cvx).point₁ (QDR_cvx A B C D nd cvx).not_collinear₃₄₁).angle₃.end_ray.toDir = (QDR_cvx A B C D nd cvx).edgeND₁₄.toDir := by rfl
  --  have J₄: (QDR_cvx A B C D nd cvx).edgeND₂₃.reverse.toDir = - (QDR_cvx A B C D nd cvx).edgeND₂₃.toDir := (QDR_cvx A B C D nd cvx).edgeND₂₃.toDir_of_rev_eq_neg_toDir
  --  rw [J₁, J₂, J₃, J₄] at near
  --  simp only [neg_inj] at near
  --  have close: (QDR_cvx A B C D nd cvx).edgeND₂₃.toProj = (QDR_cvx A B C D nd cvx).edgeND₁₄.toProj := by
  --    apply Dir.toProj_eq_toProj_iff.mpr
  --    left
  --    exact near
  --  constructor
  --  exact h₁
  --  exact close.symm
  --  -- Done!
  --  constructor
  --  exact (QDR_cvx A B C D nd cvx).not_collinear₁₂₃
  --  exact (QDR_cvx A B C D nd cvx).not_collinear₂₃₄
  --  exact (QDR_cvx A B C D nd cvx).not_collinear₃₄₁
  --  exact (QDR_cvx A B C D nd cvx).not_collinear₄₁₂

/- Given Quadrilateral_cvx qdr_cvx, and qdr_cvx.edgeND₁₄ ∥ qdr_cvx.edgeND₂₃ and (qdr_cvx.edgeND₁₄).length = (qdr_cvx.edgeND₂₃).length, qdr_cvx is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_para_eq_length' (h₁ : qdr_cvx.edgeND₁₄ ∥ qdr_cvx.edgeND₂₃) (h₂ : qdr_cvx.edgeND₁₄.length = qdr_cvx.edgeND₂₃.length) : qdr_cvx.IsParallelogram_nd := by sorry
  -- unfold QuadrilateralND.IsParallelogram_nd
  -- constructor
  -- let perm_convex := Quadrilateral_cvx.mk_is_convex qdr_cvx.perm_is_convex
  -- have K₁: perm_convex.edgeND₁₂.toProj = qdr_cvx.edgeND₂₃.toProj := by rfl
  -- have K₂: perm_convex.edgeND₁₂.length = qdr_cvx.edgeND₂₃.length := by rfl
  -- have j₂: perm_convex.edgeND₃₄ = qdr_cvx.edgeND₁₄.reverse := by rfl
  -- have K₃: perm_convex.edgeND₃₄.toProj = qdr_cvx.edgeND₁₄.toProj := by
  --   rw [j₂]
  --   apply SegND.toProj_of_rev_eq_toProj
  -- have K₄: perm_convex.edgeND₃₄.length = qdr_cvx.edgeND₁₄.length := by
  --   rw [j₂]
  --   apply SegND.length_of_rev_eq_length
  -- have H₁: perm_convex.edgeND₁₂.toProj = perm_convex.edgeND₃₄.toProj := by
  --   rw [K₁, K₃]
  --   unfold parallel at h₁
  --   exact h₁.symm
  -- have H₂: perm_convex.edgeND₁₂.length = perm_convex.edgeND₃₄.length := by
  --   rw [K₂, K₄]
  --   exact h₂.symm
  -- have H: perm_convex.IsParallelogram_nd := qdr_cvx_is_prg_nd_of_para_eq_length perm_convex H₁ H₂
  -- unfold QuadrilateralND.IsParallelogram_nd at H
  -- rcases H with ⟨para, _⟩
  -- unfold QuadrilateralND.IsParallelogram_para
  -- unfold QuadrilateralND.IsParallelogram_para at para
  -- rcases para with ⟨para₁, para₂⟩
  -- unfold parallel
  -- have K₉: perm_convex.edgeND₁₄.reverse.toProj = qdr_cvx.edgeND₁₂.toProj := by rfl
  -- have K₁₀: perm_convex.edgeND₁₄.reverse.toProj = perm_convex.edgeND₁₄.toProj := by apply SegND.toProj_of_rev_eq_toProj
  -- have K₈: perm_convex.edgeND₂₃.toProj = qdr_cvx.edgeND₃₄.toProj := by rfl
  -- rw [K₁₀] at K₉
  -- unfold parallel at para₁
  -- unfold parallel at para₂
  -- constructor
  -- have key: qdr_cvx.edgeND₁₂.toProj = qdr_cvx.edgeND₃₄.toProj := by
  --   rw [K₉.symm, K₈.symm]
  --   exact para₂
  -- exact key
  -- exact h₁
  -- constructor
  -- exact qdr_cvx.not_collinear₁₂₃
  -- exact qdr_cvx.not_collinear₂₃₄
  -- exact qdr_cvx.not_collinear₃₄₁
  -- exact qdr_cvx.not_collinear₄₁₂

/- Given four points ABCD and Quadrilateral ABCD IsConvex, and AD ∥ BC and AD = BC, Quadrilateral ABCD is a Parallelogram_nd. -/
-- theorem qdr_cvx_is_prg_nd_of_para_eq_length'_variant (h₁ : (SEG_nd A D (QDR_cvx A B C D nd cvx).nd₁₄.out) ∥ (SEG_nd B C (QDR_cvx A B C D nd cvx).nd₂₃.out)) (h₂ : (QDR_cvx A B C D nd cvx).edgeND₁₄.length = (QDR_cvx A B C D nd cvx).edgeND₂₃.length) : (QuadrilateralND.mk_nd nd) IsParallelogram_nd := by
--    unfold QuadrilateralND.IsParallelogram_nd
--    constructor
--    let perm_convex := Quadrilateral_cvx.mk_is_convex (QDR_cvx A B C D nd cvx).perm_is_convex
--    have K₁: perm_convex.edgeND₁₂.toProj = (QDR_cvx A B C D nd cvx).edgeND₂₃.toProj := by rfl
--    have K₂: perm_convex.edgeND₁₂.1.length = (QDR_cvx A B C D nd cvx).edgeND₂₃.1.length := by rfl
--    have j₂: perm_convex.edgeND₃₄ = (QDR_cvx A B C D nd cvx).edgeND₁₄.reverse := by rfl
--    have K₃: perm_convex.edgeND₃₄.toProj = (QDR_cvx A B C D nd cvx).edgeND₁₄.toProj := by
--      rw [j₂]
--      apply SegND.toProj_of_rev_eq_toProj
--    have K₄: perm_convex.edgeND₃₄.1.length = (QDR_cvx A B C D nd cvx).edgeND₁₄.1.length := by
--      rw [j₂]
--      apply SegND.length_of_rev_eq_length
--    have H₁: perm_convex.edgeND₁₂.toProj = perm_convex.edgeND₃₄.toProj := by
--      rw [K₁, K₃]
--      unfold parallel at h₁
--      exact h₁.symm
--    have H₂: perm_convex.edgeND₁₂.1.length = perm_convex.edgeND₃₄.1.length := by
--      rw [K₂, K₄]
--      exact h₂.symm
--    have H: perm_convex.IsParallelogram_nd := qdr_cvx_is_prg_nd_of_para_eq_length perm_convex H₁ H₂
--    unfold QuadrilateralND.IsParallelogram_nd at H
--    rcases H with ⟨para, _⟩
--    unfold QuadrilateralND.IsParallelogram_para
--    unfold QuadrilateralND.IsParallelogram_para at para
--    rcases para with ⟨para₁, para₂⟩
--    unfold parallel
--    have K₉: perm_convex.edgeND₁₄.reverse.toProj = (QDR_cvx A B C D nd cvx).edgeND₁₂.toProj := by rfl
--    have K₁₀: perm_convex.edgeND₁₄.reverse.toProj = perm_convex.edgeND₁₄.toProj := by apply SegND.toProj_of_rev_eq_toProj
--    have K₈: perm_convex.edgeND₂₃.toProj = (QDR_cvx A B C D nd cvx).edgeND₃₄.toProj := by rfl
--    rw [K₁₀] at K₉
--    unfold parallel at para₁
--    unfold parallel at para₂
--    constructor
--    have key: (QDR_cvx A B C D nd cvx).edgeND₁₂.toProj = (QDR_cvx A B C D nd cvx).edgeND₃₄.toProj := by
--      rw [K₉.symm, K₈.symm]
--      exact para₂
--    exact key
--    exact h₁
--    constructor
--    exact (QDR_cvx A B C D nd cvx).not_collinear₁₂₃
--    exact (QDR_cvx A B C D nd cvx).not_collinear₂₃₄
--    exact (QDR_cvx A B C D nd cvx).not_collinear₃₄₁
--    exact (QDR_cvx A B C D nd cvx).not_collinear₄₁₂

/-- Given Quadrilateral_cvx qdr_cvx, and angle₁ = angle₃ and angle₂ = angle₄, qdr_cvx is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_eq_angle_value_eq_angle_value (h₁ : qdr_cvx.angle₁ = qdr_cvx.angle₃) (h₂ : qdr_cvx.angle₂ = qdr_cvx.angle₄) : qdr_cvx.IsParallelogram_nd := by
  unfold QuadrilateralND.IsParallelogram_nd
  constructor
  sorry
  constructor
  exact qdr_cvx.not_collinear₁₂₃
  exact qdr_cvx.not_collinear₂₃₄
  exact qdr_cvx.not_collinear₃₄₁
  exact qdr_cvx.not_collinear₄₁₂

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and ∠DAB = ∠BCD and ∠ABC = ∠CDA, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_of_eq_angle_value_eq_angle_value_variant (h₁ : (ANG D A B (QDR_nd A B C D nd).nd₁₄.out (QDR_nd A B C D nd).nd₁₂.out) = (ANG B C D (QDR_nd A B C D nd).nd₂₃.out.symm (QDR_nd A B C D nd).nd₃₄.out)) (h₂ : (ANG A B C (QDR_nd A B C D nd).nd₁₂.out.symm (QDR_nd A B C D nd).nd₂₃.out) = (ANG C D A (QDR_nd A B C D nd).nd₃₄.out.symm (QDR_nd A B C D nd).nd₁₄.out.symm)) : (QuadrilateralND.mk_nd nd) IsParallelogram_nd := by
   sorry

/-- Given Quadrilateral_cvx qdr_cvx, and qdr_cvx.diag_nd₁₃.1.midpoint = qdr_cvx.diag_nd₂₄.1.midpoint, qdr_cvx is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_nd_of_diag_inx_eq_mid_eq_mid (h' : qdr_cvx.diag_nd₁₃.1.midpoint = qdr_cvx.diag_nd₂₄.1.midpoint) : qdr_cvx.IsParallelogram_nd := by
  unfold QuadrilateralND.IsParallelogram_nd
  constructor
  let midpoint := qdr_cvx.diag_nd₁₃.1.midpoint
  have qdr_cvx_eq_midpoint_of_diag₂₄: qdr_cvx.diag_nd₂₄.1.midpoint = midpoint := by rw [h'.symm]
  have midpoint_Liesint_diag₁₃: midpoint LiesInt qdr_cvx.diag_nd₁₃ := by apply SegND.midpt_lies_int
  have midpoint_Liesint_diag₂₄: midpoint LiesInt qdr_cvx.diag_nd₂₄ := by
    rw [qdr_cvx_eq_midpoint_of_diag₂₄.symm]
    apply SegND.midpt_lies_int
  have nd₁₅: midpoint ≠ qdr_cvx.point₁ := by apply SegND.midpt_ne_source
  have nd₂₅: qdr_cvx.point₂ ≠ midpoint := by
    have h: qdr_cvx.diag_nd₂₄.1.midpoint ≠ qdr_cvx.point₂ := by apply SegND.midpt_ne_source
    rw [qdr_cvx_eq_midpoint_of_diag₂₄] at h
    exact h.symm
  have nd₃₅: midpoint ≠ qdr_cvx.point₃ := by apply SegND.midpt_ne_target
  have nd₄₅: midpoint ≠ qdr_cvx.point₄ := by
    have h: qdr_cvx.diag_nd₂₄.1.midpoint ≠ qdr_cvx.point₄ := by apply SegND.midpt_ne_target
    rw [qdr_cvx_eq_midpoint_of_diag₂₄] at h
    exact h
  have prep₁_pre: (SEG_nd qdr_cvx.point₁ midpoint nd₁₅).length = (SEG_nd midpoint qdr_cvx.point₃ nd₃₅.symm).length :=  dist_target_eq_dist_source_of_midpt (seg := qdr_cvx.diag₁₃)
  have prep₁_pre': (SEG_nd qdr_cvx.point₁ midpoint nd₁₅).length = (SEG_nd midpoint qdr_cvx.point₁ nd₁₅.symm).length := by   apply length_of_rev_eq_length'
  sorry
  constructor
  exact qdr_cvx.not_collinear₁₂₃
  exact qdr_cvx.not_collinear₂₃₄
  exact qdr_cvx.not_collinear₃₄₁
  exact qdr_cvx.not_collinear₄₁₂

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and the midpoint of the diagonal AC and BD is the same, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdr_cvx_is_prg_of_diag_inx_eq_mid_eq_mid_variant (h' : (SEG A C).midpoint = (SEG B D).midpoint) : (QuadrilateralND.mk_nd nd) IsParallelogram_nd := by
  sorry

end criteria_prg_nd_of_qdr_cvx

section property
variable {A B C D : P}
variable {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P)

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
theorem nd₁₂_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₂ ≠ qdr.point₁ := by sorry
  -- have s : qdr.IsConvex := is_convex_of_is_prg_nd qdr h
  -- exact (Quadrilateral_cvx.mk_is_convex s).nd₁₂.out

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, B ≠ A. -/
theorem nd₁₂_of_is_prg_nd_variant (h : ((QDR A B C D).IsParallelogram_nd) ) : B ≠ A := by sorry
  -- have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_nd_variant h
  -- exact (Quadrilateral_cvx.mk_is_convex s).nd₁₂.out

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₃ ≠ qdr.point₂. -/
theorem nd₂₃_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₃ ≠ qdr.point₂ := by sorry
  -- have s : qdr.IsConvex:= is_convex_of_is_prg_nd qdr h
  -- exact (Quadrilateral_cvx.mk_is_convex s).nd₂₃.out

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, C ≠ B. -/
theorem nd₂₃_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : C ≠ B := by sorry
  -- have s : (QDR A B C D) IsConvex := is_convex_of_is_prg_nd_variant h
  -- exact (Quadrilateral_cvx.mk_is_convex s).nd₂₃.out

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₄ ≠ qdr.point₃. -/
theorem nd₃₄_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₄ ≠ qdr.point₃ := by sorry
  -- have s : qdr.IsConvex:= is_convex_of_is_prg_nd qdr h
  -- exact (Quadrilateral_cvx.mk_is_convex s).nd₃₄.out

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, D ≠ C. -/
theorem nd₃₄_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : D ≠ C := by sorry
  -- have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_nd_variant h
  -- exact (Quadrilateral_cvx.mk_is_convex s).nd₃₄.out

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₄ ≠ qdr.point₁. -/
theorem nd₁₄_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₄ ≠ qdr.point₁ := by sorry
  -- have s : qdr.IsConvex:= is_convex_of_is_prg_nd qdr h
  -- exact (Quadrilateral_cvx.mk_is_convex s).nd₁₄.out

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, D ≠ A. -/
theorem nd₁₄_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : D ≠ A := by sorry
  -- have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_nd_variant h
  -- exact (Quadrilateral_cvx.mk_is_convex s).nd₁₄.out

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

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are equal namely (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_abstract qdr h)).length = (SEG_nd qdr.point₃ qdr.point₄ (nd₁₂_of_is_prg_abstract qdr h)).length. -/
theorem eq_length_of_is_prg_nd (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_nd qdr h)).length = (SEG_nd qdr.point₃ qdr.point₄ (nd₃₄_of_is_prg_nd qdr h)).length := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are equal namely (SEG A B).length = (SEG C D).length. -/
theorem eq_length_of_is_prg_nd_variant  (h : (QDR A B C D).IsParallelogram_nd) : (SEG A B).length = (SEG C D).length := by
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are equal namely (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_abstract qdr h)).length = (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_abstract qdr h)).length. -/
theorem eq_length_of_is_prg_nd'  (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_nd qdr h)).length = (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_nd qdr h)).length := by
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

/-- Given Quadrilateral qdr IsPRG_nd, then VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃. -/
theorem eq_vec_of_is_prg_nd (h : qdr.IsParallelogram_nd) : VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃ := sorry

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
variable {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P)
variable {P : Type*} [EuclideanPlane P] (prg_nd : Parallelogram_nd P)

/-- Given Quadrilateral qdr IsPRG_nd, Quadrilateral qdr IsND. -/

theorem nd_is_nd_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.IsND := by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases j: qdr.IsND
  simp only [j, dite_true]
  simp only [j, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, Quadrilateral ABCD IsND. -/
theorem nd_is_nd_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : (QDR A B C D).IsND := nd_is_nd_of_is_prg_nd (QDR A B C D) h

/-- Given Quadrilateral qdr IsPRG_nd, Quadrilateral qdr IsND.-/
theorem nd_is_nd_of_is_prg_nd_restated (h : qdr.IsParallelogram_nd) : (QDR qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄).IsND := nd_is_nd_of_is_prg_nd_variant h

theorem nd_is_nd_of_is_prg_nd_restated_variant (h : (QDR A B C D).IsParallelogram_nd) : (QDR A B C D).IsND := nd_is_nd_of_is_prg_nd_variant h

/-- Given Quadrilateral qdr IsPRG_nd, qdr IsConvex. -/
theorem nd_is_convex_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.IsConvex := by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases j: qdr.IsND
  unfold Quadrilateral.IsConvex
  simp only [j, dite_true]
  simp only [j, dite_true] at h
  unfold QuadrilateralND.IsParallelogram_nd at h
  --have p: criteria_cvx.is_convex_of_diag_inx_lies_int' (P := P) := by
    --sorry
  sorry
  simp only [j, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, Quadrilateral ABCD IsConvex. -/
theorem nd_is_convex_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : (QDR A B C D) IsConvex := is_convex_of_is_prg_nd_variant h

/- Given Quadrilateral qdr IsPRG_nd, qdr IsConvex. -/
-- theorem nd_is_convex_of_is_prg_nd_restated (h : qdr.IsParallelogram_nd) : (QuadrilateralND.mk_nd (nd_is_nd_of_is_prg_nd_restated qdr h)) IsConvex := by
--   sorry

/- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, Quadrilateral ABCD IsConvex. -/
-- theorem nd_is_convex_of_is_prg_nd_restated_variant (h : (QDR A B C D).IsParallelogram_nd) : (QuadrilateralND.mk_nd (nd_is_nd_of_is_prg_nd_restated (QDR A B C D) h)) IsConvex := nd_is_convex_of_is_prg_nd_restated (QDR A B C D) h

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
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases j: qdr.IsND
  simp only [j, dite_true] at h
  unfold QuadrilateralND.IsParallelogram_nd at h
  rcases h with ⟨a,_⟩
  unfold QuadrilateralND.IsParallelogram_para at a
  rcases a with ⟨p,_⟩
  exact p
  simp only [j, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are parallel namely AB ∥ CD. -/
theorem nd_para_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ (SEG_nd C D (nd₃₄_of_is_prg_nd_variant h)) := para_of_is_prg_nd_variant h

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are parallel namely (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_abstract qdr h)) ∥ (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_abstract qdr h)). -/
theorem nd_para_of_is_prg_nd' (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_nd qdr h)) ∥ (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_nd qdr h)):= by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases j: qdr.IsND
  simp only [j, dite_true] at h
  unfold QuadrilateralND.IsParallelogram_nd at h
  rcases h with ⟨a,_⟩
  unfold QuadrilateralND.IsParallelogram_para at a
  rcases a with ⟨_,q⟩
  exact q
  simp only [j, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are parallel namely AD ∥ BC. -/
theorem nd_para_of_is_prg_nd'_variant (h : (QDR A B C D).IsParallelogram_nd) : (SEG_nd A D (nd₁₄_of_is_prg_nd_variant h)) ∥ SEG_nd B C (nd₂₃_of_is_prg_nd_variant h) := para_of_is_prg_nd'_variant h

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are equal namely (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_abstract qdr h)).length = (SEG_nd qdr.point₃ qdr.point₄ (nd₁₂_of_is_prg_abstract qdr h)).length. -/
theorem nd_eq_length_of_is_prg_nd (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_nd qdr h)).length = (SEG_nd qdr.point₃ qdr.point₄ (nd₃₄_of_is_prg_nd qdr h)).length := by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases j: qdr.IsND
  simp only [j, dite_true] at h
  unfold QuadrilateralND.IsParallelogram_nd at h
  rcases h with ⟨a,b⟩
  unfold QuadrilateralND.IsParallelogram_para at a
  rcases a with ⟨p,q⟩
  unfold parallel at p q

  rcases b with ⟨b₁,b₂,b₃,b₄⟩
  sorry
  simp only [j, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are equal namely (SEG A B).length = (SEG C D).length. -/
theorem nd_eq_length_of_is_prg_nd_variant  (h : (QDR A B C D).IsParallelogram_nd) : (SEG A B).length = (SEG C D).length := eq_length_of_is_prg_nd_variant h

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are equal namely (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_abstract qdr h)).length = (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_abstract qdr h)).length. -/
theorem nd_eq_length_of_is_prg_nd'  (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_nd qdr h)).length = (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_nd qdr h)).length := by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases j: qdr.IsND
  simp only [j, dite_true] at h
  unfold QuadrilateralND.IsParallelogram_nd at h
  rcases h with ⟨a,b⟩
  unfold QuadrilateralND.IsParallelogram_para at a
  rcases a with ⟨p,q⟩
  unfold parallel at p q
  rcases b with ⟨b₁,b₂,b₃,b₄⟩
  sorry
  simp only [j, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are equal namely (SEG A D).length = (SEG B C).length. -/
theorem nd_eq_length_of_is_prg_nd'_variant  (h : (QDR A B C D).IsParallelogram_nd) : (SEG A D).length = (SEG B C).length := eq_length_of_is_prg_nd'_variant h

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

/- Given Quadrilateral qdr IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ = (SEG qdr.point₁ qdr.point₃).midpoint.-/
-- theorem nd_eq_midpt_of_diag_inx_of_is_prg_nd (h : qdr.IsParallelogram_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ (nd_is_nd_of_is_prg_nd_restated qdr h) (nd_is_convex_of_is_prg_nd_restated qdr h)) = (SEG qdr.point₁ qdr.point₃).midpoint :=
--   sorry

/- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx A B C D = (SEG A C).midpoint. -/
-- theorem nd_eq_midpt_of_diag_inx_of_is_prg_nd_variant (h : (QDR A B C D).IsParallelogram_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (nd_is_nd_of_is_prg_nd_restated (QDR A B C D) h) (nd_is_convex_of_is_prg_nd_restated (QDR A B C D) h)) = (SEG A C).midpoint := by
--   have h : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ SEG_nd C D (nd₃₄_of_is_prg_nd_variant h) := para_of_is_prg_nd_variant h
--   sorry

/- Given Quadrilateral qdr IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ = (SEG qdr.point₂ qdr.point₄).midpoint. -/
-- theorem nd_eq_midpt_of_diag_inx_of_is_prg_nd' (h : qdr.IsParallelogram_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ (nd_is_nd_of_is_prg_nd_restated qdr h) (nd_is_convex_of_is_prg_nd_restated qdr h)) = (SEG qdr.point₂ qdr.point₄).midpoint :=
--   sorry

/- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx A B C D = (SEG B D).midpoint. -/
-- theorem nd_eq_midpt_of_diag_inx_of_is_prg_nd'_variant (h : (QDR A B C D).IsParallelogram_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (nd_is_nd_of_is_prg_nd_restated (QDR A B C D) h) (nd_is_convex_of_is_prg_nd_restated (QDR A B C D) h)) = (SEG B D).midpoint :=
--   have h : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ SEG_nd C D (nd₃₄_of_is_prg_nd_variant h) := para_of_is_prg_nd_variant h
--   sorry

/-- Given Quadrilateral qdr IsPRG_nd, the midpoints of the diagonals are the same. -/
theorem nd_eq_midpt_of_diag_of_is_prg (h : qdr.IsParallelogram_nd) : (SEG qdr.point₁ qdr.point₃).midpoint = (SEG qdr.point₂ qdr.point₄).midpoint := by
  sorry

/-- Given four points A B C D and Quadrilateral ABCD IsPRG_nd, the midpoints of the diagonals are the same. -/
theorem nd_eq_midpt_of_diag_of_is_prg_variant (h : (QDR A B C D).IsParallelogram_nd) : (SEG A C).midpoint = (SEG B D).midpoint := eq_midpt_of_diag_of_is_prg (QDR A B C D) h

/-- Given Quadrilateral qdr IsPRG_nd, then Quadrilateral IsPRG. -/
theorem nd_prg_nd_is_prg (h : qdr.IsParallelogram_nd) : qdr.IsParallelogram := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, then Quadrilateral ABCD IsPRG. -/
theorem nd_prg_nd_is_prg_variant (h : (QDR A B C D).IsParallelogram_nd) : (QDR A B C D).IsParallelogram := nd_prg_nd_is_prg (QDR A B C D) h

/-- Given Quadrilateral qdr IsPRG_nd, then VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃. -/
theorem nd_eq_vec_of_is_prg_nd (h : qdr.IsParallelogram_nd) : VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃ := nd_prg_nd_is_prg qdr h

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
  repeat rw [Seg.length_eq_norm_toVec]
  repeat rw [seg_tovec_eq_vec]
  dsimp
  rw [← vec_add_vec qdr.point₁ qdr.point₂ qdr.point₃]
  rw [← vec_add_vec qdr.point₂ qdr.point₃ qdr.point₄]
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

-/
