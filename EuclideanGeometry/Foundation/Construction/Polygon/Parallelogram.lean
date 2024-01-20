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
There're some structural problems need further discuss.
1. In our earlier implement, we tried to claim most theorems in two different form. One of them accept arguments like (A B C D : P) ((QDR A B C D) satisfies...), the other accept arguments like (qdr : Quadrilateral) (qdr satisfies...). We called first one 'variant'. But it's seems that we can delete all 'variant's and force user to use theorems in format of (some_prg_theorem (QDR A B C D) some_conditions), in this way we can get rid of most variants.
The reason we keep the variant in our file due to problem 3. While IsPrgND is not iff with Prg_nd. Maybe some instance can solve this.
2. We have quite much criteria from Prg and/or Qdr_nd to PrgND. For user's ease, we need to provide some make methods. It's clear we should have a method like (PRG A B C D (QDR A B C D is PrgND)), It's the most intuitive make method. We should discuss the necessity of other make methods. For example, do we need a method accepts arguments qdr_cvx and (qdr_cvx satisfies IsPara)?
3. In other structures we define predicate IsXXX then define structure XXX with it's element IsXXX. Now the PrgND is not involving new predicate, so the definition of 'IsPrgND' is not related to structure PrgND naturally. How to solve this? Shall we simply provide more instances?
4. the naming of predicate currently called 'GPt_PRG_nd' and 'IsParaPara_PRG_nd', and the naming of 'IsParaPara' and 'GPt' needs discuss.
-/

/-

Recall certain definitions concerning quadrilaterals:

A QDR consists of four points; it is the generalized quadrilateral formed by these four points.

A QDR_nd is QDR that the points that adjacent is not same, namely point₂ ≠ point₁, point₃ ≠ point₂, point₄ ≠ point₃, and point₁ ≠ point₁.

We take notice that, by the well-known fact that non-trivial parallelograms are indeed convex, and considering the fine qualities of convex quadrilaterals, we decide to define parallelogram_nds as a parallelogram that is convex, while the class of parallelograms permit degenerate cases. In this way, the structure of parallelogram_nd becomes natural in both aspects of quadrilaterals and parallelograms. We do take notice that there are more straightforward ways to descibe parallelograms, such as IsPara and InGPos mentioned later. So it is due to user-friendliness that we leave quite a number of shortcuts to ease theorem-proving.

In this section we define two types of parallelograms. 'parallel_nd' deals with those quadrilaterals we commomly call parallelogram (convex), and 'parallel' with more general cases (we permite degenerate cases).

-/

-- /-- A QuadrilateralND satisfies IsPara if two sets of opposite sides are parallel respectively. -/
-- @[pp_dot]
-- def QuadrilateralND.IsParaPara {P : Type*} [EuclideanPlane P] (qdr_nd : QuadrilateralND P) : Prop := ( qdr_nd.edgeND₁₂ ∥ qdr_nd.edgeND₃₄) ∧ (qdr_nd.edgeND₁₄ ∥ qdr_nd.edgeND₂₃)

-- -- scoped postfix : 50 "IsParaPara" => QuadrilateralND.IsParaPara

-- /-- A quadrilateral satisfies IsPara if it is a QuadrilateralND and satisfies IsPara as a QuadrilateralND. -/
-- @[pp_dot]
-- def Quadrilateral.IsParaPara {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
--   by_cases h : qdr.IsND
--   · exact (QuadrilateralND.mk_nd h).IsParaPara
--   · exact False

/-- A quadrilateral satisfies IsPara if it is a QuadrilateralND and satisfies IsPara as a QuadrilateralND. -/
@[pp_dot]
def Quadrilateral.IsParaPara {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases h : qdr.IsND
  · have qdr_nd : QuadrilateralND P := QDR_nd' h
    exact (qdr_nd.edgeND₁₂ ∥ qdr_nd.edgeND₃₄) ∧ (qdr_nd.edgeND₄₁ ∥ qdr_nd.edgeND₂₃)
  · exact False

/-- A quadrilateral is called parallelogram if VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃.-/
@[pp_dot]
def Quadrilateral.IsPrg {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃

scoped postfix : 50 "IsPrg" => Quadrilateral.IsPrg

-- `shall we define this?`
-- /-- A QuadrilateralND is called parallelogram if VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃.-/
-- @[pp_dot]
-- def QuadrilateralND.IsPrg {P : Type*} [EuclideanPlane P] (qdr_nd : QuadrilateralND P) : Prop := VEC qdr_nd.point₁ qdr_nd.point₂ = VEC qdr_nd.point₄ qdr_nd.point₃

-- scoped postfix : 50 "nd_IsPrg" => QuadrilateralND.IsPrg

/-- We define parallelogram as a structure. -/
@[ext]
structure Parallelogram (P : Type*) [EuclideanPlane P] extends Quadrilateral P where
  is_parallelogram : toQuadrilateral IsPrg

/-- Make a parallelogram with 4 points on a plane, and using condition IsPrg. -/
def Parallelogram.mk_pt_pt_pt_pt {P : Type*} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D) IsPrg) : Parallelogram P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h

scoped notation "PRG" => Parallelogram.mk_pt_pt_pt_pt

/-- Make a parallelogram with a quadrilateral, and using condition IsPrg. -/
def Parallelogram.mk_isPrg {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsPrg) : Parallelogram P where
  toQuadrilateral := qdr
  is_parallelogram := h

scoped notation "PRG'" => Parallelogram.mk_isPrg

/-- Vectors point₁ point₂ and point₄ point₃ in a parallelogram are equal. -/
theorem Parallelogram.eq_vec_of_isPrg {P : Type*} [EuclideanPlane P] {prg : Parallelogram P} : VEC prg.point₁ prg.point₂ = VEC prg.point₄ prg.point₃ := prg.is_parallelogram

/-- Vectors point₁ point₄ and point₂ point₃ in a parallelogram are equal. -/
theorem Parallelogram.eq_vec_of_isPrg' {P : Type*} [EuclideanPlane P] {prg : Parallelogram P} : VEC prg.point₁ prg.point₄ = VEC prg.point₂ prg.point₃ := by rw [← vec_add_vec prg.point₁ prg.point₂ prg.point₄, ← vec_add_vec prg.point₂ prg.point₄ prg.point₃, prg.is_parallelogram, add_comm]

/-- A parallelogram which satisfies Prallelogram.InGPos satisfies IsParaPara. -/
theorem Parallelogram.parapara_of_gpos {P : Type*} [EuclideanPlane P] {prg : Parallelogram P} (InGPos : prg.InGPos): prg.IsParaPara:= by
  unfold Quadrilateral.IsParaPara
  sorry

/-- A parallelogram which satisfies Prallelogram.InGPos is convex. -/
theorem Parallelogram.cvx_of_gpos {P : Type*} [EuclideanPlane P] {prg : Parallelogram P} (InGPos : prg.InGPos): prg.IsConvex:= by sorry

/-- We define parallelogram_nd as a structure. -/
@[ext]
structure ParallelogramND (P : Type*) [EuclideanPlane P] extends Quadrilateral_cvx P, Parallelogram P

/-- A quadrilateral is parallelogram_nd if it is both convex and satisfies qualities of a parallelogram. This definition is in agreement with the structure above. -/
@[pp_dot]
def Quadrilateral.IsPrgND {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := qdr IsConvex ∧ qdr IsPrg

scoped postfix : 50 "IsPrgND" => Quadrilateral.IsPrgND

-- /-- A QuadrilateralND is parallelogram_nd if its toQuadrilateral is both convex and satisfies qualities of a parallelogram. -/
-- @[pp_dot]
-- def QuadrilateralND.IsPrgND {P : Type*} [EuclideanPlane P] (qdr_nd : QuadrilateralND P) : Prop := Quadrilateral.IsPrgND qdr_nd.toQuadrilateral

-- scoped postfix : 50 "nd_IsPrgND" => QuadrilateralND.IsPrgND

theorem QuadrilateralND.parapara_iff_para_para {P : Type*} [EuclideanPlane P] (qdr_nd : QuadrilateralND P) : (qdr_nd.IsParaPara) ↔ (qdr_nd.edgeND₁₂ ∥ qdr_nd.edgeND₃₄) ∧ (qdr_nd.edgeND₄₁ ∥ qdr_nd.edgeND₂₃) := by
  constructor
  unfold Quadrilateral.IsParaPara
  simp only [dite_true, qdr_nd.nd, and_imp]
  exact fun a a_1 ↦ { left := a, right := a_1 }
  unfold Quadrilateral.IsParaPara
  simp only [dite_true, qdr_nd.nd,and_imp]
  exact fun a a_1 ↦ { left := a, right := a_1 }

/-- A parallelogram_nd satisfies InGPos. -/
theorem ParallelogramND.gpos_of_prgnd {P : Type*} [EuclideanPlane P] (prg_nd : ParallelogramND P) : prg_nd.InGPos := ⟨prg_nd.not_collinear₁₂₃, prg_nd.not_collinear₂₃₄, prg_nd.not_collinear₃₄₁, prg_nd.not_collinear₄₁₂⟩

/-- A parallelogram_nd satisfies IsParaPara. -/
theorem ParallelogramND.parapara_of_prgnd {P : Type*} [EuclideanPlane P] (prg_nd : ParallelogramND P) : prg_nd.IsParaPara := by
  unfold Quadrilateral.IsParaPara
  simp only [dite_true, prg_nd.nd]
  unfold Parallel
  constructor
  have h: VEC prg_nd.point₁ prg_nd.point₂ = VEC prg_nd.point₄ prg_nd.point₃ := prg_nd.is_parallelogram
  have p: (VEC_nd prg_nd.point₁ prg_nd.point₂ prg_nd.nd₁₂.out).toProj = (VEC_nd prg_nd.point₄ prg_nd.point₃ prg_nd.nd₃₄.out.symm).toProj := by

    sorry
  sorry
  sorry

def ParallelogramND.mk_pt_pt_pt_pt {P : Type*} [EuclideanPlane P] (A B C D : P) (h: (QDR A B C D) IsPrgND) : ParallelogramND P where
  toQuadrilateral := (QDR A B C D)
  nd := h.left; convex := h.left
  is_parallelogram := h.right

scoped notation "PRG_nd" => ParallelogramND.mk_pt_pt_pt_pt

def ParallelogramND.mk_isPrgND {P : Type*} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsPrgND) : ParallelogramND P where
  toQuadrilateral := qdr
  nd := h.left; convex := h.left
  is_parallelogram := h.right

scoped notation "PRG_nd'" => ParallelogramND.mk_isPrgND

/-
 Using the property above, we leave such a shortcut in a way people usually sense a parallelogram. A quadrilateral A B C D is parallelogram_nd if it is ND, is a parallelogram, and satisfies InGPos.
def ParallelogramND.mk_prgND_of_gpos {P : Type*} [EuclideanPlane P] {prg : Parallelogram P} (gpos: prg.InGPos): ParallelogramND P where
  toQuadrilateral := prg.toQuadrilateral
  nd := sorry
  convex := sorry
  is_parallelogram := sorry

`name maybe changed`
scoped notation "non_triv_PRG_nd" => ParallelogramND.mk_prgND_of_gpos

A quadrilateral A B C D is parallelogram_nd if it is ND, is a parallelogram, and satisfies IsParaPara.
--def ParallelogramND.mk_prgND_of_para {P : Type*} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D).IsND) (h': (QDR A B C D) IsPrg) (IsPara: (QDR_nd A B C D h).IsParaPara): ParallelogramND P where
  point₁ := A; point₂ := B; point₃ := C; point₄ := D
  nd := h
  convex := sorry
  is_parallelogram := h'

`name maybe changed`
scoped notation "IsParaPara_PRG_nd" => ParallelogramND.mk_parallelogram_para

here is two theorem using first version of definition of PRG_nd, may not useful currently.
theorem Quadrilateral.IsPrg_nd_redef {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P) (h: qdr.IsND) (h': qdr IsPrg) (h': (((QuadrilateralND.mk_nd h).angle₁.value.IsPos ∧ (QuadrilateralND.mk_nd h).angle₃.value.IsPos) ∨ ((QuadrilateralND.mk_nd h).angle₁.value.IsNeg ∧ (QuadrilateralND.mk_nd h).angle₃.value.IsNeg) ∨ ((QuadrilateralND.mk_nd h).angle₂.value.IsPos ∧ (QuadrilateralND.mk_nd h).angle₄.value.IsPos) ∨ ((QuadrilateralND.mk_nd h).angle₂.value.IsNeg ∧ (QuadrilateralND.mk_nd h).angle₄.value.IsNeg))) : (QuadrilateralND.mk_nd h).IsPrgND := sorry

theorem Parallelogram.parallelogramIs_nd_redef {P : Type*} [EuclideanPlane P] (prg : Parallelogram P) (h': prg.1.IsND) (k: ((QuadrilateralND.mk_nd h').angle₁.value.IsPos ∧ (QuadrilateralND.mk_nd h').angle₃.value.IsPos) ∨ ((QuadrilateralND.mk_nd h').angle₁.value.IsNeg ∧ (QuadrilateralND.mk_nd h').angle₃.value.IsNeg) ∨ ((QuadrilateralND.mk_nd h').angle₂.value.IsPos ∧ (QuadrilateralND.mk_nd h').angle₄.value.IsPos) ∨ ((QuadrilateralND.mk_nd h').angle₂.value.IsNeg ∧ (QuadrilateralND.mk_nd h').angle₄.value.IsNeg)) : (QuadrilateralND.mk_nd h').IsPrgND := sorry
-/

section perm

variable {P : Type*} [EuclideanPlane P]
variable (qdr : Quadrilateral P)
variable (qdr_nd : QuadrilateralND P)
variable (qdr_cvx : Quadrilateral_cvx P)
variable (prg : Parallelogram P)

/-- If a quadrilateral is a parallelogram, then its perm is also a parallelogram. -/
theorem qdr_isPrg_iff_perm_isPrg : (qdr.IsPrg) ↔ ((qdr.perm).IsPrg) := by
  unfold Quadrilateral.perm
  unfold Quadrilateral.IsPrg
  simp only
  unfold Vec.mkPtPt
  rw [eq_comm]
  refine (eq_iff_eq_of_sub_eq_sub ?H)
  rw [vsub_sub_vsub_comm]

/-- If a quadrilateral is a parallelogram_nd, then its perm is also a parallelogram_nd. -/
theorem prgND_iff_perm_prgND : (qdr.IsPrgND) ↔ ((qdr.perm).IsPrgND) := by sorry

/-- If a quadrilateral satisfies IsParaPara, then its perm also satisfies IsParaPara. -/
theorem para_iff_perm_para : (qdr.IsParaPara) ↔ ((qdr.perm).IsParaPara) := by sorry

/-- If a quadrilateral_nd satisfies IsParaPara, then its perm also satisfies IsParaPara. -/
theorem qdrND_IsParaPara_iff_perm_IsParaPara : (qdr_nd.IsParaPara) ↔ ((qdr_nd.perm).IsParaPara) := by sorry

/-- If a quadrilateral satisfies IsParaPara, then its perm also satisfies IsParaPara. -/
theorem qdr_gpos_iff_perm_gpos : (qdr.InGPos) ↔ ((qdr.perm).InGPos) := by sorry

end perm

section flip

variable {P : Type*} [EuclideanPlane P]
variable (qdr : Quadrilateral P)
variable (qdr_nd : QuadrilateralND P)
variable (qdr_cvx : Quadrilateral_cvx P)
variable (prg : Parallelogram P)

/-- If a quadrilateral is a parallelogram, then its flip is also a parallelogram. -/
theorem qdr_isPrg_iff_flip_isPrg : (qdr.IsPrg) ↔ ((qdr.flip).IsPrg) := by
  unfold Quadrilateral.flip
  unfold Quadrilateral.IsPrg
  simp only
  unfold Vec.mkPtPt
  refine (eq_iff_eq_of_sub_eq_sub ?H)
  sorry

/-- If a quadrilateral is a parallelogram_nd, then its flip is also a parallelogram_nd. -/
theorem qdr_isPrgND_iff_qdr_isPrgND : (qdr.IsPrgND) ↔ ((qdr.flip).IsPrgND) := by
  sorry

/-- If a quadrilateral satisfies IsParaPara, then its flip also satisfies IsParaPara. -/
theorem qdr_IsParaPara_iff_flip_IsParaPara : (qdr.IsParaPara) ↔ ((qdr.flip).IsParaPara) := by sorry

/-- If a quadrilateral_nd satisfies IsParaPara, then its flip also satisfies IsParaPara. -/
theorem qdrND_IsParaPara_iff_flip_IsParaPara : (qdr_nd.IsParaPara) ↔ ((qdr_nd.flip).IsParaPara) := by sorry

/-- If a quadrilateral satisfies IsParaPara, then its flip also satisfies IsParaPara. -/
theorem qdr_gpos_iff_flip_gpos : (qdr.InGPos) ↔ ((qdr.flip).InGPos) := by sorry

end flip

section criteria_prgND_of_prg

variable {P : Type*} [EuclideanPlane P]
variable (qdr_nd : QuadrilateralND P)
variable (prg : Parallelogram P)

/-- If the 2nd, 3rd and 4th points of a parallelogram are not collinear, then it is a parallelogram_nd. -/
theorem isPrgND_of_prg_not_collinear₁ (h : ¬ Collinear prg.point₂ prg.point₃ prg.point₄) : prg.IsPrgND := by
  sorry

/-- If the 3rd, 4th and 1st points of a parallelogram are not collinear, then it is a parallelogram_nd. -/
theorem isPrgND_of_prg_not_collinear₂ (h: ¬ Collinear prg.point₃ prg.point₄ prg.point₁) : prg.IsPrgND := by
  sorry

/-- If the 4th, 1st and 2nd points of a parallelogram are not collinear, then it is a parallelogram_nd. -/
theorem isPrgND_of_prg_not_collinear₃ (h: ¬ Collinear prg.point₄ prg.point₁ prg.point₂) : prg.IsPrgND := by
  sorry

/-- If the 1st, 2nd and 3rd points of a parallelogram are not collinear, then it is a parallelogram_nd. -/
theorem isPrgND_of_prg_not_collinear₄ (h: ¬ Collinear prg.point₁ prg.point₂ prg.point₃) : prg.IsPrgND := by
  sorry

/- We leave these four theorems as interface for the user. They are simply replica of the theorems above. -/
theorem prg_isPrgND_iff_not_collinear₁ : prg.IsPrgND ↔ (¬ Collinear prg.point₂ prg.point₃ prg.point₄) := sorry

theorem prg_isPrgND_iff_not_collinear₂ : prg.IsPrgND ↔ (¬ Collinear prg.point₃ prg.point₄ prg.point₁) := sorry

theorem prg_isPrgND_iff_not_collinear₃ : prg.IsPrgND ↔ (¬ Collinear prg.point₄ prg.point₁ prg.point₂) := sorry

theorem prg_isPrgND_iff_not_collinear₄ : prg.IsPrgND ↔ (¬ Collinear prg.point₁ prg.point₂ prg.point₃) := sorry

end criteria_prgND_of_prg

/- `besides these, we also need the make method from qdr and qdr_nd to prg_nd `-/

-- `the form of all the codes above needs more discussion`

section criteria_prgND_of_qdrND

variable {P : Type*} [EuclideanPlane P]
variable {A B C D : P} (nd : (QDR A B C D).IsND)
variable (qdr : Quadrilateral P) (qdr_nd : QuadrilateralND P)

/-- If a QuadrilateralND satisfies IsParaPara and its 1st, 2nd and 3rd points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_parapara_not_collinear₄ (h: qdr_nd.IsParaPara) (notcollinear : ¬ Collinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃) : qdr_nd.IsPrgND := by
  sorry

/-- If a QuadrilateralND satisfies IsParaPara and its 2nd, 3rd and 4th points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_parapara_not_collinear₁ (h: qdr_nd.IsParaPara) (notcollinear : ¬ Collinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) : qdr_nd.IsPrgND := by
  sorry

/-- If a QuadrilateralND satisfies IsParaPara and its 3rd, 4th and 1st points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_parapara_not_collinear₂ (h: qdr_nd.IsParaPara) (notcollinear : ¬ Collinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁) : qdr_nd.IsPrgND := by
  sorry

/-- If a QuadrilateralND satisfies IsParaPara and its 4th, 1st and 2nd points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_parapara_not_collinear₃ (h: qdr_nd.IsParaPara) (notcollinear : ¬ Collinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂) : qdr_nd.IsPrgND := sorry

/-- If the 1st, 3rd and 2nd, 4th angle of a QuadrilateralND are equal in value respectively, and its 1st, 2nd and 3rd points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_eq_angle_value_eq_angle_value_not_collinear₄ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcollinear : ¬ Collinear qdr_nd.point₁ qdr_nd.point₂ qdr_nd.point₃) : qdr_nd.IsPrgND := by
  sorry

/-- If the 1st, 3rd and 2nd, 4th angle of a QuadrilateralND are equal in value respectively, and its 2nd, 3rd and 4th points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_eq_angle_value_eq_angle_value_not_collinear₁ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcollinear : ¬ Collinear qdr_nd.point₂ qdr_nd.point₃ qdr_nd.point₄) : qdr_nd.IsPrgND := by sorry

/-- If the 1st, 3rd and 2nd, 4th angle of a QuadrilateralND are equal in value respectively, and its 3rd, 4th and 1st points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_eq_angle_value_eq_angle_value_not_collinear₂ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcollinear : ¬ Collinear qdr_nd.point₃ qdr_nd.point₄ qdr_nd.point₁) : qdr_nd.IsPrgND := by sorry

/-- If the 1st, 3rd and 2nd, 4th angle of a QuadrilateralND are equal in value respectively, and its 4th, 1st and 2nd points are not collinear, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_eq_angle_value_eq_angle_value_not_collinear₃ (h₁ : qdr_nd.angle₁.value = qdr_nd.angle₃.value) (h₂ : qdr_nd.angle₂.value = qdr_nd.angle₄.value) (notcollinear : ¬ Collinear qdr_nd.point₄ qdr_nd.point₁ qdr_nd.point₂) : qdr_nd.IsPrgND := by sorry

/-- If edgeND₁₂, edgeND₃₄ and edgeND₁₄, edgeND₂₃ of a QuadrilateralND are equal in value respectively, and angle₁ and angle₃ are of the same sign, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_eq_length_eq_length_eq_angle_sign (h₁ : qdr_nd.edgeND₁₂.length = qdr_nd.edgeND₃₄.length) (h₂ : qdr_nd.edgeND₄₁.length = qdr_nd.edgeND₂₃.length) (h : (qdr_nd.angle₁.value.IsPos ∧ qdr_nd.angle₃.value.IsPos) ∨ (qdr_nd.angle₁.value.IsNeg ∧ qdr_nd.angle₃.value.IsNeg)) : qdr_nd.IsPrgND := by sorry

/-- If edgeND₁₂, edgeND₃₄ and edgeND₁₄, edgeND₂₃ of a QuadrilateralND are equal in value respectively, and angle₂ and angle₄ are of the same sign, then it is a parallelogram_nd. -/
theorem qdrND_is_prgND_of_eq_length_eq_length_eq_angle_sign' (h₁ : qdr_nd.edgeND₁₂.length = qdr_nd.edgeND₃₄.length) (h₂ : qdr_nd.edgeND₄₁.length = qdr_nd.edgeND₂₃.length) (h : (qdr_nd.angle₂.value.IsPos ∧ qdr_nd.angle₄.value.IsPos) ∨ (qdr_nd.angle₂.value.IsNeg ∧ qdr_nd.angle₄.value.IsNeg)) : qdr_nd.IsPrgND := by sorry

end criteria_prgND_of_qdrND

section criteria_prg_of_qdrND

variable {P : Type*} [EuclideanPlane P]
variable {A B C D: P}
variable (nd : (QDR A B C D).IsND)
variable (cvx : (QDR A B C D).IsConvex)
variable {P : Type*} [EuclideanPlane P] (qdr_nd : QuadrilateralND P)
variable {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P)

-- `why this theorem used two set of parallel and equal?`
/-- If edgeND₁₂ and edgeND₃₄ of a QuadrilateralND are equal in value and parallel, and so do edgeND₁₄ and edgeND₂₃, then it is a parallelogram. -/
theorem qdrND_is_prg_of_parapara_eq_length_eq_length (h : qdr_nd.IsParaPara) (h₂ : qdr_nd.edgeND₁₂.length = qdr_nd.edgeND₃₄.length) (H₂ : qdr_nd.edgeND₄₁.length = qdr_nd.edgeND₂₃.length): qdr_nd.IsPrg := by
  sorry

/-- If the midpoint of the two diags of a QuadrilateralND are exactly the same, then it is a parallelogram. -/
theorem qdrND_is_prg_of_diag_inx_eq_midpt_eq_midpt (h' : (qdr_nd.diag₁₃).midpoint = (qdr_nd.diag₂₄).midpoint) : qdr_nd.IsPrg := by
  sorry

/-- If the midpoint of AC and BD are exactly the same, then QuadrilateralND A B C D is a parallelogram. -/
theorem qdrND_is_prg_of_diag_inx_eq_midpt_eq_midpt_variant (h' : (SEG A C).midpoint = (SEG B D).midpoint) : (QuadrilateralND.mk_nd nd).IsPrg := by
  sorry

end criteria_prg_of_qdrND

section criteria_prgND_of_qdrcvx

variable {P : Type*} [EuclideanPlane P]
variable {A B C D : P}
variable (nd : (QDR A B C D).IsND)
variable (cvx : (QDR A B C D).IsConvex)
variable {P : Type*} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P)
variable {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P)

/-- If edgeND₁₂ and edgeND₃₄ of a quadrilateral_cvx are parallel, and so do edgeND₁₄ and edgeND₂₃, then it is a parallelogram_nd. -/
theorem qdrcvx_is_prgND_of_parapara (h₁ : qdr_cvx.IsParaPara) : qdr_cvx.IsPrgND := by sorry

/-- If edgeND₁₂ and edgeND₃₄ of a quadrilateral_cvx are equal in length, and so do edgeND₁₄ and edgeND₂₃, then it is a parallelogram_nd. -/
theorem qdrcvx_is_prgND_of_eq_length_eq_length (h₁ : qdr_cvx.edgeND₁₂.length = qdr_cvx.edgeND₃₄.length) (h₂ : qdr_cvx.edgeND₄₁.length = qdr_cvx.edgeND₂₃.length) : qdr_cvx.IsPrgND := by sorry

/-- If edgeND₁₂ and edgeND₃₄ of a quadrilateral_cvx are not only equal in length but also parallel, then it is a parallelogram_nd. -/
theorem qdrcvx_is_prgND_of_para_eq_length (h₁ : qdr_cvx.edgeND₁₂ ∥ qdr_cvx.edgeND₃₄) (h₂ : qdr_cvx.edgeND₁₂.length = qdr_cvx.edgeND₃₄.length) : qdr_cvx.IsPrgND := by sorry

/-- If edgeND₄₁ and edgeND₂₃ of a quadrilateral_cvx are not only equal in length but also parallel, then it is a parallelogram_nd. -/
theorem qdrcvx_is_prgND_of_para_eq_length' (h₁ : qdr_cvx.edgeND₄₁ ∥ qdr_cvx.edgeND₂₃) (h₂ : qdr_cvx.edgeND₄₁.length = qdr_cvx.edgeND₂₃.length) : qdr_cvx.IsPrgND := by sorry

/-- If angle₁ and angle₃ of a quadrilateral_cvx are equal in value, and so do angle₂ and angle₄, then it is a parallelogram_nd. -/
theorem qdrcvx_is_prgND_of_eq_angle_value_eq_angle_value (h₁ : qdr_cvx.angle₁.value = qdr_cvx.angle₃.value) (h₂ : qdr_cvx.angle₂.value = qdr_cvx.angle₄.value) : qdr_cvx.IsPrgND := by sorry

/-- If the midpoint of the two diags of a quadrilateral_cvx are exactly the same, then it is a parallelogram_nd. -/
theorem qdrcvx_is_prgND_of_diag_eq_midpt (h' : qdr_cvx.diag_nd₁₃.midpoint = qdr_cvx.diag_nd₂₄.midpoint) : qdr_cvx.IsPrgND := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and the midpoint of the diagonal AC and BD is the same, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem qdrcvx_is_prgND_of_diag_eq_midpt_variant (h' : (SEG A C).midpoint = (SEG B D).midpoint) : (QDR_cvx' cvx).IsPrgND := by
  sorry

end criteria_prgND_of_qdrcvx

section property

variable {P : Type*} [EuclideanPlane P]
variable {A B C D : P}
variable {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P)
variable {P : Type*} [EuclideanPlane P] (prg : Parallelogram P)

/-- The lengths of segments point₁ point₂ and point₃ point₄ in a parallelogram are equal. -/
theorem eq_length_of_isPrg : (prg.edge₁₂).length = (prg.edge₃₄).length := by sorry

theorem eq_length_of_isPrg_variant (h : (QDR A B C D).IsPrg) : (SEG A B).length = (SEG C D).length := by sorry

/-- The lengths of segments point₁ point₄ and point₂ point₃ in a parallelogram are equal. -/
theorem eq_length_of_isPrg' : (prg.edge₁₄).length = (prg.edge₂₃).length := by sorry

theorem eq_length_of_isPrg'_variant (h : (QDR A B C D).IsPrg) : (SEG A D).length = (SEG B C).length := by sorry

/-- The midpoints of segments point₁ point₃ and point₂ point₄ in a parallelogram are exactly the same. -/
theorem eq_midpt_of_diag_of_isPrg : (prg.diag₁₃).midpoint = (prg.diag₂₄).midpoint := by sorry

/-- In a parallelogram the sum of the square of the sides is equal to that of the two diags. -/
theorem parallelogram_law : 2 * (prg.edge₁₂).length ^ 2 + 2 * (prg.edge₂₃).length ^ 2 = (prg.diag₁₃).length ^ 2 + (prg.diag₂₄).length ^ 2 := by sorry

/-- In a parallelogram A B C D the sum of the square of the sides is equal to that of the two diags, namely 2 * AB² + 2 * BC² = AC² + BD². -/
theorem parallelogram_law_variant (h : (QDR A B C D).IsPrg) : 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2 := by sorry

end property

section property_nd

variable {P : Type*} [EuclideanPlane P]
variable {A B C D : P}
variable {P : Type*} [EuclideanPlane P] (qdr : Quadrilateral P)
variable {P : Type*} [EuclideanPlane P] (prg_nd : ParallelogramND P)

/-- In a parallelogram_nd, edgeND₁₂ and edge₃₄ are parallel. -/
theorem para_of_isPrgND : prg_nd.edgeND₁₂ ∥ prg_nd.edgeND₃₄ := (prg_nd.parapara_iff_para_para.mp prg_nd.parapara_of_prgnd).left

/-- In a parallelogram_nd, edgeND₁₄ and edge₂₃ are parallel. -/
theorem para_of_isPrgND' : prg_nd.edgeND₄₁ ∥ prg_nd.edgeND₂₃ := (prg_nd.parapara_iff_para_para.mp prg_nd.parapara_of_prgnd).right

/-- The toDirs of edgeND₁₂ and edgeND₃₄ of a parallelogram_nd remain reverse. -/
theorem todir_eq_of_isPrgND : prg_nd.edgeND₁₂.toDir = - prg_nd.edgeND₃₄.toDir := by sorry

/-- The toDirs of edgeND₁₄ and edgeND₂₃ of a parallelogram_nd remain the same. -/
theorem todir_eq_of_isPrgND' : prg_nd.edgeND₄₁.toDir = - prg_nd.edgeND₂₃.toDir := by sorry

/-- In a parallelogram_nd, angle₂ and angle₄ are equal. -/
theorem eq_angle_value_of_isPrgND : prg_nd.angle₂.value = prg_nd.angle₄.value := by sorry

/-- In a parallelogram_nd, angle₁ and angle₃ are equal. -/
theorem eq_angle_value_of_isPrgND' : prg_nd.angle₁.value = prg_nd.angle₃.value := by sorry

/-- In a parallelogram_nd the intersection of the two diags is the same as the midpoint of diag₁₃. -/
theorem eq_midpt_of_diag_inx_of_isPrgND : prg_nd.diag_inx = prg_nd.diag_nd₁₃.midpoint := by sorry

/-- In a parallelogram_nd the intersection of the two diags is the same as the midpoint of diag₂₄. -/
theorem eq_midpt_of_diag_inx_of_isPrgND' : prg_nd.diag_inx = prg_nd.diag_nd₂₄.midpoint := by sorry

end property_nd
