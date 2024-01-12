import EuclideanGeometry.Foundation.Axiom.Position.Orientation
import EuclideanGeometry.Foundation.Axiom.Linear.Colinear

universe u

noncomputable section
namespace EuclidGeom

open Classical

/- Class of generalized triangles -/
@[ext]
structure Triangle (P : Type u) [EuclideanPlane P] where
  point₁ : P
  point₂ : P
  point₃ : P

namespace Triangle

variable {P : Type u} [EuclideanPlane P]
--implies  1 left of 23, 2 left of 31

-- not is_cclock implies 1 right of 23, ..., ...
@[pp_dot]
def edge₁ (tr : Triangle P) : Seg P := Seg.mk tr.2 tr.3

@[pp_dot]
def edge₂ (tr : Triangle P) : Seg P := Seg.mk tr.3 tr.1

@[pp_dot]
def edge₃ (tr : Triangle P) : Seg P := Seg.mk tr.1 tr.2

@[pp_dot]
def oarea (tr : Triangle P) : ℝ := EuclidGeom.oarea tr.1 tr.2 tr.3

@[pp_dot]
def area (tr : Triangle P) : ℝ := |tr.oarea|

@[pp_dot]
def IsND (tr : Triangle P) : Prop := ¬ colinear tr.1 tr.2 tr.3

end Triangle

def TriangleND (P : Type u) [EuclideanPlane P] := { tr : Triangle P // tr.IsND }

namespace TriangleND

variable {P : Type u} [EuclideanPlane P] (tr_nd : TriangleND P)

@[pp_dot]
abbrev point₁ : P := tr_nd.1.1

@[pp_dot]
abbrev point₂ : P := tr_nd.1.2

@[pp_dot]
abbrev point₃ : P := tr_nd.1.3

instance nontriv₁ : PtNe tr_nd.point₃ tr_nd.point₂ := ⟨(ne_of_not_colinear tr_nd.2).1⟩

instance nontriv₂ : PtNe tr_nd.point₁ tr_nd.point₃ := ⟨(ne_of_not_colinear tr_nd.2).2.1⟩

instance nontriv₃ : PtNe tr_nd.point₂ tr_nd.point₁ := ⟨(ne_of_not_colinear tr_nd.2).2.2⟩

@[pp_dot]
abbrev edge₁ : Seg P := tr_nd.1.edge₁

@[pp_dot]
abbrev edge₂ : Seg P := tr_nd.1.edge₂

@[pp_dot]
abbrev edge₃ : Seg P := tr_nd.1.edge₃

@[pp_dot]
def edge_nd₁ : SegND P := ⟨tr_nd.1.edge₁, tr_nd.nontriv₁.out⟩

@[pp_dot]
def edge_nd₂ : SegND P := ⟨tr_nd.1.edge₂, tr_nd.nontriv₂.out⟩

@[pp_dot]
def edge_nd₃ : SegND P := ⟨tr_nd.1.edge₃, tr_nd.nontriv₃.out⟩

@[pp_dot]
abbrev oarea : ℝ := tr_nd.1.oarea

@[pp_dot]
abbrev area : ℝ := tr_nd.1.area

/- Only nondegenerate triangles can talk about orientation -/
@[pp_dot]
def is_cclock : Prop := 0 < TriangleND.oarea tr_nd

@[pp_dot]
def angle₁ : Angle P := ANG tr_nd.point₂ tr_nd.point₁ tr_nd.point₃

@[pp_dot]
def angle₂ : Angle P := ANG tr_nd.point₃ tr_nd.point₂ tr_nd.point₁

@[pp_dot]
def angle₃ : Angle P := ANG tr_nd.point₁ tr_nd.point₃ tr_nd.point₂

end TriangleND

variable {P : Type u} [EuclideanPlane P]

namespace Triangle

-- When we have DirFig, rewrite this definition.
protected def IsInt (A : P) (tr : Triangle P) : Prop := by
  by_cases h : colinear tr.1 tr.2 tr.3
  -- why not using ¬ tr.IsND?
  · exact False
  · let tr_nd : TriangleND P := ⟨tr, h⟩
    exact (if tr_nd.is_cclock then A LiesOnLeft SegND.toRay ⟨tr.edge₁, tr_nd.nontriv₁.out⟩ ∧ A LiesOnLeft SegND.toRay ⟨tr.edge₂, tr_nd.nontriv₂.out⟩ ∧ A LiesOnLeft SegND.toRay ⟨tr.edge₃, tr_nd.nontriv₃.out⟩ else A LiesOnRight SegND.toRay ⟨tr.edge₁, tr_nd.nontriv₁.out⟩ ∧ A LiesOnRight SegND.toRay ⟨tr.edge₂, tr_nd.nontriv₂.out⟩ ∧ A LiesOnRight SegND.toRay ⟨tr.edge₃, tr_nd.nontriv₃.out⟩)

protected def IsOn (A : P) (tr : Triangle P) : Prop := Triangle.IsInt A tr ∨ A LiesOn tr.edge₁ ∨ A LiesOn tr.edge₂ ∨ A LiesOn tr.edge₃

protected def carrier (tr : Triangle P) : Set P := { p : P | Triangle.IsOn p tr }

protected def interior (tr : Triangle P) : Set P := { p : P | Triangle.IsInt p tr }


instance : Interior (Triangle P) P where
  interior := Triangle.interior

/-
instance : IntFig Triangle where
  carrier := Triangle.carrier
  interior_subset_carrier := fun _ [EuclideanPlane _] _ _ => Or.inl
-/

end Triangle

namespace TriangleND

protected def IsInt (A : P) (tr_nd : TriangleND P) : Prop := by
  exact (if tr_nd.is_cclock then A LiesOnLeft SegND.toRay ⟨tr_nd.edge₁, tr_nd.nontriv₁.out⟩ ∧ A LiesOnLeft SegND.toRay ⟨tr_nd.edge₂, tr_nd.nontriv₂.out⟩ ∧ A LiesOnLeft SegND.toRay ⟨tr_nd.edge₃, tr_nd.nontriv₃.out⟩ else A LiesOnRight SegND.toRay ⟨tr_nd.edge₁, tr_nd.nontriv₁.out⟩ ∧ A LiesOnRight SegND.toRay ⟨tr_nd.edge₂, tr_nd.nontriv₂.out⟩ ∧ A LiesOnRight SegND.toRay ⟨tr_nd.edge₃, tr_nd.nontriv₃.out⟩)

protected def IsOn (A : P) (tr_nd : TriangleND P) : Prop := TriangleND.IsInt A tr_nd ∨ A LiesOn tr_nd.edge₁ ∨ A LiesOn tr_nd.edge₂ ∨ A LiesOn tr_nd.edge₃

protected def carrier (tr_nd : Triangle P) : Set P := { p : P | Triangle.IsOn p tr_nd }

protected def interior (tr_nd : Triangle P) : Set P := { p : P | Triangle.IsInt p tr_nd }

/-
instance : Interior Triangle where
  interior := Triangle.interior
-/

/-
instance : IntFig Triangle where
  carrier := Triangle.carrier
  interior_subset_carrier := fun _ [EuclideanPlane _] _ _ => Or.inl
-/

end TriangleND

def TriangleND.mk (A B C : P) (h : ¬ colinear A B C) : TriangleND P := Subtype.mk (Triangle.mk A B C) h

scoped notation "TRI" => Triangle.mk
scoped notation "▵" => Triangle.mk
scoped notation "TRI_nd" A:max B:max C:max h:max => EuclidGeom.TriangleND.mk A B C h


namespace Triangle

variable (tr : Triangle P) (tr_nd : TriangleND P)

-- The following theorems are only related to tr_nd, so I move them to namespace TriangleND

/-
theorem angle_pos_of_cclock (cclock : tr_nd.is_cclock) : 0 < tr_nd.angle₁.value ∧ 0 < tr_nd.angle₂.value ∧ 0 < tr_nd.angle₃.value := by sorry

theorem angle_neg_of_clock (clock : ¬ tr_nd.is_cclock) : tr_nd.angle₁.value < 0 ∧ tr_nd.angle₂.value  < 0 ∧ tr_nd.angle₃.value < 0  := by sorry

theorem cclock_of_pos_angle (h : 0 < tr_nd.angle₁.value ∨ 0 < tr_nd.angle₂.value ∨ 0 < tr_nd.angle₃.value) : tr_nd.is_cclock := sorry

theorem clock_of_neg_angle (h : tr_nd.angle₁.value < 0 ∨ tr_nd.angle₂.value < 0 ∨ tr_nd.angle₃.value < 0) :¬ tr_nd.is_cclock := sorry

theorem pos_pos_or_neg_neg_of_iff_cclock {tr_nd₁ tr_nd₂ : TriangleND P} : (tr_nd₁.is_cclock ↔ tr_nd₂.is_cclock) ↔ (0 < tr_nd₁.angle₁.value ∧ 0 < tr_nd₂.angle₁.value) ∨ (tr_nd₁.angle₁.value < 0 ∧ tr_nd₂.angle₁.value < 0) := by
  constructor
  · intro k
    by_cases tr_nd₁.is_cclock
    · have h0 : tr_nd₂.is_cclock := by rw [←k] ; apply h
      left
      exact ⟨(angle_pos_of_cclock tr_nd₁ h).1, (angle_pos_of_cclock tr_nd₂ h0).1⟩
    · have h0: ¬ tr_nd₂.is_cclock := by rw [←k] ; apply h
      right
      exact ⟨(angle_neg_of_clock tr_nd₁ h).1, (angle_neg_of_clock tr_nd₂ h0).1⟩
  intro k
  rcases k with x | y
  · have k1 : tr_nd₁.is_cclock := by
      apply cclock_of_pos_angle tr_nd₁
      apply Or.inl x.1
    have k2 : tr_nd₂.is_cclock := by
      apply cclock_of_pos_angle tr_nd₂
      apply Or.inl x.2
    simp only [k1,k2]
  · have k1 : ¬ tr_nd₁.is_cclock := by
      apply clock_of_neg_angle tr_nd₁
      apply Or.inl y.1
    have k2 : ¬ tr_nd₂.is_cclock := by
      apply clock_of_neg_angle tr_nd₂
      apply Or.inl y.2
    simp only [k1,k2]

theorem angle_sum_eq_pi_of_cclock (cclock : tr_nd.is_cclock): tr_nd.angle₁.value + tr_nd.angle₂.value + tr_nd.angle₃.value = π := sorry

theorem angle_sum_eq_neg_pi_of_clock (clock : ¬ tr_nd.is_cclock): tr_nd.angle₁.value + tr_nd.angle₂.value + tr_nd.angle₃.value = - π := sorry
-/
theorem triangle_ineq : tr.edge₃.length ≤ tr.edge₁.length + tr.edge₂.length := by
  unfold Seg.length
  rw [dist_comm]
  exact dist_triangle _ _ _

theorem trivial_of_edge_sum_eq_edge : tr.edge₁.length + tr.edge₂.length = tr.edge₃.length → ¬ tr.IsND  := by
  let A := tr.point₁
  let B := tr.point₂
  let C := tr.point₃
  have l₃ : tr.edge₃.length = norm (VEC A B) := Seg.length_eq_norm_toVec
  rw [l₃, ← neg_vec B _, norm_neg, ← vec_add_vec B C A]
  intro eq
  unfold IsND
  rw [not_not]
  by_cases h₁ : VEC B C = 0
  · simp only [(eq_iff_vec_eq_zero B C).2 h₁]
    apply flip_colinear_fst_trd
    exact triv_colinear _ _
  · by_cases h₂ : VEC C A = 0
    · simp only [(eq_iff_vec_eq_zero C A).2 h₂]
      apply flip_colinear_snd_trd
      exact triv_colinear _ _
    · have g : SameRay ℝ (VEC B C) (VEC C A)
      · rw [sameRay_iff_norm_add, ← eq]
        congr <;>
        exact Seg.length_eq_norm_toVec
      rcases SameRay.exists_pos g h₁ h₂ with ⟨_, ⟨_, ⟨_, ⟨_, g⟩⟩⟩⟩
      rw [← neg_vec C B, ← neg_one_smul ℝ, ← mul_smul, mul_neg_one, ← eq_inv_smul_iff₀ (by linarith), ← mul_smul] at g
      exact perm_colinear_snd_trd_fst (colinear_of_vec_eq_smul_vec g)

theorem triangle_ineq' (nontriv : tr.IsND) : tr.edge₁.length + tr.edge₂.length > tr.edge₃.length := by
  have ne : tr.edge₁.length + tr.edge₂.length ≠ tr.edge₃.length := by
    by_contra h
    let g := trivial_of_edge_sum_eq_edge tr h
    tauto
  by_contra h
  let g := eq_of_le_of_not_lt (triangle_ineq tr) h
  tauto

/- The following two theorems are totally wrong:

theorem nontrivial_of_edge_sum_ne_edge : tr.edge₁.length + tr.edge₂.length ≠ tr.edge₃.length → tr.IsND  := by

theorem nontrivial_of_edge_sum_gt_edge : tr.edge₁.length + tr.edge₂.length > tr.edge₃.length → tr.IsND  := sorry

So funny. Can you get it? -/

theorem edge_sum_eq_edge_iff_colinear : colinear tr.1 tr.2 tr.3 ↔ (tr.edge₁.length + tr.edge₂.length = tr.edge₃.length) ∨ (tr.edge₂.length + tr.edge₃.length = tr.edge₁.length) ∨ (tr.edge₃.length + tr.edge₁.length = tr.edge₂.length) := sorry
/- area ≥ 0, nontrivial → >0, =0 → trivial -/

end Triangle

namespace TriangleND

variable (tr_nd : TriangleND P)
--`Rewrite this Part!!!!`
theorem angle_pos_of_cclock (cclock : tr_nd.is_cclock) : tr_nd.angle₁.value.IsPos ∧ tr_nd.angle₂.value.IsPos ∧ tr_nd.angle₃.value.IsPos := by sorry

theorem angle_neg_of_clock (clock : ¬ tr_nd.is_cclock) : tr_nd.angle₁.value.IsNeg ∧ tr_nd.angle₂.value.IsNeg ∧ tr_nd.angle₃.value.IsNeg  := by sorry

theorem cclock_of_pos_angle (h : tr_nd.angle₁.value.IsPos ∨ tr_nd.angle₂.value.IsPos ∨ tr_nd.angle₃.value.IsPos) : tr_nd.is_cclock := sorry

theorem clock_of_neg_angle (h : tr_nd.angle₁.value.IsNeg ∨ tr_nd.angle₂.value.IsNeg ∨ tr_nd.angle₃.value.IsNeg) :¬ tr_nd.is_cclock := sorry

theorem pos_pos_or_neg_neg_of_iff_cclock {tr_nd₁ tr_nd₂ : TriangleND P} : (tr_nd₁.is_cclock ↔ tr_nd₂.is_cclock) ↔ (tr_nd₁.angle₁.value.IsPos ∧ tr_nd₂.angle₁.value.IsPos) ∨ (tr_nd₁.angle₁.value.IsNeg ∧ tr_nd₂.angle₁.value.IsNeg) := by
  constructor
  · intro k
    by_cases h : tr_nd₁.is_cclock
    · have h0 : tr_nd₂.is_cclock := by rw [←k] ; apply h
      left
      exact ⟨(angle_pos_of_cclock tr_nd₁ h).1, (angle_pos_of_cclock tr_nd₂ h0).1⟩
    · have h0: ¬ tr_nd₂.is_cclock := by rw [←k] ; apply h
      right
      exact ⟨(angle_neg_of_clock tr_nd₁ h).1, (angle_neg_of_clock tr_nd₂ h0).1⟩
  intro k
  rcases k with x | y
  · have k1 : tr_nd₁.is_cclock := by
      apply cclock_of_pos_angle tr_nd₁
      apply Or.inl x.1
    have k2 : tr_nd₂.is_cclock := by
      apply cclock_of_pos_angle tr_nd₂
      apply Or.inl x.2
    simp only [k1,k2]
  · have k1 : ¬ tr_nd₁.is_cclock := by
      apply clock_of_neg_angle tr_nd₁
      apply Or.inl y.1
    have k2 : ¬ tr_nd₂.is_cclock := by
      apply clock_of_neg_angle tr_nd₂
      apply Or.inl y.2
    simp only [k1,k2]

theorem angle_sum_eq_pi_of_cclock (cclock : tr_nd.is_cclock): tr_nd.angle₁.value + tr_nd.angle₂.value + tr_nd.angle₃.value = π := sorry

theorem angle_sum_eq_neg_pi_of_clock (clock : ¬ tr_nd.is_cclock): tr_nd.angle₁.value + tr_nd.angle₂.value + tr_nd.angle₃.value = - π := sorry

theorem triangle_ineq' : tr_nd.edge₁.length + tr_nd.edge₂.length > tr_nd.edge₃.length := sorry

theorem sum_of_other_angle_same_if_one_angle_same (tr₁ tr₂ : TriangleND P) (a : tr₁.angle₁.value = tr₂.angle₁.value) : tr₁.angle₂.value + tr₁.angle₃.value = tr₂.angle₂.value + tr₂.angle₃.value := by sorry

theorem sum_of_other_angle_same_neg_if_one_angle_same_neg (tr₁ tr₂ : TriangleND P) (a : tr₁.angle₁.value =  - tr₂.angle₁.value) : tr₁.angle₂.value + tr₁.angle₃.value = - (tr₂.angle₂.value + tr₂.angle₃.value ) := by sorry

end TriangleND

end EuclidGeom
