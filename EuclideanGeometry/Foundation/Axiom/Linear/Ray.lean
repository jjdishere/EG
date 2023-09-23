import EuclideanGeometry.Foundation.Axiom.Basic.Plane
import EuclideanGeometry.Foundation.Axiom.Basic.Class

/-!
# Segments and rays

We define the class of generalized directed segments and rays, and their coersions. We also define the property of a point lying on such a structure. Finally, we discuss the nonemptyness/degeneracy of generalized directed segments. 

From now on, by "segment" we mean a generalized directed segment.

## Important definitions

* `Ray` : the class of rays on an EuclideanPlane
* `Seg` : the class of generalized directed segments on an EuclideanPlane (meaning segments with specified source and target, but allowing it to reduce to a singleton.)


## Notation

*  : notation for a point lies on a ray
*  : notation for a point lies on a generalized directed segment
* notation for Seg A B

## Implementation Notes

## Further Works

-/
noncomputable section
namespace EuclidGeom

section definition
/- Rays -/
@[ext]
class Ray (P : Type _) [EuclideanPlane P] where
  source : P
  toDir: Dir

/- Generalized Directed segment -/
@[ext]
class Seg (P : Type _) [EuclideanPlane P] where
  source : P
  target : P

namespace Seg

def is_nd {P : Type _} [EuclideanPlane P] (seg : Seg P) : Prop := seg.target ≠ seg.source

end Seg

def Seg_nd (P : Type _) [EuclideanPlane P] := {seg : Seg P // seg.is_nd}

end definition

variable {P : Type _} [EuclideanPlane P]

section make

scoped notation "SEG" => Seg.mk

def Seg_nd.mk (A B : P) (h : B ≠ A) : Seg_nd P where
  val := SEG A B
  property := h

scoped notation "SEG_nd" => Seg_nd.mk

/- make method of Ray giving 2 distinct point -/
def Ray.mk_pt_pt {P : Type _} [EuclideanPlane P] (A B : P) (h : B ≠ A) : Ray P where
  source := A
  toDir := Vec_nd.normalize ⟨VEC A B, (vsub_ne_zero.mpr h)⟩ 

scoped notation "RAY" => Ray.mk_pt_pt

end make

section coersion

namespace Ray 

variable (ray : Ray P)

def toProj : Proj := (ray.toDir : Proj)

/- Def of point lies on a ray -/
protected def IsOn (a : P) (ray : Ray P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ VEC ray.source a = t • ray.toDir.toVec

protected def IsInt (a : P) (ray : Ray P) : Prop := Ray.IsOn a ray ∧ a ≠ ray.source

protected def carrier (ray : Ray P) : Set P := { p : P | Ray.IsOn p ray }

protected def interior (ray : Ray P) : Set P := { p : P | Ray.IsInt p ray }

instance : Carrier P (Ray P) where
  carrier := fun l => l.carrier

instance : Interior P (Ray P) where
  interior := fun l => l.interior

end Ray

namespace Seg

def toVec (seg : Seg P) : Vec := VEC seg.source seg.target

protected def IsOn (a : P) (seg : Seg P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧ VEC seg.source a  = t • (VEC seg.source seg.target)

protected def IsInt (a : P) (seg : Seg P) : Prop := Seg.IsOn a seg ∧ a ≠ seg.source ∧ a ≠ seg.target 

protected def carrier (seg : Seg P) : Set P := { p : P | Seg.IsOn p seg }

protected def interior (seg : Seg P) : Set P := { p : P | Seg.IsInt p seg }

instance : Carrier P (Seg P) where
  carrier := fun l => l.carrier

instance : Interior P (Seg P) where
  interior := fun l => l.interior

end Seg

namespace Seg_nd

instance : Coe (Seg_nd P) (Seg P) where
  coe := fun x => x.1

variable (seg_nd : Seg_nd P)

def toVec_nd : Vec_nd := ⟨VEC seg_nd.1.source seg_nd.1.target, (ne_iff_vec_ne_zero _ _).mp seg_nd.2⟩ 

def toDir : Dir := Vec_nd.normalize seg_nd.toVec_nd

def toRay : Ray P where
  source := seg_nd.1.source
  toDir := seg_nd.toDir

def toProj : Proj := (seg_nd.toVec_nd.toProj : Proj)

/- We choose not to define IsOn IsInt of Seg_nd directly, since it can always be called by Seg.IsOn p seg_nd.1. And this will save us a lot of lemmas. But I leave the code here temporarily, in case of future changes.-/
/-
protected def IsOn (a : P) (seg_nd : Seg_nd P) : Prop := Seg.IsOn a seg_nd.1

protected def IsInt (a : P) (seg_nd : Seg_nd P) : Prop := Seg.IsInt a seg_nd.1

protected def carrier (seg_nd : Seg_nd P) : Set P := { p : P | Seg_nd.IsOn p seg_nd }

protected def interior (seg_nd : Seg_nd P) : Set P := { p : P | Seg.IsInt p seg_nd }

instance : Carrier P (Seg_nd P) where
  carrier := fun l => l.carrier

instance : Interior P (Seg_nd P) where
  interior := fun l => l.interior
-/

end Seg_nd

end coersion

section coersion_compatibility

variable (seg : Seg P) (seg_nd : Seg_nd P) (ray : Ray P) 

section lies

theorem Ray.source_lies_on : ray.source LiesOn ray := by sorry

theorem Seg.source_lies_on : seg.source LiesOn seg := by sorry

theorem Seg.target_lies_on : seg.target LiesOn seg := by sorry

theorem Seg.source_not_lies_int : ¬ seg.source LiesInt seg := by sorry 

theorem Seg.target_not_lies_int : ¬ seg.target LiesInt seg := by sorry

theorem Seg.lies_on_of_lies_int (p : P) : (p LiesInt seg) → (p LiesOn seg) := by sorry

theorem Ray.lies_on_of_lies_int (p : P) : (p LiesInt ray) → (p LiesOn ray) := by sorry

theorem Seg_nd.lies_on_toRay_of_lies_on (p : P) : (p LiesOn seg_nd.1) → (p LiesOn seg_nd.toRay) := by sorry

theorem Seg_nd.lies_int_toRay_of_lies_int (p : P) : (p LiesInt seg_nd.1) → (p LiesInt seg_nd.toRay) := by sorry

end lies

theorem Seg_nd.toDir_eq_toRay_toDir : seg_nd.toDir = seg_nd.toRay.toDir := by sorry

theorem Seg_nd.toProj_eq_toRay_toProj : seg_nd.toProj = seg_nd.toRay.toProj := by sorry

theorem Ray.is_in_inter_iff_add_pos_Dir : p LiesInt ray ↔ ∃ t : ℝ, 0 < t ∧ VEC ray.source p = t • ray.toDir.toVec := by sorry

end coersion_compatibility

@[simp]
theorem seg_toVec_eq_vec (A B : P) : (SEG A B).toVec = VEC A B := rfl

theorem toVec_eq_zero_of_deg (l : Seg P) : (l.target = l.source) ↔ l.toVec = 0 := by unfold Seg.toVec Vec.mk_pt_pt; simp

section length

variable (l : Seg P)

-- define the length of a generalized directed segment.
def Seg.length : ℝ := norm (l.toVec)

-- length of a generalized directed segment is nonnegative.
theorem length_nonneg : 0 ≤ l.length := by exact @norm_nonneg _ _ _

-- A generalized directed segment is nontrivial if and only if its length is positive.
theorem length_pos_iff_nd : 0 < l.length ↔ (l.is_nd) := by
  rw [Seg.length]
  rw [Seg.is_nd]
  rw [norm_pos_iff]
  apply Iff.not
  rw [toVec_eq_zero_of_deg]

theorem length_ne_zero_iff_nd : 0 ≠ l.length ↔ (l.is_nd) := by 
  rw [Seg.length]
  rw [Seg.is_nd]
  apply Iff.not
  rw [toVec_eq_zero_of_deg]
  rw [eq_comm]
  exact norm_eq_zero

theorem length_pos (l : Seg_nd P): 0 < l.1.length := by
  rw [length_pos_iff_nd]
  simp only [l.2, not_false_eq_true]

theorem length_sq_eq_inner_toVec_toVec : l.length ^ 2 = inner l.toVec l.toVec := by
  have w : l.length = Real.sqrt (inner l.toVec l.toVec) := by 
    unfold Seg.length inner InnerProductSpace.toInner InnerProductSpace.complexToReal InnerProductSpace.isROrCToReal
    simp only [Complex.norm_eq_abs, Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul,
      sub_neg_eq_add]
    rfl
  rw [w]
  have n : (0 : ℝ)  ≤ inner l.toVec l.toVec := by 
    exact InnerProductSpace.Core.nonneg_re (@InnerProductSpace.toCore _ _ _ _ InnerProductSpace.complexToReal) l.toVec
  rw [Real.sq_sqrt n]

-- A generalized directed segment is trivial if and only if length is zero.
theorem triv_iff_length_eq_zero : (l.target = l.source) ↔ l.length = 0 := by
  unfold Seg.length
  exact Iff.trans (toVec_eq_zero_of_deg _)  (@norm_eq_zero _ _).symm

-- If P lies on a generalized directed segment AB, then length(AB) = length(AP) + length(PB)
theorem length_eq_length_add_length (l : Seg P) (A : P) (lieson : A LiesOn l) : l.length = (SEG l.source A).length + (SEG A l.target).length := by
  unfold Seg.length
  rw [seg_toVec_eq_vec]
  rw [seg_toVec_eq_vec]
  rw [seg_toVec_eq_vec]
  rcases lieson with ⟨t, ⟨a, b, c⟩ ⟩
  have h: VEC l.source l.target = VEC l.source A + VEC A l.target := by simp
  rw [c]
  have s: VEC A l.target = ( 1 - t ) • VEC l.source l.target := by 
    rw [c] at h
    rw [sub_smul]
    rw [one_smul]
    exact eq_sub_of_add_eq' (id (Eq.symm h))
  rw [s]
  rw [norm_smul]
  rw [norm_smul]
  rw [← add_mul]
  rw [Real.norm_of_nonneg]
  rw [Real.norm_of_nonneg]
  linarith
  simp
  exact b
  exact a

end length

section midpoint

variable (seg : Seg P) (seg_nd : Seg_nd P)

def Seg.midpoint : P := (1 / 2 : ℝ) • (seg.toVec) +ᵥ seg.source

theorem Seg.midpt_lies_on : seg.midpoint LiesOn seg := sorry

theorem Seg_nd.midpt_lies_int : seg_nd.1.midpoint LiesInt seg_nd.1 := sorry

-- A point is the mid opint of a segment if and only it defines the same vector to the source and the target of the segment
theorem midpt_iff_same_vector_to_source_and_target (A : P) (l : Seg P) : A = l.midpoint ↔ (SEG l.source A).toVec = (SEG A l.target).toVec := by sorry

theorem dist_target_eq_dist_source_of_midpt : (SEG seg.source seg.midpoint).length = (SEG seg.midpoint seg.target).length := sorry

theorem eq_midpoint_iff_in_seg_and_dist_target_eq_dist_source {A : P} : A = seg.midpoint ↔ (A LiesOn seg) ∧ (SEG seg.source A).length = (SEG A seg.target).length := sorry

end midpoint

section existence

-- Archimedean property I : given a directed segment AB (with A ≠ B), then there exists a point P such that B lies on the directed segment AP and P ≠ B.

theorem Seg_nd.exist_pt_beyond_pt {P : Type _} [EuclideanPlane P] (l : Seg_nd P) : (∃ q : P, l.1.target LiesInt (SEG l.1.source q)) := by 
  let h := l.1.toVec +ᵥ l.1.target
  let half : ℝ := 1/2
  have c: 0 ≤ half ∧ half ≤ 1 ∧ VEC l.1.source l.1.target = half • VEC l.1.source h := by
    norm_num
    rw [seg_toVec_eq_vec]
    repeat rw [Vec.mk_pt_pt]
    rw [vadd_vsub_assoc]
    let t := l.1.target -ᵥ l.1.source
    have x: t = 1/2 * (t + t) := by
      calc t = 1/2 * (2 * t) := by simp
      _ = 1/2 * (t + t) := by rw [two_mul]
    exact x
  have a: l.1.target LiesOn SEG l.1.source h := ⟨half, c⟩
  have b: l.1.target ≠ l.1.source ∧ l.1.target ≠ h := by
    constructor
    exact l.2
    have x: l.1.toVec ≠ 0 := by 
      rw [seg_toVec_eq_vec]
      rw [Vec.mk_pt_pt]
      rw [vsub_ne_zero]
      exact l.2
    have y: l.1.target ≠ l.1.toVec +ᵥ l.1.target := by
      rw [ne_comm]
      by_contra t
      simp at t
      exact x t
    exact y
  have k: l.1.target LiesInt SEG l.1.source h := ⟨a, b⟩
  use h
 
-- Archimedean property II: On an nontrivial directed segment, one can always find a point in its interior.  `This will be moved to later disccusion about midpoint of a segment, as the midpoint is a point in the interior of a nontrivial segment`

theorem nd_of_exist_int_pt (l : Seg P) (p : P) (h : p LiesInt l) : l.is_nd := by
  rw [Seg.is_nd]
  rcases h with ⟨⟨c, d⟩, b⟩
  rcases b with ⟨p_ne_s, _⟩
  rcases d with ⟨_, _, e⟩
  have t: VEC Seg.source p ≠ 0 := by exact Iff.mp (ne_iff_vec_ne_zero Seg.source p) p_ne_s
  have u: c • VEC Seg.source Seg.target ≠ 0 := by 
    rw [← e]
    exact t
  have v: VEC Seg.source Seg.target ≠ 0 := by
    exact right_ne_zero_of_smul u
  exact Iff.mp vsub_ne_zero v

-- If a generalized directed segment contains an interior point, then it is nontrivial
theorem nd_iff_exist_int_pt (l : Seg P) : (∃ (p : P), p LiesInt l) ↔ l.is_nd := by
  constructor

  intro h
  rcases h with ⟨a, b⟩
  exact nd_of_exist_int_pt l a b

  intro h
  use l.midpoint
  exact Seg_nd.midpt_lies_int ⟨l, h⟩

theorem Seg_nd.exist_int_pt (l : Seg_nd P) : ∃ (p : P), p LiesInt l.1 := by
  use l.1.midpoint
  exact midpt_lies_int l

theorem length_pos_iff_exist_int_pt (l : Seg P) : 0 < l.length ↔ (∃ (p : P), p LiesInt l) := by 
  exact Iff.trans (length_pos_iff_nd _) (nd_iff_exist_int_pt _).symm
end existence

end EuclidGeom