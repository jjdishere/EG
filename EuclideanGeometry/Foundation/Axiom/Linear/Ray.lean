import EuclideanGeometry.Foundation.Axiom.Basic.Plane
import EuclideanGeometry.Foundation.Axiom.Basic.Class

/-!
# Segments and rays

In this file, we define the class of segments, rays and their coercions, as well as basic properties.  A more precise plan is the following:
We define the corresponding classes: rays, segments, and nondegenerate segments.

We define the coercions among these concepts as well as coercions to directions, or projective directions.

We give different ways to make a segment or a ray.

We discuss compatibility of the coercion functions.

We introduce the concept of reversing a segment, that is to switch the start and end point of a segment.

We define the length function of a segment.

We define the concept of extending a segment into a ray.

We define the function that gives the midpoint of a segment.

We discuss the Archimedean property of a segment.

## Important definitions

* `Ray` : A \emph{ray} consists of a pair of a point $P$ and a direction; it is the ray that starts at the point and extends in the given direction.
* `Seg` : A \emph{Segment} consists of a pair of points: the source and the target; it is the segment from the source to the target. (We allow the source and the target to be the same.)


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

/-- A \emph{ray} consists of a pair of a point $P$ and a direction; it is the ray that starts at the point and extends in the given direction. -/
@[ext]
class Ray (P : Type _) [EuclideanPlane P] where
  source : P
  toDir : Dir

/-- A \emph{Segment} consists of a pair of points: the source and the target; it is the segment from the source to the target. (We allow the source and the target to be the same.) -/
@[ext]
class Seg (P : Type _) [EuclideanPlane P] where
  source : P
  target : P

namespace Seg

/-- Given a segment $AB$, this function returns whether the segment $AB$ is nondegenerate, i.e. whether $A \neq B$. -/
def is_nd {P : Type _} [EuclideanPlane P] (seg : Seg P) : Prop := seg.target ≠ seg.source

end Seg

/-- A \emph{nondegenerate segment} is a segment $AB$ that is nondegenerate, i.e. $A \neq B$. -/
def Seg_nd (P : Type _) [EuclideanPlane P] := {seg : Seg P // seg.is_nd}

end definition

variable {P : Type _} [EuclideanPlane P]

section make

scoped notation "SEG" => Seg.mk

/-- Given two distinct points $A$ and $B$, this function returns a nondegenerate segment with source $A$ and target $B$. -/
def Seg_nd.mk (A B : P) (h : B ≠ A) : Seg_nd P where
  val := SEG A B
  property := h

scoped notation "SEG_nd" => Seg_nd.mk

/-- Given two distinct points $A$ and $B$, this function returns the ray starting from $A$ in the direction of $B$. By definition, it is to first construct the nondegenerate segment from $A$ to $B$, and then convert the nondegenerate segment $AB$ to the associated ray using \verb|toRay| function. -/
def Ray.mk_pt_pt {P : Type _} [EuclideanPlane P] (A B : P) (h : B ≠ A) : Ray P where
  source := A
  toDir := Vec_nd.toDir ⟨VEC A B, (vsub_ne_zero.mpr h)⟩

scoped notation "RAY" => Ray.mk_pt_pt

end make

section coersion

namespace Ray

variable (ray : Ray P)

/--  Given a nondegenerate segment $AB$, this function returns the projective direction  of $AB$, defined as the projective direction of the nondegenerate vector $\overrightarrow{AB}$.  -/
def toProj : Proj := (ray.toDir : Proj)

/--  Given a point $A$ and a ray $ray$, this function returns whether $A$ lies on $ray$; here saying that $A$ lies on $ray$ means that the vector from the start point of the ray to $A$ is some nonnegative multiple of the direction vector of the ray. -/
protected def IsOn (a : P) (ray : Ray P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ VEC ray.source a = t • ray.toDir.toVec

/-- Given a point $A$ and a ray, this function returns whether the point lies in the interior of the ray; here saying that a point lies in the interior of a ray means that it lies on the ray and is not equal to the source of the ray. -/
protected def IsInt (a : P) (ray : Ray P) : Prop := Ray.IsOn a ray ∧ a ≠ ray.source

/-- Given a ray, its carrier is the set of points that lie on the ray. -/
protected def carrier (ray : Ray P) : Set P := { p : P | Ray.IsOn p ray }

/-- Given a ray, its interior is the set of points that lie in the interior of the ray. -/
protected def interior (ray : Ray P) : Set P := { p : P | Ray.IsInt p ray }

instance : Carrier P (Ray P) where
  carrier := fun l => l.carrier

instance : Interior P (Ray P) where
  interior := fun l => l.interior

end Ray

namespace Seg

/-- Given a segment, this function returns the vector associated to the segment, that is, the vector from the source of the segment to the target of the segment. -/
def toVec (seg : Seg P) : Vec := VEC seg.source seg.target

/-- Given a point $A$ and a segment $seg$, this function returns whether $A$ lies on $seg$; here saying that $A$ lies on $seg$ means that the vector from the source of $seg$ to $A$ is a real multiple $t$ of the vector of $seg$ with $0 \leq t \leq 1$. -/
protected def IsOn (a : P) (seg : Seg P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧ VEC seg.source a  = t • (VEC seg.source seg.target)

/-- Given a point $A$ and a segment $seg$, this function returns whether $A$ lies in the interior of $seg$; here saying that $A$ lies in the interior of $seg$ means $A$ lies on $seg$ and is different from the source and the target of $seg$. -/
protected def IsInt (a : P) (seg : Seg P) : Prop := Seg.IsOn a seg ∧ a ≠ seg.source ∧ a ≠ seg.target

/-- Given a segment, this function returns the set of points that lie on the segment. -/
protected def carrier (seg : Seg P) : Set P := { p : P | Seg.IsOn p seg }

/-- Given a segment, this function returns the set of points that lie in the interior of the segment. -/
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

/-- Given a nondegenerate segment $AB$, this function returns the nondegenerate vector $\overrightarrow{AB}$. -/
def toVec_nd : Vec_nd := ⟨VEC seg_nd.1.source seg_nd.1.target, (ne_iff_vec_ne_zero _ _).mp seg_nd.2⟩

/-- Given a nondegenerate segment $AB$, this function returns the direction associated to the segment, defined by normalizing the nondegenerate vector $\overrightarrow{AB}$. -/
def toDir : Dir := Vec_nd.toDir seg_nd.toVec_nd

/-- Given a nondegenerate segment $AB$, this function returns the ray $AB$, whose source is $A$ in the direction of $B$. -/
def toRay : Ray P where
  source := seg_nd.1.source
  toDir := seg_nd.toDir

/-- Given a nondegenerate segment $AB$, this function returns the projective direction  of $AB$, defined as the projective direction of the nondegenerate vector $\overrightarrow{AB}$.  -/
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

variable {seg : Seg P} {seg_nd : Seg_nd P} {ray : Ray P}

section lieson

/-- Given a ray, the source of the ray lies on the ray. -/
theorem Ray.source_lies_on : ray.source LiesOn ray := ⟨0, by rfl, by rw [vec_same_eq_zero, zero_smul]⟩

/-- Given a segment, the source of the segment lies on the segment. -/
theorem Seg.source_lies_on : seg.source LiesOn seg :=
  ⟨0, by rfl, zero_le_one, by rw [vec_same_eq_zero, zero_smul]⟩

/--  Given a segment $AB$, the target $B$ lies on the segment $AB$. -/
theorem Seg.target_lies_on : seg.target LiesOn seg := ⟨1, zero_le_one, by rfl, by rw [one_smul]⟩

/-- Given a segment $AB$, the source $A$ does not belong to the interior of $AB$. -/
theorem Seg.source_not_lies_int : ¬ seg.source LiesInt seg := fun h ↦ h.2.1 rfl

/-- Given a segment $AB$, the target $B$ does not belong to the interior of $AB$. -/
theorem Seg.target_not_lies_int : ¬ seg.target LiesInt seg := fun h ↦ h.2.2 rfl

/-- For a segment $AB$, every point of the interior of $AB$ lies on the segment $AB$. -/
theorem Seg.lies_on_of_lies_int {p : P} (h : p LiesInt seg) : p LiesOn seg := h.1

/-- For a segment $AB$, a point P lies in the interior of $AB$ if and only if there exist a real number between 0 and 1 satisfying the vector $\overrightarrow{AP}$ is same as $t\overrightarrow{AB}$-/
theorem Seg.lies_int_iff (p : P) : p LiesInt seg ↔ seg.is_nd ∧ ∃ (t : ℝ) , 0 < t ∧ t < 1 ∧ VEC seg.1 p = t • seg.toVec := by
  constructor
  · intro ⟨⟨t, tnonneg, tle1, ht⟩, ns, nt⟩
    rw [ne_iff_vec_ne_zero] at ns nt
    constructor
    · rw [Seg.is_nd]
      contrapose! ns
      rw [ns, vec_same_eq_zero,smul_zero] at ht
      rw [ht]
    · use t
      constructor
      · contrapose! ns
        have : t = 0 := by linarith
        rw [ht, this, zero_smul]
      · constructor
        · contrapose! nt
          have : t = 1 := by linarith
          rw [← vec_sub_vec seg.source, ht, this, one_smul, sub_self]
        · exact ht
  · intro ⟨nd, t, tpos, tlt1, ht⟩
    constructor
    · exact ⟨t, by linarith, by linarith, ht⟩
    · constructor
      · rw [ne_iff_vec_ne_zero,ht, smul_ne_zero_iff]
        constructor
        · linarith
        · rw [Seg.toVec, ← ne_iff_vec_ne_zero]
          exact nd
      · have : t • VEC seg.source seg.target - VEC seg.source seg.target = (t - 1) • VEC seg.source seg.target := by rw [sub_smul, one_smul]
        rw [ne_iff_vec_ne_zero, ← vec_sub_vec seg.source, ht, toVec, this, smul_ne_zero_iff]
        constructor
        · linarith
        · simp only [Seg.toVec, ← ne_iff_vec_ne_zero]
          exact nd

/-- For a ray, every point of the interior of the ray lies on the ray. -/
theorem Ray.lies_on_of_lies_int {p : P} (h : p LiesInt ray) : p LiesOn ray := h.1

/-- Given a ray, a point $A$ lies in the interior of the ray if and only if the vector from the source of the ray to $A$ is a positive multiple of the direction of ray. -/
theorem Ray.lies_int_iff (p : P) : p LiesInt ray ↔ ∃ (t : ℝ) , 0 < t ∧ VEC ray.source p = t • ray.toDir.toVec := by
  constructor
  intro ⟨⟨t, tnonneg, ht⟩, ns⟩
  · use t
    constructor
    · contrapose! ns
      have : t = 0 := by linarith
      rw [eq_iff_vec_eq_zero, ht, this, zero_smul]
    · exact ht
  · intro ⟨t, tpos, ht⟩
    constructor
    · exact ⟨t, by linarith, ht⟩
    · rw [ne_iff_vec_ne_zero, ht, smul_ne_zero_iff]
      exact ⟨by linarith, Dir.toVec_ne_zero ray.toDir⟩

/-- Given a ray, a point lies in the interior of the ray if and only if it lies on the ray and is different from the source of ray -/
theorem Ray.lies_int_def {p : P} : p LiesInt ray ↔ p LiesOn ray ∧ p ≠ ray.source := Iff.rfl

/-- For a nondegenerate segment $AB$, every point of the segment $AB$ lies on the ray associated to $AB$.  -/
theorem Seg_nd.lies_on_toRay_of_lies_on {p : P} (h : p LiesOn seg_nd.1) : p LiesOn seg_nd.toRay := by
  rcases h with ⟨t, ht0, _, h⟩
  refine' ⟨t * Vec.norm (VEC seg_nd.1.1 seg_nd.1.2),
    mul_nonneg ht0 (Vec.norm_nonnegative (VEC seg_nd.1.1 seg_nd.1.2)), _⟩
  simp only [toRay, h, Complex.real_smul, Complex.ofReal_mul, mul_assoc]
  exact congrArg (HMul.hMul _) seg_nd.toVec_nd.self_eq_norm_smul_todir

/-- For a nondegenerate segment $segnd$, every point of the interior of the $segnd$ lies in the interior of the ray associated to the $segnd$. -/
theorem Seg_nd.lies_int_toRay_of_lies_int {p : P} (h : p LiesInt seg_nd.1) : p LiesInt seg_nd.toRay :=
  ⟨Seg_nd.lies_on_toRay_of_lies_on h.1, h.2.1⟩

/-- Given two distinct points $A$ and $B$, $B$ lies on the ray $AB$. -/
theorem Ray.snd_pt_lies_on_mk_pt_pt {A B : P} (h : B ≠ A) : B LiesOn (RAY A B h) := by
  show B LiesOn (SEG_nd A B h).toRay
  exact Seg_nd.lies_on_toRay_of_lies_on Seg.target_lies_on

end lieson

/-- Given a nondegenerate segment, the direction associated to the nondegenerate segment is the same as the direction associated to the ray associated to the nondegenerate segment. -/
theorem Seg_nd.toDir_eq_toRay_toDir : seg_nd.toDir = seg_nd.toRay.toDir := rfl

/-- Given a nondegenerate segment, the projective direction associated to the nondegenerate segment is the same as the projective direction associated to the ray associated to the nondegenerate segment. -/
theorem Seg_nd.toRay_toProj_eq_toProj : seg_nd.toRay.toProj = seg_nd.toProj := rfl

/-- Given two distinct points $A$ and $B$, the direction of ray $AB$ is same as the negative direction of $BA$ -/
theorem Ray.todir_eq_neg_todir_of_mk_pt_pt {A B : P} (h : B ≠ A) : (RAY A B h).toDir = - (RAY B A h.symm).toDir := by
  simp only [Ray.mk_pt_pt, ne_eq]
  exact (neg_to_dir_eq_to_dir_smul_neg ⟨VEC B A, (ne_iff_vec_ne_zero _ _).mp h.symm⟩ ⟨VEC A B, (ne_iff_vec_ne_zero _ _).mp h⟩ (by rw [neg_smul, one_smul, neg_vec]) (by norm_num)).symm

/-- Given two distinct points $A$ and $B$, the projective direction of ray $AB$ is same as that of $BA$ -/
theorem Ray.toProj_eq_toProj_of_mk_pt_pt {A B : P} (h : B ≠ A) : (RAY A B h).toProj = (RAY B A h.symm).toProj := (Dir.eq_toProj_iff _ _).mpr (Or.inr (todir_eq_neg_todir_of_mk_pt_pt h))

/-- Given two distinct points $A$ and $B$, the ray associated to the segment $AB$ is same as ray $AB$-/
theorem pt_pt_seg_toRay_eq_pt_pt_ray {A B : P} (h : B ≠ A) : (Seg_nd.mk A B h).toRay = Ray.mk_pt_pt A B h := rfl

/-- Given ray and a point A, A lies int the ray, then the ray from ray.source to A is just the ray -/
theorem Ray.source_int_toRay_eq_ray {ray : Ray P} {A : P} {ha : A LiesInt ray} : (SEG_nd ray.source A (ha.2)).toRay = ray := sorry

end coersion_compatibility

/-- Given two points $A$ and $B$, the vector associated to the segment $AB$ is same as vector $\overrightarrow{AB}$ -/
@[simp]
theorem seg_toVec_eq_vec (A B : P) : (SEG A B).toVec = VEC A B := rfl

/-- Given a segment $AB$, $A$ is same as $B$ if and only if vector $\overrightarrow{AB}$ is zero  -/
theorem toVec_eq_zero_of_deg {l : Seg P} : (l.target = l.source) ↔ l.toVec = 0 := by
  rw [Seg.toVec, Vec.mk_pt_pt, vsub_eq_zero_iff_eq]

/-- Given a segment $AB$, $AB$ is non-degenerated if and only if vector  $\overrightarrow{AB}$ is not zero -/
theorem Seg.is_nd_iff_toVec_ne_zero {l : Seg P} : l.is_nd ↔ l.toVec ≠ 0 := toVec_eq_zero_of_deg.not

section length

variable {l : Seg P}

/-- This function gives the length of a given segment. -/
def Seg.length (l : Seg P) : ℝ := norm (l.toVec)

/-- Every segment has nonnegative length. -/
theorem length_nonneg : 0 ≤ l.length := norm_nonneg _

/-- A segment has positive length if and only if it is nondegenerate. -/
theorem length_pos_iff_nd : 0 < l.length ↔ l.is_nd :=
  norm_pos_iff.trans toVec_eq_zero_of_deg.symm.not

/-- The length of a given segment is nonzero if and only if the segment is nondegenerate. -/
theorem length_ne_zero_iff_nd : 0 ≠ l.length ↔ l.is_nd :=
  (ne_iff_lt_iff_le.mpr (norm_nonneg _)).trans length_pos_iff_nd

/--  A nondegenerate segment has strictly positive length. -/
theorem length_pos (l : Seg_nd P) : 0 < l.1.length := length_pos_iff_nd.mpr l.2

/-- Given a segment, the square of its length is equal to the the inner product of the associated vector with itself. -/
theorem length_sq_eq_inner_toVec_toVec : l.length ^ 2 = inner l.toVec l.toVec :=
  (real_inner_self_eq_norm_sq (Seg.toVec l)).symm

/-- The length of a segment is zero if and only if it is degenerate, i.e. it has same source and target. -/
theorem triv_iff_length_eq_zero : (l.target = l.source) ↔ l.length = 0 :=
  (toVec_eq_zero_of_deg).trans norm_eq_zero.symm

/-- Given a segment and a point that lies on the segment, the additional point will separate the segment into two segments, whose lengths add up to the length of the original segment. -/
theorem length_eq_length_add_length (l : Seg P) (A : P) (lieson : A LiesOn l) : l.length = (SEG l.source A).length + (SEG A l.target).length := by
  rcases lieson with ⟨t, ⟨a, b, c⟩⟩
  have h : VEC l.source l.target = VEC l.source A + VEC A l.target := by rw [vec_add_vec]
  have s : VEC A l.target = (1 - t) • VEC l.source l.target := by
    rw [c] at h
    rw [sub_smul, one_smul]
    exact eq_sub_of_add_eq' h.symm
  rw [Seg.length, Seg.length, Seg.length, seg_toVec_eq_vec, seg_toVec_eq_vec, seg_toVec_eq_vec, c, s,
    norm_smul, norm_smul, ← add_mul, Real.norm_of_nonneg a, Real.norm_of_nonneg (sub_nonneg.mpr b)]
  linarith

end length

section midpoint

variable (seg : Seg P) (seg_nd : Seg_nd P) {A : P} {l : Seg P}

/-- Given a segment $AB$, this function returns the midpoint of $AB$, defined as moving from $A$ by the vector $\overrightarrow{AB}/2$. -/
def Seg.midpoint : P := (1 / 2 : ℝ) • seg.toVec +ᵥ seg.source

/-- Given a segment $AB$, the vector from $A$ to the midpoint of $AB$ is half of the vector from $A$ to $B$-/
theorem Seg.vec_source_midpt : VEC seg.1 seg.midpoint = 1 / 2 * VEC seg.1 seg.2 := by
  simp only [midpoint, one_div, Complex.real_smul, Complex.ofReal_inv, vec_of_pt_vadd_pt_eq_vec]
  rfl
/-- Given a segment $AB$, the vector from the midpoint of $AB$ to $B$ is half of the vector from $A$ to $B$-/
theorem Seg.vec_midpt_target : VEC seg.midpoint seg.2 = 1 / 2 * VEC seg.1 seg.2 := by
  rw [midpoint, ← vec_add_vec _ seg.1 _, ← neg_vec, vec_of_pt_vadd_pt_eq_vec]
  field_simp
  calc
    _ = VEC seg.1 seg.2 * (- 1) + VEC seg.1 seg.2 * 2 := by
      rw [mul_neg, mul_one]
      rfl
    _ = _ := by
      rw [← mul_add]
      norm_num

/-- Given a segment $AB$, the vector from $A$ to the midpoint of $AB$ is same as the vector from the midpoint of $AB$ to $B$ -/
theorem Seg.vec_midpt_eq : VEC seg.1 seg.midpoint = VEC seg.midpoint seg.2 := by
  rw[seg.vec_source_midpt, seg.vec_midpt_target]

/-- Given a segment $AB$ and its midpoint P, the vector from $A$ to $P$ is same as the vector from $P$ to $B$ -/
theorem Seg.vec_eq_of_eq_midpt (h : A = l.midpoint) : VEC l.1 A = VEC A l.2 := by
  rw [h]
  exact l.vec_midpt_eq

/-- Given a segment $AB$ and a point P, if vector $\overrightarrow{AP}$ is half of vector $\overrightarrow{AB}$, P is the midpoint of $AB$  -/
theorem midpt_of_vector_from_source (h : VEC l.1 A = 1 / 2 * VEC l.1 l.2) : A = l.midpoint := by
  rw [← start_vadd_vec_eq_end l.1 A, h, Seg.midpoint, Complex.real_smul]
  norm_num
  rfl

/-- Given a segment $AB$ and a point P, if vector $\overrightarrow{PB}$ is half of vector $\overrightarrow{AB}$, P is the midpoint of $AB$  -/
theorem midpt_of_vector_to_target (h : VEC A l.2 = 1 / 2 * VEC l.1 l.2) : A = l.midpoint := by
  refine' midpt_of_vector_from_source _
  nth_rw 1 [eq_sub_of_add_eq (vec_add_vec l.1 A l.2), h, ← one_mul (VEC l.1 l.2), ← sub_mul]
  norm_num

/-- Given a segment $AB$ and a point P, if vector $\overrightarrow{AP}$ is same as vector $\overrightarrow{PB}$, P is the midpoint of $AB$  -/
theorem midpt_of_same_vector_to_source_and_target (h : VEC l.1 A = VEC A l.2) :
    A = l.midpoint := by
  refine' midpt_of_vector_from_source _
  field_simp
  rw [mul_two, ← vec_add_vec l.1 A l.2]
  exact congrArg (HAdd.hAdd _) h

/-- The midpoint of a segment lies on the segment. -/
theorem Seg.midpt_lies_on : seg.midpoint LiesOn seg := ⟨1 / 2, by norm_num; exact seg.vec_source_midpt⟩

/-- The midpoint of a segment lies on the segment. -/
theorem Seg.lies_on_of_eq_midpt (h : A = l.midpoint) : A LiesOn l := by
  rw [h]
  exact l.midpt_lies_on

/-- The midpoint of a nondegenerate segment lies in the interior of the segment. -/
theorem Seg_nd.midpt_lies_int : seg_nd.1.midpoint LiesInt seg_nd.1 :=
  (Seg.lies_int_iff seg_nd.1.midpoint).mpr ⟨seg_nd.2, ⟨1 / 2, by norm_num; exact seg_nd.1.vec_source_midpt⟩⟩

/-- The midpoint of a nondegenerate segment lies in the interior of the segment. -/
theorem Seg_nd.lies_int_of_eq_midpt (h : A = seg_nd.1.midpoint) : A LiesInt seg_nd.1 := by
  rw [h]
  exact seg_nd.midpt_lies_int

/-- A point $X$ on a given segment $AB$ is the midpoint if and only if the vector $\overrightarrow{AX}$ is the same as the vector $\overrightarrow{XB}$. -/
theorem midpt_iff_same_vector_to_source_and_target (A : P) (l : Seg P) : A = l.midpoint ↔ (SEG l.source A).toVec = (SEG A l.target).toVec :=
  ⟨fun h ↦ Seg.vec_eq_of_eq_midpt h, fun h ↦ midpt_of_same_vector_to_source_and_target h⟩

/-- The midpoint of a segment has same distance to the source and to the target of the segment. -/
theorem dist_target_eq_dist_source_of_midpt : (SEG seg.source seg.midpoint).length = (SEG seg.midpoint seg.target).length := congrArg norm seg.vec_midpt_eq

/-- The midpoint of a segment has same distance to the source and to the target of the segment. -/
theorem dist_target_eq_dist_source_of_eq_midpt (h : A = l.midpoint) : (SEG l.1 A).length = (SEG A l.2).length := by
  rw [h]
  exact dist_target_eq_dist_source_of_midpt l

/-- A point $X$ is the midpoint of a segment $AB$ if and only if $X$ lies on $AB$ and $X$ has equal distance to $A$ and $B$. -/
theorem eq_midpoint_iff_in_seg_and_dist_target_eq_dist_source (A : P) (l : Seg P) : A = l.midpoint ↔ (A LiesOn l) ∧ (SEG l.source A).length = (SEG A l.target).length := by
  refine' ⟨fun h ↦ ⟨Seg.lies_on_of_eq_midpt h, dist_target_eq_dist_source_of_eq_midpt h⟩, _⟩
  intro ⟨⟨t, ht0, ht1, ht⟩, hv⟩
  have hv : ‖VEC l.1 A‖ = ‖VEC A l.2‖ := hv
  by_cases h0 : ‖VEC A l.2‖ = 0
  · apply midpt_of_same_vector_to_source_and_target
    rw [h0] at hv
    rw [norm_eq_zero.mp h0, norm_eq_zero.mp hv]
  · have h := ht
    rw [← one_smul ℝ (VEC l.1 A), ← vec_add_vec l.1 A l.2, smul_add, add_comm] at h
    have h := sub_eq_of_eq_add h
    rw [← sub_smul 1 t _] at h
    have h := congrArg norm h
    simp only [norm_smul, hv, Real.norm_of_nonneg ht0, Real.norm_of_nonneg (sub_nonneg.mpr ht1)] at h
    have h : t = 1 / 2 := by
      apply eq_one_div_of_mul_eq_one_left
      rw [mul_two]
      exact (eq_add_of_sub_eq (mul_right_cancel₀ h0 h)).symm
    exact midpt_of_vector_from_source (by rw [ht, h]; norm_num)

end midpoint

section existence

/-- Given a segment $AB$, the midpoint of $A$ and $B + \overrightarrow{AB}$ is B  -/
theorem target_eq_vec_vadd_target_midpt (l : Seg P) : l.2 = (SEG l.1 (l.toVec +ᵥ l.2)).midpoint :=
  midpt_of_same_vector_to_source_and_target (vadd_vsub l.toVec l.2).symm

/-- Given a nondegenerate segment $AB$, B lies in the interior of the segment of $A(B + \overrightarrow{AB})$  -/
theorem Seg_nd.target_lies_int_seg_source_vec_vadd_target (l : Seg_nd P) : l.1.2 LiesInt (SEG l.1.source (l.1.toVec +ᵥ l.1.2)) :=
  lies_int_of_eq_midpt (SEG_nd l.1.1 _ <| fun h ↦ l.2 <| toVec_eq_zero_of_deg.mpr <|
    zero_eq_bit0.mp ((vsub_eq_zero_iff_eq.mpr h).symm.trans <| vadd_vsub_assoc l.1.toVec l.1.2 l.1.1))
      (target_eq_vec_vadd_target_midpt l.1)

/-- Archimedean property I : given a directed segment AB (with A ≠ B), then there exists a point P such that B lies on the directed segment AP and P ≠ B. -/
theorem Seg_nd.exist_pt_beyond_pt (l : Seg_nd P) : (∃ q : P, l.1.target LiesInt (SEG l.1.source q)) :=
  ⟨l.1.toVec +ᵥ l.1.target, l.target_lies_int_seg_source_vec_vadd_target⟩

/-- Archimedean property II: On an nontrivial directed segment, one can always find a point in its interior.  `This will be moved to later disccusion about midpoint of a segment, as the midpoint is a point in the interior of a nontrivial segment`
    If a segment contains an interior point, then it is nondegenerate-/
theorem Seg.nd_of_exist_int_pt {p : P} {l : Seg P} (h : p LiesInt l) : l.is_nd := by
  rcases h with ⟨⟨_, ⟨_, _, e⟩⟩, ⟨p_ne_s, _⟩⟩
  have t : VEC Seg.source p ≠ 0 := (ne_iff_vec_ne_zero Seg.source p).mp p_ne_s
  rw [e] at t
  exact Iff.mp vsub_ne_zero (right_ne_zero_of_smul t)

/-- A segment is nondegenerate if and only if it contains an interior point -/
theorem Seg.nd_iff_exist_int_pt (l : Seg P) : (∃ (p : P), p LiesInt l) ↔ l.is_nd :=
  ⟨fun ⟨_, b⟩ ↦ nd_of_exist_int_pt b, fun h ↦ ⟨l.midpoint, Seg_nd.midpt_lies_int ⟨l, h⟩⟩⟩

/-- If a segment is nondegenerate, it contains an interior point -/
theorem Seg_nd.exist_int_pt (l : Seg_nd P) : ∃ (p : P), p LiesInt l.1 := ⟨l.1.midpoint, midpt_lies_int l⟩

/-- A segment contains an interior point if and only if its length is positive -/
theorem Seg.length_pos_iff_exist_int_pt (l : Seg P) : 0 < l.length ↔ (∃ (p : P), p LiesInt l) :=
  length_pos_iff_nd.trans (nd_iff_exist_int_pt l).symm

/-- A ray contains two distinct points -/
theorem Ray.nontriv (r : Ray P) : ∃ (A B : P), (A ∈ r.carrier) ∧ (B ∈ r.carrier) ∧ (B ≠ A) := sorry

end existence

end EuclidGeom
