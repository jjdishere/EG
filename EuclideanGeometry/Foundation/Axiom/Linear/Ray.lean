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

section definitions
/- Rays -/
@[ext]
class Ray (P : Type _) [EuclideanPlane P] where
  source : P
  toDir: Dir
  
/- Def of point lies on a ray -/
def IsOnRay {P : Type _} [EuclideanPlane P] (a : P) (l : Ray P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ a = t • l.toDir.toVec +ᵥ l.source

namespace Ray 

variable {P : Type _} [EuclideanPlane P] (ray : Ray P)

/- Def of point lies on a ray -/
protected def IsOn (a : P) (ray : Ray P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ VEC ray.source a = t • ray.toDir.toVec

protected def IsInt (a : P) (ray : Ray P) : Prop := Ray.IsOn a ray ∧ a ≠ ray.source

def toProj : Proj := (ray.toDir : Proj)

-- instance : PlaneFigure P (Ray P) where

instance : Carrier P (Ray P) where
  carrier := fun l => { p : P | Ray.IsOn p l }

instance : Interior P (Ray P) where
  interior := fun l => { p : P | Ray.IsInt p l }

end Ray

/- Generalized Directed segment -/
@[ext]
class Seg (P : Type _) [EuclideanPlane P] where
  source : P
  target : P

namespace Seg

variable {P : Type _} [EuclideanPlane P]

def is_nd (seg : Seg P) : Prop := seg.target ≠ seg.source

protected def IsOn (a : P) (seg : Seg P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧ VEC seg.source a  = t • (VEC seg.source seg.target)

protected def IsInt (a : P) (seg : Seg P) : Prop := Seg.IsOn a seg ∧ a ≠ seg.source ∧ a ≠ seg.target 

-- instance : PlaneFigure P (Seg P) where

instance : Carrier P (Seg P) where
  carrier := fun s => { p : P | Seg.IsOn p s }

instance : Interior P (Seg P) where
  interior := fun s => { p : P | Seg.IsInt p s }

end Seg

scoped notation "SEG" => Seg.mk

def Seg_nd (P : Type _) [EuclideanPlane P] := {seg : Seg P // seg.is_nd}

namespace Seg_nd

variable {P : Type _} [EuclideanPlane P]

def mk (A B : P) (h : B ≠ A) : Seg_nd P where
  val := SEG A B
  property := h

protected def IsOn (a : P) (seg_nd : Seg_nd P) : Prop := Seg.IsOn a seg_nd.1

protected def IsInt (a : P) (seg_nd : Seg_nd P) : Prop := Seg.IsInt a seg_nd.1

-- instance : PlaneFigure P (Seg_nd P) where

instance : Carrier P (Seg_nd P) where
  carrier := fun s => { p : P | Seg_nd.IsOn p s }

instance : Interior P (Seg_nd P) where
  interior := fun s => { p : P | Seg_nd.IsInt p s }

end Seg_nd

scoped notation "SEG_nd" => Seg_nd.mk
variable  {P : Type _} [EuclideanPlane P] (A B : P) ( h : B ≠ A)

#check SEG_nd A B h

end definitions

variable {P : Type _} [EuclideanPlane P]

theorem source_of_ray_lies_on_ray (r : Ray P) : r.source LiesOn r := by
  sorry

/- Coe from Seg to Vector, Ray-/
namespace Seg 

variable {P : Type _} [EuclideanPlane P] (seg : Seg P) 

def toVec : Vec := VEC seg.source seg.target

@[simp]
theorem seg_toVec_eq_vec (A B : P) : (SEG A B).toVec = VEC A B := by
  sorry

end Seg

namespace Seg_nd

instance : Coe (Seg_nd P) (Seg P) where
  coe := fun x => x.1

variable {P : Type _} [EuclideanPlane P] (seg_nd : Seg_nd P)

def toVec_nd : Vec_nd := ⟨VEC seg_nd.1.source seg_nd.1.target, (ne_iff_vec_ne_zero _ _).mp seg_nd.2⟩ 

def toDir : Dir := Vec_nd.normalize seg_nd.toVec_nd

def toRay : Ray P where
  source := seg_nd.1.source
  toDir := seg_nd.toDir

def toProj : Proj := (seg_nd.toVec_nd.toProj : Proj)

end Seg_nd

section mk

-- mk method of Ray giving 2 distinct point
def Ray.mk_pt_pt {P : Type _} [EuclideanPlane P] (A B : P) (h : B ≠ A) : Ray P where
  source := A
  toDir := Vec_nd.normalize ⟨VEC A B, (vsub_ne_zero.mpr h)⟩ 

-- notation 
end mk

scoped notation "RAY" => Ray.mk_pt_pt

section length

variable {P : Type _} [EuclideanPlane P] (l : Seg P)

namespace Seg

-- define the length of a generalized directed segment.
def length : ℝ := Vec.Norm.norm (l.toVec)

-- length of a generalized directed segment is nonnegative.
theorem length_nonneg : 0 ≤ l.length := by exact @norm_nonneg _ Vec.SeminormedAddGroup _

theorem length_sq_eq_inner_toVec_toVec : l.length ^ 2 = Vec.InnerProductSpace.Core.inner l.toVec l.toVec := by
  have w : l.length = Real.sqrt (Vec.InnerProductSpace.Core.inner l.toVec l.toVec) := by rfl
  rw [w]
  have n : 0 ≤ Vec.InnerProductSpace.Core.inner l.toVec l.toVec := by 
    exact Vec.InnerProductSpace.Core.nonneg_re l.toVec
  rw [Real.sq_sqrt n]

theorem toVec_eq_zero_of_deg : (l.target = l.source) ↔ l.toVec = 0 := by unfold Seg.toVec Vec.mk_pt_pt; simp

-- A generalized directed segment is trivial if and only if length is zero.
theorem triv_iff_length_eq_zero : (l.target = l.source) ↔ l.length = 0 := by
  unfold Seg.length
  exact Iff.trans (Seg.toVec_eq_zero_of_deg _)  (@norm_eq_zero _ Vec.NormedAddGroup).symm

-- A generalized directed segment is nontrivial if and only if its length is positive.
theorem nd_iff_length_pos : (l.is_nd) ↔ 0 < l.length := by sorry

-- If P lies on a generalized directed segment AB, then length(AB) = length(AP) + length(PB)
theorem length_eq_sum_of_length_two_part (l : Seg P) (p : P) (lieson : p LiesOn l) : l.length = (SEG l.source p).length + (SEG p l.target).length := sorry

theorem nd_of_exist_inter_pt (l : Seg P) (p : P) (h : p LiesInt l) : l.is_nd := sorry

-- If a generalized directed segment contains an interior point, then it is nontrivial
theorem nd_iff_exist_inter_pt (l : Seg P) : ∃ (p : P), p LiesInt l ↔ l.is_nd := sorry

end Seg

namespace Seg_nd

theorem Seg_nd.length_pos (l : Seg_nd P): 0 < l.1.length := by sorry

theorem exist_inter_pt (l : Seg_nd P) : ∃ (p : P), p LiesInt l := sorry

end Seg_nd

end length


section Archimedean_property

-- Archimedean property I : given a directed segment AB (with A ≠ B), then there exists a point P such that B lies on the directed segment AP and P ≠ B.

theorem exist_pt_beyond_pt {P : Type _} [EuclideanPlane P] (l : Seg P) (nontriv : l.is_nd) : (∃ q : P, l.target LiesInt (SEG l.source q)) := by sorry

-- Archimedean property II: On an nontrivial directed segment, one can always find a point in its interior.  `This will be moved to later disccusion about midpoint of a segment, as the midpoint is a point in the interior of a nontrivial segment`

end Archimedean_property

end EuclidGeom