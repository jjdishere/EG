import EuclideanGeometry.Foundation.Axiom.Plane

/-!
# Segments and rays

We define the class of generalized directed segments and rays, and their coersions. We also define the property of a point lying on such a structure. Finally, we discuss the nonemptyness/degeneracy of generalized directed segments. 

From now on, by "segment" we mean a generalized directed segment

## Important definitions

* `Ray` : the class of rays on an EuclideanPlane
* `Seg` : the class of generalized directed segments on an EuclideanPlane (meaning segments with specified source and target, but allowing it to reduce to a singleton.)


## Notation

* `LiesOnRay` : notation for a point lies on a ray
* `LiesOnSeg` : notation for a point lies on a generalized directed segment
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
  direction: UniVec

/- Def of point lies on a ray -/
def IsOnRay {P : Type _} [EuclideanPlane P] (a : P) (l : Ray P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ a = t • l.direction.vec +ᵥ l.source

/- Generalized Directed segment -/
@[ext]
class Seg (P : Type _) [EuclideanPlane P] where
  source : P
  target : P

def IsOnSeg {P : Type _} [EuclideanPlane P] (a : P) (l : Seg P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧ a = t • (l.target -ᵥ l.source) +ᵥ l.source

end definitions

scoped infix : 50 "LiesOnRay" => IsOnRay
scoped infix : 50 "LiesOnSeg" => IsOnSeg

/- Coe from Seg to Vector, Ray-/
namespace Seg 

def toVec {P : Type _} [EuclideanPlane P] (l : Seg P) : (ℝ × ℝ) := l.target -ᵥ l.source 

def toRay_of_nontriv {P : Type _} [EuclideanPlane P] (l : Seg P) (h : l.target ≠ l.source) : Ray P := sorry

end Seg

section mk

-- mk method of Ray giving 2 distinct point
def Ray.mk_pt_pt {P : Type _} [EuclideanPlane P] (A B : P) (h : B ≠ A) : Ray P where
  source := A
  direction := UniVec.normalize (B -ᵥ A) (vsub_ne_zero.mpr h)

-- notation 
end mk

scoped notation "SEG" => Seg.mk
scoped notation "RAY" => Ray.mk_pt_pt

section length

namespace Seg

variable {P : Type _} [EuclideanPlane P] (l : Seg P)

-- define the length of a generalized directed segment.
def length : ℝ := StdR2.Norm.norm (l.toVec)

-- length of a generalized directed segment is nonnegative.
theorem length_nonneg : 0 ≤ l.length := by exact @norm_nonneg _ StdR2.SeminormedAddGroup _

-- A generalized directed segment is trivial if and only if length is zero.
theorem is_triv_iff_length_eq_zero : (l.target = l.source) ↔ l.length = 0 := by sorry

-- A generalized directed segment is nontrivial if and only if its length is positive.
theorem nontriv_iff_length_pos : (l.target ≠ l.source) ↔ 0 < l.length := by sorry

-- If P lies on a generalized directed segment AB, then length(AB) = length(AP) + length(PB)
theorem length_eq_sum_of_length_two_part (l : Seg P) (p : P) (lieson : p LiesOnSeg l) : l.length = (SEG l.source p).length + (SEG p l.target).length := sorry

end Seg

end length

section existance
-- Archimedean property : 

-- theorem Ray.exist_pt_beyond_pt {P : Type _} [EuclideanPlane P] (ray : Ray P) (p : P) (h: p LiesOnRay ray) : (∃ q : P, p LiesOn 


-- Archimedean property II: Onn an oriented segment, one can always find a point in the interior.

-- theorem 

-- The generalized directed segment is nontrivial if and only if one can find a point in the interior of the generalized segment.
-- theorem nontriv_iff_exist_inter_pt {P : Type _} [EuclideanPlane P] (l : Seg P) (interior : ∃ (p : P), (p LiesOnSeg l) ∧ (p ≠ l.source) ∧ (p ≠ l.target) ) : (l.target ≠ l.source) := by sorry

-- In this proof, may need to use Classical.choose (p LiesOnRay l)....

end existance

end EuclidGeom