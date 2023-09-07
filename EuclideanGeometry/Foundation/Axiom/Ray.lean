import EuclideanGeometry.Foundation.Axiom.Plane

/-!
# Segments and rays

We define the class of generalized directed segments and rays, and their coersions. We also define the property of a point lying on such a structure. Finally, we discuss the nonemptyness/degeneracy of generalized directed segments. 

From now on, by "segment" we mean a generalized directed segment.

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

namespace Ray 

variable {P : Type _} [EuclideanPlane P] (ray : Ray P)


/- Def of point lies on a ray -/
def IsOnRay {P : Type _} [EuclideanPlane P] (a : P) (ray : Ray P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ a = t • ray.direction.vec +ᵥ ray.source

def IsOnIntRay {P : Type _} [EuclideanPlane P] (a : P) (ray : Ray P) : Prop := IsOnRay a ray ∧ a ≠ ray.source

def toProj : Proj := (ray.direction : Proj)

end Ray

/- Generalized Directed segment -/
@[ext]
class Seg (P : Type _) [EuclideanPlane P] where
  source : P
  target : P

namespace Seg

def is_nontriv {P : Type _} [EuclideanPlane P] (seg : Seg P) : Prop := seg.target ≠ seg.source 

def IsOnSeg {P : Type _} [EuclideanPlane P] (a : P) (seg : Seg P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧ a = t • (VEC seg.source seg.target) +ᵥ seg.source

def IsOnIntSeg {P : Type _} [EuclideanPlane P] (a : P) (seg : Seg P) : Prop := IsOnSeg a seg ∧ a ≠ seg.source ∧ a ≠ seg.target 

end Seg

end definitions

scoped infix : 50 "LiesOnRay" => Ray.IsOnRay
scoped infix : 50 "LiesOnSeg" => Seg.IsOnSeg
scoped infix : 50 "LiesOnIntRay" => Ray.IsOnIntRay
scoped infix : 50 "LiesOnIntSeg" => Seg.IsOnIntSeg

/- Coe from Seg to Vector, Ray-/
namespace Seg 

variable {P : Type _} [EuclideanPlane P] (seg : Seg P)

def toVec : (ℝ × ℝ) := VEC seg.source seg.target

variable (h : seg.is_nontriv)
def direction_of_nontriv : UniVec := UniVec.normalize seg.toVec ((ne_iff_vec_nonzero _ _).mp h)

def toRay_of_nontriv : Ray P where
  source := seg.source
  direction := seg.direction_of_nontriv h

def toProj_of_nontriv : Proj := (seg.direction_of_nontriv h : Proj)

end Seg

section mk

-- mk method of Ray giving 2 distinct point
def Ray.mk_pt_pt {P : Type _} [EuclideanPlane P] (A B : P) (h : B ≠ A) : Ray P where
  source := A
  direction := UniVec.normalize (VEC A B) (vsub_ne_zero.mpr h)

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
theorem triv_iff_length_eq_zero : (l.target = l.source) ↔ l.length = 0 := by sorry

-- A generalized directed segment is nontrivial if and only if its length is positive.
theorem nontriv_iff_length_pos : (l.is_nontriv) ↔ 0 < l.length := by sorry

-- If P lies on a generalized directed segment AB, then length(AB) = length(AP) + length(PB)
theorem length_eq_sum_of_length_two_part (l : Seg P) (p : P) (lieson : p LiesOnSeg l) : l.length = (SEG l.source p).length + (SEG p l.target).length := sorry

-- If a generalized directed segment contains an interior point, then it is nontrivial
theorem nontriv_iff_exist_inter_pt (l : Seg P) (p : P) (lieson : p LiesOnIntSeg l) : l.is_nontriv := sorry

end Seg

end length

section Archimedean_property

-- Archimedean property I : given a directed segment AB (with A ≠ B), then there exists a point P such that B lies on the directed segment AP and P ≠ B.

theorem exist_pt_beyond_pt {P : Type _} [EuclideanPlane P] (l : Seg P) (nontriv : l.is_nontriv) : (∃ q : P, l.target LiesOnIntSeg (SEG l.source q)) := by sorry

-- Archimedean property II: On an nontrivial directed segment, one can always find a point in its interior.  `This will be moved to later disccusion about midpoint of a segment, as the midpoint is a point in the interior of a nontrivial segment`

end Archimedean_property

end EuclidGeom