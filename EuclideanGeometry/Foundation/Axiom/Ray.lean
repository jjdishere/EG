import EuclideanGeometry.Foundation.Axiom.Plane

/-!
# DSegments and rays

We define the class of generalized directed segments and rays, and their coersions. We also define the property of a point lying on such a structure. Finally, we discuss the nonemptyness/degeneracy of generalized directed segments. 

From now on, by "segment" we mean a generalized directed segment.

## Important definitions

* `Ray` : the class of rays on an EuclideanPlane
* `DSeg` : the class of generalized directed segments on an EuclideanPlane (meaning segments with specified source and target, but allowing it to reduce to a singleton.)


## Notation

* `LiesOnRay` : notation for a point lies on a ray
* `LiesOnDSeg` : notation for a point lies on a generalized directed segment
* notation for DSeg A B

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
def IsOnRay {P : Type _} [EuclideanPlane P] (a : P) (ray : Ray P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ a = t • ray.toDir.toVec +ᵥ ray.source

def IsOnIntRay {P : Type _} [EuclideanPlane P] (a : P) (ray : Ray P) : Prop := IsOnRay a ray ∧ a ≠ ray.source

def toProj : Proj := (ray.toDir : Proj)

end Ray
  
/- Generalized Directed segment -/
@[ext]
class DSeg (P : Type _) [EuclideanPlane P] where
  source : P
  target : P

namespace DSeg

def is_nontriv {P : Type _} [EuclideanPlane P] (dseg : DSeg P) : Prop := dseg.target ≠ dseg.source 

def IsOnDSeg {P : Type _} [EuclideanPlane P] (a : P) (dseg : DSeg P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧ a = t • (VEC dseg.source dseg.target) +ᵥ dseg.source

def IsOnIntDSeg {P : Type _} [EuclideanPlane P] (a : P) (dseg : DSeg P) : Prop := IsOnDSeg a dseg ∧ a ≠ dseg.source ∧ a ≠ dseg.target 

end DSeg

end definitions

scoped infix : 50 "LiesOnRay" => Ray.IsOnRay
scoped infix : 50 "LiesOnDSeg" => DSeg.IsOnDSeg
scoped infix : 50 "LiesOnIntRay" => Ray.IsOnIntRay
scoped infix : 50 "LiesOnIntDSeg" => DSeg.IsOnIntDSeg

/- Coe from DSeg to Vector, Ray-/
namespace DSeg 

variable {P : Type _} [EuclideanPlane P] (dseg : DSeg P)

def toVec : Vec := VEC dseg.source dseg.target

variable (h : dseg.is_nontriv)
def toDir_of_nontriv : Dir := Vec.normalize dseg.toVec ((ne_iff_vec_nonzero _ _).mp h)

def toRay_of_nontriv : Ray P where
  source := dseg.source
  toDir := dseg.toDir_of_nontriv h

def toProj_of_nontriv : Proj := (dseg.toDir_of_nontriv h : Proj)

end DSeg

section mk

-- mk method of Ray giving 2 distinct point
def Ray.mk_pt_pt {P : Type _} [EuclideanPlane P] (A B : P) (h : B ≠ A) : Ray P where
  source := A
  toDir := Vec.normalize (VEC A B) (vsub_ne_zero.mpr h)

-- notation 
end mk

scoped notation "DSEG" => DSeg.mk
scoped notation "RAY" => Ray.mk_pt_pt

section length

namespace DSeg

variable {P : Type _} [EuclideanPlane P] (l : DSeg P)

-- define the length of a generalized directed segment.
def length : ℝ := Vec.Norm.norm (l.toVec)

-- length of a generalized directed segment is nonnegative.
theorem length_nonneg : 0 ≤ l.length := by exact @norm_nonneg _ Vec.SeminormedAddGroup _

-- A generalized directed segment is trivial if and only if length is zero.
theorem triv_iff_length_eq_zero : (l.target = l.source) ↔ l.length = 0 := by sorry

-- A generalized directed segment is nontrivial if and only if its length is positive.
theorem nontriv_iff_length_pos : (l.is_nontriv) ↔ 0 < l.length := by sorry

-- If P lies on a generalized directed segment AB, then length(AB) = length(AP) + length(PB)
theorem length_eq_sum_of_length_two_part (l : DSeg P) (p : P) (lieson : p LiesOnDSeg l) : l.length = (DSEG l.source p).length + (DSEG p l.target).length := sorry

-- If a generalized directed segment contains an interior point, then it is nontrivial
theorem nontriv_iff_exist_inter_pt (l : DSeg P) (p : P) (lieson : p LiesOnIntDSeg l) : l.is_nontriv := sorry

end DSeg

end length


section Archimedean_property

-- Archimedean property I : given a directed segment AB (with A ≠ B), then there exists a point P such that B lies on the directed segment AP and P ≠ B.

theorem exist_pt_beyond_pt {P : Type _} [EuclideanPlane P] (l : DSeg P) (nontriv : l.is_nontriv) : (∃ q : P, l.target LiesOnIntDSeg (DSEG l.source q)) := by sorry

-- Archimedean property II: On an nontrivial directed segment, one can always find a point in its interior.  `This will be moved to later disccusion about midpoint of a segment, as the midpoint is a point in the interior of a nontrivial segment`

end Archimedean_property

end EuclidGeom