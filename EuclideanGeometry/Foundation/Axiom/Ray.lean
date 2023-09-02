import EuclideanGeometry.Foundation.Axiom.Plane

/-!
# Directed segments and rays

We define the class of (generalized) directed segments and rays, and their coersions. We also define the property of a point lying on such a structure. Finally, we discuss the nonemptyness/degeneracy of generalized directed segments.

## Important definitions

* `Ray` : the class of rays on an EuclideanPlane
* `GDSeg` : the class of generalized directed segments on an EuclideanPlane (meaning segments with specified source and target, but allowing it to reduce to a singleton.)


## Notation

* notation for lieson
* notation for DSeg A B, GDSeg A B, Ray A B

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
  ∃ (t : ℝ) (ht : 0 ≤ t ), (a : P) = t • l.direction.vec +ᵥ l.source

/- Generalized Directed segment -/
@[ext]
class GDSeg (P : Type _) [EuclideanPlane P] where
  source : P
  target : P

/- Directed segment -/
class DSeg (P : Type _) [EuclideanPlane P] extends Ray P, GDSeg P where
  on_ray : IsOnRay target toRay 
  non_triv : target ≠ source

/- Define a point lies on an oriented segment, a line, a segment, immediate consequences -/
def IsOnDSeg {P : Type _} [EuclideanPlane P] (a : P) (l : DSeg P) : Prop :=
  ∃ (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1 ), (a : P) = t • (l.target -ᵥ l.source) +ᵥ l.source

def IsOnGDSeg {P : Type _} [EuclideanPlane P] (a : P) (l : GDSeg P) : Prop :=
  ∃ (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1 ), (a : P) = t • (l.target -ᵥ l.source) +ᵥ l.source

end definitions

scoped infix : 50 "LiesOnRay" => IsOnRay
scoped infix : 50 "LiesOnDSeg" => IsOnDSeg
scoped infix : 50 "LiesOnGDSeg" => IsOnGDSeg

/- Relations between these concepts as coersion, theorems-/
section coersions

instance {P : Type _} [EuclideanPlane P] : Coe (DSeg P) (GDSeg P) where
  coe := fun _ => DSeg.toGDSeg

/- def of DirSeg from GDirSeg if length ≠ 0 -/
def GDSeg.toDSeg_of_nontriv {P : Type _} [EuclideanPlane P] (l : GDSeg P) (nontriv : l.target ≠ l.source): DSeg P where
  source := l.source
  target := l.target
  direction := normalize (l.target -ᵥ l.source) (vsub_ne_zero.mpr nontriv)
  on_ray := sorry
  non_triv := sorry

-- coe from GDirSeg to Vector
def GDSeg.toVec {P : Type _} [EuclideanPlane P] (l : GDSeg P) : (ℝ × ℝ) := l.target -ᵥ l.source 

-- theorems "if p LiesOnDSeg l, then p LiesOnRay l.toRay and p LiesOnGDSeg l.toGDSeg"

theorem DSeg.pt_on_toRay_of_pt_on_DSeg {P : Type _} [EuclideanPlane P] (p : P) (l : DSeg P) (lieson : p LiesOnDSeg l) : p LiesOnRay l.toRay := sorry

theorem DSeg.pt_on_toGDSeg_of_pt_on_DSeg {P : Type _} [EuclideanPlane P] (p : P) (l : DSeg P) (lieson : p LiesOnDSeg l) : p LiesOnGDSeg l.toGDSeg := sorry



end coersions

section mk

-- mk method of DirSeg giving 2 distinct point
def DSeg.mk_pt_pt {P : Type _} [EuclideanPlane P] (A B : P) (h : B ≠ A) : DSeg P := sorry  

-- mk method of Ray giving 2 distinct point
def Ray.mk_pt_pt {P : Type _} [EuclideanPlane P] (A B : P) (h : B ≠ A) : Ray P where
  source := A
  direction := normalize (B -ᵥ A) (vsub_ne_zero.mpr h)

-- notation 
end mk

scoped notation "GSEG" => GDSeg.mk



section length

namespace GDSeg

variable {P : Type _} [EuclideanPlane P] (l : GDSeg P)

-- define the length of a generalized directed segment.
def length : ℝ := StdR2.Norm.norm (l.toVec)

-- length of a generalized directed segment is nonnegative.
theorem length_nonneg : 0 ≤ l.length := by exact @norm_nonneg _ StdR2.SeminormedAddGroup _

-- A generalized directed segment is trivial if and only if length is zero.
theorem is_triv_iff_length_eq_zero : (l.target = l.source) ↔ l.length = 0 := by sorry

-- A generalized directed segment is nontrivial if and only if its length is positive.
theorem nontriv_iff_length_pos : (l.target ≠ l.source) ↔ 0 < l.length := by sorry

-- If P lies on a generalized directed segment AB, then length(AB) = length(AP) + length(PB)
theorem length_eq_sum_of_length_two_part (l : GDSeg P) (p : P) (lieson : p LiesOnGDSeg l) : l.length = (GSEG l.source p).length + (GSEG p l.target).length := sorry





end GDSeg

namespace DSeg

def length {P : Type _} [EuclideanPlane P] (l : DSeg P): ℝ := (l : GDSeg P).length



end DSeg 

end length



section existance
-- Archimedean property : 

-- theorem Ray.exist_pt_beyond_pt {P : Type _} [EuclideanPlane P] (ray : Ray P) (p : P) (h: p LiesOnRay ray) : (∃ q : P, p LiesOn 


-- Archimedean property II: Onn an oriented segment, one can always find a point in the interior.

-- theorem 

-- The generalized directed segment is nontrivial if and only if one can find a point in the interior of the generalized segment.
-- theorem nontriv_iff_exist_inter_pt {P : Type _} [EuclideanPlane P] (l : GDSeg P) (interior : ∃ (p : P), (p LiesOnGDSeg l) ∧ (p ≠ l.source) ∧ (p ≠ l.target) ) : (l.target ≠ l.source) := by sorry

-- In this proof, may need to use Classical.choose (p LiesOnRay l)....

end existance

end EuclidGeom