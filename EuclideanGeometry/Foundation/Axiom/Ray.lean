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
  non_triv : source ≠ target

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

-- theorems of "if p LiesOnRay l, then p LiesOnLine l" each coe should equipped with a theorem here 
end coersions

section mk

-- mk method of DirSeg giving 2 distinct point
def DSeg.mk_pt_pt {P : Type _} [EuclideanPlane P] (A B : P) (h : A ≠ B) : DSeg P := sorry  

-- mk method of Ray giving 2 distinct point
def Ray.mk_pt_pt {P : Type _} [EuclideanPlane P] (A B : P) (h : A ≠ B) : Ray P where
  source := A
  direction := normalize (B -ᵥ A) (vsub_ne_zero.mpr (Ne.symm h))

-- notation 
end mk

scoped notation "GSEG" => GDSeg.mk

section length

namespace GDSeg

def length {P : Type _} [EuclideanPlane P] (l : GDSeg P): ℝ := sorry

end GDSeg

namespace DSeg

def length {P : Type _} [EuclideanPlane P] (l : GDSeg P): ℝ := (l : GDSeg P).length

end DSeg 

-- theorem length >0, ≥0 
-- theorem xxx_ne_zero :(Classical.choose (p LiesOnRay l)) ≠ 0 := sorry. Don't need this if add length into def of class DirSeg

-- def length of DirSeg, length of GDirSeg, length = 0 implies same point, length of DirSeg = length of GDirSeq (move length after coe)


--theorem of samepoint if length GDirSeg = 0?
end length

section existance
/- Archimedean properties: on a ray/line, one can always find a far away point, and on an oriented segment, one can always find a point in the interior. -/
end existance

end EuclidGeom