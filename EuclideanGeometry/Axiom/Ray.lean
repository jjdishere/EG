import EuclideanGeometry.Axiom.Basic

/-!
# Directed segments and rays

We define the class of (directed) segments, rays, and lines and their coersions. We also define the proposition of a point lying on such a structure. Finally, we discuss the nonemptyness of such structures.

## Important definitions

* `Ray` : the class of rays on an EuclideanPlane
* 


## Notation

## Implementation Notes

## Further Works

-/

namespace EuclidGeom

section defs
/- Rays -/
@[ext]
class Ray (P : Type _) [EuclideanPlane P] where
  source : P
  direction: UniVec

/- Def of point lies on a ray -/
def IsOnRay {P : Type _} [EuclideanPlane P] (a : P) (l : Ray P) : Prop :=
  ∃ (t : ℝ) (ht : 0 ≤ t ), (a : P) = t • l.direction.vec +ᵥ l.source

infixl : 50 "LiesOnRay" => IsOnRay

-- theorem ... : unique t in IsOnRay

/- Generalized Directed segment -/
@[ext]
class GDirSeg (P : Type _) [EuclideanPlane P]where
  source : P
  target : P

namespace GDirSeg

def length {P : Type _} [EuclideanPlane P] (l : GDirSeg P): ℝ := sorry 

end GDirSeg

-- variable (P : Type _) [EuclideanPlane P] (l : GDirSeg P)
-- #check (l.length)

/- Directed segment -/
class DirSeg (P : Type _) [EuclideanPlane P] extends Ray P, GDirSeg P where
  on_ray : target LiesOnRay toRay 
  non_triv : source ≠ target
  -- length : ℝ (Or NNReal ?)
  -- vsub_eq_len_smul_dir : target -ᵥ source = length • direction 
  -- nontriv : length > 0
    
--  theorem xxx_ne_zero :(Classical.choose (p LiesOnRay l)) ≠ 0 := sorry. Don't need this if add length into def of class DirSeg

-- def length of DirSeg, length of GDirSeg, length = 0 implies same point, length of DirSeg = length of GDirSeq (move length after coe)

end defs

section mk
-- mk method of GDirSeg giving 2 points, this is auto generated as GDirSeg.mk
-- mk method of DirSeg giving 2 distinct point

-- mk method of Ray giving 2 distinct point
-- ...
-- notation   
end mk

section LiesOn
/- Define a point lies on an oriented segment, a line, a segment, immediate consequences -/
def IsOnDirSeg {P : Type _} [EuclideanPlane P] (a : P) (l : DirSeg P) : Prop :=
  ∃ (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1 ), (a : P) = t • (l.target -ᵥ l.source) +ᵥ l.source

infixl : 50 "LiesOnDirSeg" => IsOnDirSeg

def IsOnGDirSeg {P : Type _} [EuclideanPlane P] (a : P) (l : DirSeg P) : Prop :=
  ∃ (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1 ), (a : P) = t • (l.target -ᵥ l.source) +ᵥ l.source

infixl : 50 "LiesOnGDirSeg" => IsOnGDirSeg

end LiesOn

/- Relations between these concepts as coersion, theorems-/
section coe

instance {P : Type _} [EuclideanPlane P] : Coe (DirSeg P) (Ray P) where
  coe := fun _ => by infer_instance

-- Coe from DirSeg to Ray, GDirSeg is by infer_instance

-- def of DirSeg from GDirSeg if length ≠ 0
def GDirSeg.toDirSeg_of_nontriv {P : Type _} [EuclideanPlane P] (l : GDirSeg P) (nontriv : l.source ≠ l.target): DirSeg P := sorry

-- coe from GDirSeg to Vector, should I name ℝ × ℝ as Vectors?

-- theorems of "if p LiesOnRay l, then p LiesOnLine l" each coe should equipped with a theorem here 
end coe

--theorem of samepoint if length GDirSeg = 0?

section existance
/- Archimedean properties: on a ray/line, one can always find a far away point, and on an oriented segment, one can always find a point in the interior. -/
end existance

end EuclidGeom