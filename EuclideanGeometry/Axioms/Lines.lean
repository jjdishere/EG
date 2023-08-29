import EuclideanGeometry.Axioms.Basic

/-!
# Segments, rays, and lines

We define the class of (directed) segments, rays, and lines and their coersions. We also define the proposition of a point lying on such a structure. Finally, we discuss the nonemptyness of such structures.

## Important definitions

* `Ray` : the class of rays on an EuclideanPlane
* 


## Notation

## Implementation Notes

## Further Works

-/

namespace EuclidGeom

/- Rays -/
@[ext]
class Ray (P : Type _) [EuclideanPlane P] where
  source : P
  direction: UniVec

/- Def of point lies on a ray -/
def IsOnRay {P : Type _} [EuclideanPlane P] (a : P) (l : Ray P) : Prop :=
  ∃ (t : ℝ) (ht : t ≥ 0), (a : P) = t • l.direction.vec +ᵥ l.source

infixl : 50 "LiesOnRay" => IsOnRay

-- theorem ... : unique t in IsOnRay

/- Generalized Directed segment -/
@[ext]
class GDirSeg (P : Type _) [EuclideanPlane P]where
  source : P
  target : P

/- Directed segment -/
class DirSeg (P : Type _) [EuclideanPlane P] extends Ray P, GDirSeg P where
  on_ray : target LiesOnRay toRay 
  non_triv : source ≠ target
  
-- theorem xxx_ne_zero :(Classical.choose (p LiesOnRay l)) ≠ 0 := sorry

class Line (P : Type _) [EuclideanPlane P] where
-- What is a line??? to be affine subspaces of dimension 1, citing affine vector spaces?
-- carrier : Set P
-- linearity

instance {P : Type _} [EuclideanPlane P] : Coe (Ray P) (Line P) where
  coe := sorry

class GSeg (P : Type _) [EuclideanPlane P] where
-- a multiset of 2 points?

class Seg (P : Type _) [EuclideanPlane P] where
-- a multiset of 2 diff points?
-- carrier

/- Define a point lies on an oriented segment, a line, a segment -/

/- Relations between these concepts as coersion-/

/- Archimedean properties: on a ray/line, one can always find a far away point, and on an oriented segment, one can always find a point in the interior. -/

end EuclidGeom