import EuclideanGeometry.Axioms.Basic

namespace EuclidGeom

variable (P : Type _) [h : EuclideanPlane P]

/- Rays -/

class Ray where
  source : P
  direction: UniVec

/- def lies on a ray -/

variable (l : Ray P)
#check l.direction.vec

def LiesOnRay (a : P) (l : Ray P) : Prop :=
  ∃ (t : ℝ) (ht : t ≥ 0), a = (t • (l.direction.vec)) +ᵥ (l.source)


/- Directed segment -/

class DirSeg extends Ray P where
  target : P



class DirSeg_gen where
  source : P
  target : P



/- 1.2 Segments, rays, and lines -/

/- Define vectors in dimension 2 -/

/- Define oriented segments, including "carrier" and endpoints, and directions (a unit vector).  Here we only allow nondegenerate oriented segements. Next, we define oriented segments_generalized (which only remebers the starting and end points), which allows the two points to be identified; and view oriented segments as an instance.  -/

/- Define the interior of an oriented segment -/



/- Define rays, including "carrier", endpoints, and directions. -/

/- Define lines to be affine subspaces of dimension 1, citing affine vector spaces. -/

/- Relations between these concepts -/




/- Archimedean properties: on a ray/line, one can always find a far away point, and on an oriented segment, one can always find a point in the interior. -/

end EuclidGeom