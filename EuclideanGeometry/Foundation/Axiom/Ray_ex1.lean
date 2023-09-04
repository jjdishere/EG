import EuclideanGeometry.Foundation.Axiom.Ray


namespace EuclidGeom

namespace Seg 
variable {P: Type _} [EuclideanPlane P] (seg : Seg P) 

-- source and targets are on generalized directed segments
theorem source_lies_on_seg : seg.source LiesOnSeg seg := by sorry

theorem target_lies_on_seg : seg.source LiesOnSeg seg := by sorry

-- definition of reversion of the direction of a generalized directed segment
def reverse : Seg P where
  source := seg.target
  target := seg.source

-- reversion of generalized directed vector is compatible with make process




-- double reverse a generalized directed segment gets back to itself
theorem double_rev_eq_self  : seg.reverse.reverse = seg := rfl

-- reversing the direction does not change the property that a point lies on the generalized directed segments.
theorem IsOnSeg_of_rev_of_IsOnSeg (a : P) (lieson : a LiesOnSeg seg) : a LiesOnSeg seg.reverse := sorry

-- reversing the direction does not change the nontriviality of a generalized directed segment.
theorem nontriv_of_rev_of_nontriv (nontriv : seg.target ≠ seg.source) : seg.reverse.target ≠ seg.reverse.source := sorry

-- reversing the direction does not change the length
theorem length_eq_length_of_rev : seg.length = seg.reverse.length := sorry

end Seg


section compatibility_with_coersion


variable {P: Type _} [EuclideanPlane P] (seg : Seg P) (seg : DSeg P)

-- reversing the direction of a generalized directed segment will negate the coersion to vectors
theorem Seg.neg_toVec_of_rev : seg.reverse.toVec = - seg.toVec := sorry


end compatibility_with_coersion




namespace Ray

variable {P: Type _} [EuclideanPlane P]  (ray : Ray P)


-- reverse the direction of a ray
def reverse : Ray P where
  source := ray.source
  direction := -ray.direction


theorem double_rev_eq_self : ray.reverse.reverse = ray := sorry

-- If a point lies on ray and its reversion, then it is the source

theorem eq_source_of_lies_on_and_lies_on_rev (a : P) (lieson : a LiesOnRay ray) (liesonrev : a LiesOnRay ray.reverse) : a = ray.source := by sorry

end Ray





end EuclidGeom