import EuclideanGeometry.Foundation.Axiom.Ray


namespace EuclidGeom

namespace Seg 
variable {P: Type _} [EuclideanPlane P] (l : Seg P) 

-- source and targets are on generalized directed segments
theorem source_lies_on_seg : l.source LiesOnSeg l := by sorry

theorem target_lies_on_seg : l.source LiesOnSeg l := by sorry

-- If a point lies on a directed segemnt, then it lies on the Ray associated to the directed segment

theorem pt_on_toRay_of_pt_on_Seg (p : P) (l : Seg P) (lieson : p LiesOnSeg l) (nontriv : l.is_nontriv) : p LiesOnRay (l.toRay_of_nontriv nontriv) := sorry


-- definition of reversion of the direction of a generalized directed segment
def reverse : Seg P where
  source := l.target
  target := l.source


-- double reverse a generalized directed segment gets back to itself
theorem double_rev_eq_self  : l.reverse.reverse = l := rfl

-- reversing the direction does not change the property that a point lies on the generalized directed segments.
theorem IsOnSeg_of_rev_of_IsOnSeg (p : P) (lieson : p LiesOnSeg l) : p LiesOnSeg l.reverse := sorry

-- reversing the direction does not change the nontriviality of a generalized directed segment.
theorem nontriv_of_rev_of_nontriv (nontriv : l.is_nontriv) : l.reverse.is_nontriv := sorry

-- reversing the direction does not change the length
theorem length_eq_length_of_rev : l.length = l.reverse.length := sorry

end Seg


section compatibility_with_coersion


variable {P: Type _} [EuclideanPlane P] (l : Seg P)

-- reversing the direction of a generalized directed segment will negate the coersion to vectors
theorem Seg.neg_toVec_of_rev : l.reverse.toVec = - l.toVec := sorry


end compatibility_with_coersion




namespace Ray

variable {P: Type _} [EuclideanPlane P]  (l : Ray P)


-- reverse the direction of a ray
def reverse : Ray P where
  source := l.source
  direction := - l.direction


theorem double_rev_eq_self : l.reverse.reverse = l := sorry

-- If a point lies on ray and its reversion, then it is the source

theorem eq_source_of_lies_on_and_lies_on_rev (p : P) (lieson : p LiesOnRay l) (liesonrev : p LiesOnRay l.reverse) : p = l.source := by sorry

end Ray

namespace Seg

variable {P: Type _} [EuclideanPlane P]

def extension_ray (l : Seg P) (nontriv : l.is_nontriv) : Ray P := (l.reverse.toRay_of_nontriv (Ne.symm nontriv)).reverse


end Seg



end EuclidGeom