import EuclideanGeometry.Foundation.Axiom.Ray

noncomputable section

namespace EuclidGeom

namespace Seg 
variable {P: Type _} [EuclideanPlane P] (l : Seg P) 

-- source and targets are on generalized directed segments
theorem source_lies_on_seg : l.source LiesOn l := by sorry

theorem target_lies_on_seg : l.source LiesOn l := by sorry

-- If a point lies on a directed segemnt, then it lies on the Ray associated to the directed segment

theorem pt_on_toRay_of_pt_on_Seg (p : P) (l : Seg P) (lieson : p LiesOn l) (nontriv : l.is_nontriv) : p LiesOn (l.toRay_of_nontriv nontriv) := sorry


-- definition of reversion of the toDir of a generalized directed segment
def reverse : Seg P where
  source := l.target
  target := l.source


-- double reverse a generalized directed segment gets back to itself
theorem double_rev_eq_self  : l.reverse.reverse = l := rfl

-- reversing the toDir does not change the property that a point lies on the generalized directed segments.
theorem IsOnSeg_of_rev_of_IsOnSeg (p : P) (lieson : p LiesOn l) : p LiesOn l.reverse := sorry

-- reversing the toDir does not change the nontriviality of a generalized directed segment.
theorem nontriv_of_rev_of_nontriv (nontriv : l.is_nontriv) : l.reverse.is_nontriv := sorry

-- reversing the toDir does not change the length
theorem length_eq_length_of_rev : l.length = l.reverse.length := sorry

end Seg


section compatibility_with_coersion


variable {P: Type _} [EuclideanPlane P] (l : Seg P)

-- reversing the toDir of a generalized directed segment will negate the coersion to vectors
theorem Seg.neg_toVec_of_rev : l.reverse.toVec = - l.toVec := sorry


end compatibility_with_coersion




namespace Ray

variable {P: Type _} [EuclideanPlane P]  (l : Ray P)


-- reverse the toDir of a ray
def reverse : Ray P where
  source := l.source
  toDir := - l.toDir


theorem double_rev_eq_self : l.reverse.reverse = l := sorry

-- If a point lies on ray and its reversion, then it is the source

theorem eq_source_of_lies_on_and_lies_on_rev (p : P) (lieson : p LiesOn l) (liesonrev : p LiesOn l.reverse) : p = l.source := by sorry

end Ray

namespace Seg

variable {P: Type _} [EuclideanPlane P]

-- Define the extension ray from a nontrival segment

def extension_ray_of_nontriv (seg : Seg P) (nontriv : seg.is_nontriv) : Ray P := (seg.reverse.toRay_of_nontriv (Ne.symm nontriv)).reverse

-- A point lies on the directed segment if and only if it lies on the ray associated to the segment and the ray associated to the reverse of this segment.

def lieson_iff_lieson_both_ray_of_nontriv_seg (p : P) (seg : Seg P) (nontriv : seg.is_nontriv) : (p LiesOn seg) ↔ (p LiesOn (seg.toRay_of_nontriv nontriv)) ∧ (p LiesOn (seg.reverse.toRay_of_nontriv (Ne.symm nontriv))) := by sorry

end Seg



end EuclidGeom