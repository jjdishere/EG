import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section
namespace EuclidGeom

variable {P: Type _} [EuclideanPlane P] (seg : Seg P) (seg_nd : Seg_nd P) (ray : Ray P)

-- source and targets are on generalized directed segments
theorem source_lies_on_seg : seg.source LiesOn seg := by sorry

theorem target_lies_on_seg : seg.source LiesOn seg := by sorry

-- If a point lies on a directed segemnt, then it lies on the Ray associated to the directed segment

theorem pt_on_toRay_of_pt_on_Seg {p : P} {seg_nd : Seg_nd P} (lieson : p LiesOn seg_nd) : p LiesOn (seg_nd.toRay) := sorry

section reverse

section seg

-- definition of reversion of the toDir of a generalized directed segment
def Seg.reverse : Seg P where
  source := seg.target
  target := seg.source

-- reversing the toDir does not change the nontriviality of a generalized directed segment.
theorem nd_of_rev_of_nd {seg : Seg P} (nd : seg.is_nd) : seg.reverse.is_nd := sorry

def Seg_nd.reverse : Seg_nd P := ⟨seg_nd.1.reverse, nd_of_rev_of_nd seg_nd.2⟩ 

-- double reverse a generalized directed segment gets back to itself
theorem Seg.double_rev_eq_self  : seg.reverse.reverse = seg := rfl

theorem Seg_nd.double_rev_eq_self  : seg_nd.reverse.reverse = seg_nd := rfl

-- reversing the toDir does not change the property that a point lies on the generalized directed segments.
theorem IsOnSeg_of_rev_of_IsOnSeg {p : P} (lieson : p LiesOn seg) : p LiesOn seg.reverse := sorry

-- reversing the toDir does not change the length
theorem length_eq_length_of_rev : seg.length = seg.reverse.length := sorry

section compatibility_with_coersion

-- reversing the toDir of a generalized directed segment will negate the coersion to vectors
theorem neg_toVec_of_rev : seg.reverse.toVec = - seg.toVec := sorry

theorem rev_of_toseg_eq_toseg_rev : seg_nd.reverse.1 = seg_nd.1.reverse := rfl 

end compatibility_with_coersion

end seg

section ray
-- reverse the toDir of a ray
def Ray.reverse : Ray P where
  source := ray.source
  toDir := - ray.toDir


theorem double_rev_eq_self : ray.reverse.reverse = ray := sorry

-- If a point lies on ray and its reversion, then it is the source

theorem eq_source_of_lies_on_and_lies_on_rev {p : P} (lieson : p LiesOn ray) (liesonrev : p LiesOn ray.reverse) : p = ray.source := by sorry

end ray

section seg

variable {P: Type _} [EuclideanPlane P]

-- Define the extension ray from a nontrival segment

def extension_ray_of_seg_nd (seg_nd : Seg_nd P) : Ray P := (seg_nd.reverse.toRay).reverse

-- A point lies on the directed segment if and only if it lies on the ray associated to the segment and the ray associated to the reverse of this segment.

def lieson_iff_lieson_both_ray_of_nontriv_seg {p : P} (seg_nd : Seg_nd P) : (p LiesOn seg_nd) ↔ (p LiesOn seg_nd.toRay) ∧ (p LiesOn seg_nd.reverse.toRay) := by sorry

end seg

end reverse

end EuclidGeom