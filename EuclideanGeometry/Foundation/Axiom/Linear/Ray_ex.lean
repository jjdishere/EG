import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section
namespace EuclidGeom

variable {P: Type _} [EuclideanPlane P] (seg : Seg P) (seg_nd : Seg_nd P) (ray : Ray P) 

section reverse

-- reverse the toDir of a ray
def Ray.reverse : Ray P where
  source := ray.source
  toDir := - ray.toDir

-- definition of reversion of the toDir of a generalized directed segment
def Seg.reverse (seg : Seg P): Seg P where
  source := seg.target
  target := seg.source

-- reversing the toDir does not change the nontriviality of a generalized directed segment.
theorem nd_of_rev_of_nd {seg : Seg P} (nd : seg.is_nd) : seg.reverse.is_nd := sorry

def Seg_nd.reverse : Seg_nd P := ⟨seg_nd.1.reverse, nd_of_rev_of_nd seg_nd.2⟩ 

-- double reverse a ray gets back to itself
theorem Ray.rev_rev_eq_self : ray.reverse.reverse = ray := sorry

-- double reverse a generalized directed segment gets back to itself
theorem Seg.rev_rev_eq_self  : seg.reverse.reverse = seg := rfl

theorem Seg_nd.rev_rev_eq_self  : seg_nd.reverse.reverse = seg_nd := rfl

theorem Seg_nd.rev_toSeg_eq_toSeg_rev : seg_nd.1.reverse = seg_nd.reverse.1 := rfl

-- reversing the toDir does not change the property that a point lies on the generalized directed segments.
theorem Seg.lies_on_rev_iff_lie_son {A : P} (lieson : A LiesOn seg) : A LiesOn seg.reverse := sorry

theorem eq_source_iff_lies_on_ray_lies_on_ray_rev {A : P} : A = ray.source ↔ (A LiesOn ray) ∧ (A LiesOn ray.reverse) := sorry

theorem not_lies_on_of_lies_int_rev {A : P} (liesint : A LiesInt ray.reverse) : ¬ A LiesOn ray := sorry

theorem not_lies_int_of_lies_on_rev {A : P} (liesint : A LiesOn ray.reverse) : ¬ A LiesInt ray := sorry

theorem lies_on_iff_lies_on_toRay_and_rev_toRay {A : P} : A LiesOn seg_nd.1 ↔ (A LiesOn seg_nd.toRay) ∧ (A LiesOn seg_nd.reverse.toRay) := sorry

theorem Ray.toDir_of_reverse_eq_neg_toDir : ray.reverse.toDir = - ray.toDir := rfl

theorem Ray.toProj_of_reverse_eq_toProj : ray.reverse.toProj = ray.toProj := sorry

theorem Seg.toVec_of_reverse_eq_neg_toVec : seg.reverse.toVec = - seg.toVec := sorry

theorem Seg_nd.toVec_nd_of_reverse_eq_neg_toVec_nd : seg_nd.reverse.toVec_nd = - seg_nd.toVec_nd := sorry

theorem Seg_nd.toDir_of_reverse_eq_neg_toDir : seg_nd.reverse.toDir = - seg_nd.toDir := sorry

theorem Seg_nd.toProj_of_reverse_eq_toProj : seg_nd.reverse.toProj = seg_nd.toProj := sorry

-- reversing the toDir does not change the length
theorem length_eq_length_of_rev : seg.length = seg.reverse.length := sorry

end reverse

section ray
-- If a point lies on ray and its reversion, then it is the source

theorem eq_source_of_lies_on_and_lies_on_rev {p : P} (lieson : p LiesOn ray) (liesonrev : p LiesOn ray.reverse) : p = ray.source := by sorry

end ray

section seg

variable {P: Type _} [EuclideanPlane P]

-- Define the extension ray from a nontrival segment

def extension_ray_of_seg_nd (seg_nd : Seg_nd P) : Ray P := (seg_nd.reverse.toRay).reverse

-- A point lies on the directed segment if and only if it lies on the ray associated to the segment and the ray associated to the reverse of this segment.

def lieson_iff_lieson_both_ray_of_nontriv_seg {p : P} (seg_nd : Seg_nd P) : (p LiesOn seg_nd.1) ↔ (p LiesOn seg_nd.toRay) ∧ (p LiesOn seg_nd.reverse.toRay) := by sorry

end seg

end EuclidGeom