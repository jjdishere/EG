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

-- A point lies on the directed segment if and only if it lies on the ray associated to the segment and the ray associated to the reverse of this segment.
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

section extension

-- Define the extension ray from a nontrival segment
def Seg_nd.extension : Ray P := (seg_nd.reverse.toRay).reverse

theorem extn_eq_rev_toray_rev : seg_nd.extension = seg_nd.reverse.toRay.reverse := sorry

theorem eq_target_iff_lies_on_lies_on_extn {A : P} : (A LiesOn seg_nd.1) ∧ (A LiesOn seg_nd.extension) ↔ A = seg_nd.1.target := sorry

theorem target_lies_int_seg_source_pt_of_pt_lies_int_extn {A : P} (liesint : A LiesInt seg_nd.extension) : seg_nd.1.target LiesInt SEG seg_nd.1.source A := sorry

end extension

end EuclidGeom