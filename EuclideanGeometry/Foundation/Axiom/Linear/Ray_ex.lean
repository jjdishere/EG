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
theorem nd_of_rev_of_nd {seg : Seg P} (nd : seg.is_nd) : seg.reverse.is_nd := by
-- sorry
  simp [Seg.is_nd]
  push_neg
  symm
  apply nd

def Seg_nd.reverse : Seg_nd P := ⟨seg_nd.1.reverse, nd_of_rev_of_nd seg_nd.2⟩ 

-- double reverse a ray gets back to itself
theorem Ray.rev_rev_eq_self : ray.reverse.reverse = ray := by
-- sorry
  simp [reverse]

-- double reverse a generalized directed segment gets back to itself
theorem Seg.rev_rev_eq_self  : seg.reverse.reverse = seg := rfl

theorem Seg_nd.rev_rev_eq_self  : seg_nd.reverse.reverse = seg_nd := rfl

theorem Seg_nd.rev_toSeg_eq_toSeg_rev : seg_nd.1.reverse = seg_nd.reverse.1 := rfl

-- reversing the toDir does not change the property that a point lies on the generalized directed segments.
theorem Seg.lies_on_rev_iff_lie_son {A : P} (lieson : A LiesOn seg) : A LiesOn seg.reverse := by
-- sorry
  unfold lies_on Carrier.carrier instCarrierSeg
  simp only [Set.setOf_mem_eq]
  rcases lieson with ⟨a,⟨h1,⟨h2,h3⟩⟩⟩
  use 1-a
  constructor
  linarith
  constructor
  linarith
  simp only [reverse]
  rw[sub_smul,sub_eq_add_neg]
  simp
  have h:-(a • VEC seg.target seg.source)=a • (-1) • VEC seg.target seg.source:=by
    rw[smul_algebra_smul_comm]
    rw[neg_smul]
    simp
  have h':VEC seg.target A=VEC seg.target seg.source+VEC seg.source A:=by
    rw[←neg_vec seg.source seg.target,add_comm,←sub_eq_add_neg,vec_sub_vec]
  rw[h,h',←neg_vec seg.source seg.target]
  simp
  exact h3
  
theorem eq_source_iff_lies_on_ray_lies_on_ray_rev {A : P} : A = ray.source ↔ (A LiesOn ray) ∧ (A LiesOn ray.reverse) := by
-- sorry
  constructor
  intro h
  constructor
  use 0
  simp
  rw[h,vec_same_eq_zero]
  use 0
  simp
  simp only [Ray.reverse]
  rw[h,vec_same_eq_zero]
  simp
  rintro ⟨a,⟨anneg,h⟩⟩ ⟨b,⟨bnneg,h'⟩⟩
  simp only [Ray.reverse] at h'
  simp at h'
  rw[h,←add_zero a,← sub_self b,add_sub,sub_smul] at h'
  simp at h'
  have h'': a+b=0:=by
    contrapose! h'
    constructor
    exact h'
    apply Dir.toVec_ne_zero
  have:a=0:=by
    linarith
  rw[this] at h
  simp at h
  rw[eq_iff_vec_eq_zero,h]

theorem not_lies_on_of_lies_int_rev {A : P} (liesint : A LiesInt ray.reverse) : ¬ A LiesOn ray := by
-- sorry
  by_contra h
  rcases liesint with ⟨h',nsource⟩
  have: A LiesOn ray.reverse:=by
    apply h'
  have :A=ray.source:=by
    rw[eq_source_iff_lies_on_ray_lies_on_ray_rev]
    constructor
    exact h
    exact this
  trivial

theorem not_lies_int_of_lies_on_rev {A : P} (liesint : A LiesOn ray.reverse) : ¬ A LiesInt ray :=by
--  sorry
  by_contra h
  rw[←Ray.rev_rev_eq_self ray] at h
  have:¬A LiesOn ray.reverse:=by
    apply not_lies_on_of_lies_int_rev 
    exact h
  trivial

-- A point lies on the directed segment if and only if it lies on the ray associated to the segment and the ray associated to the reverse of this segment.

theorem lies_on_iff_lies_on_toRay_and_rev_toRay {A : P} : A LiesOn seg_nd.1 ↔ (A LiesOn seg_nd.toRay) ∧ (A LiesOn seg_nd.reverse.toRay) := by
-- sorry
  constructor
  intro liesonseg
  constructor
  apply Seg_nd.lies_on_toRay_of_lies_on
  trivial
  apply Seg_nd.lies_on_toRay_of_lies_on
  apply Seg.lies_on_rev_iff_lie_son
  trivial
  rintro ⟨⟨a,anneg,h⟩,b,bnneg,h'⟩
  have: seg_nd.reverse.toRay.source=seg_nd.1.target:=by
    rfl
  rw[this] at h'
  have: seg_nd.toRay.source=seg_nd.1.source:=by
    rfl
  rw[this] at h
  use a*(Vec.norm (VEC seg_nd.1.source seg_nd.1.target))⁻¹
  constructor
  apply mul_nonneg anneg
  simp
  rw[Vec.norm_eq_abs_toComplex (VEC seg_nd.1.source seg_nd.1.target)]
  apply Real.sqrt_nonneg
  rw[h]
  constructor
  sorry
  rw[mul_smul]
  have h1:seg_nd.toDir.toVec - (Vec.norm (VEC seg_nd.1.source seg_nd.1.target))⁻¹ • VEC seg_nd.1.source seg_nd.1.target=0:=by
    sorry
  trivial


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