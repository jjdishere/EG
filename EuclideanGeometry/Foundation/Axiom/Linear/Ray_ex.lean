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

theorem Ray.toDir_of_reverse_eq_neg_toDir : ray.reverse.toDir = - ray.toDir := rfl

theorem Ray.toProj_of_reverse_eq_toProj : ray.reverse.toProj = ray.toProj := sorry

theorem Seg.toVec_of_reverse_eq_neg_toVec : seg.reverse.toVec = - seg.toVec := by
-- sorry
  unfold toVec reverse
  simp
  rw[neg_vec]

theorem Seg_nd.toVec_nd_of_reverse_eq_neg_toVec_nd : seg_nd.reverse.toVec_nd = - seg_nd.toVec_nd := by
-- sorry
  apply Subtype.eq
  apply Seg.toVec_of_reverse_eq_neg_toVec
  -- simp

theorem Seg_nd.toDir_of_reverse_eq_neg_toDir : seg_nd.reverse.toDir = - seg_nd.toDir := by
-- sorry
  unfold toDir
  symm
  have :seg_nd.reverse.toVec_nd.1=(-1)•seg_nd.toVec_nd.1:=by
    rw[neg_smul,one_smul]
    rw[Seg_nd.toVec_nd_of_reverse_eq_neg_toVec_nd]
    rfl
  apply @neg_normalize_eq_normalize_smul_neg _ _ (-1)
  rw[this]
  simp
  simp

theorem Seg_nd.toProj_of_reverse_eq_toProj : seg_nd.reverse.toProj = seg_nd.toProj := by
-- sorry
  apply @eq_toProj_of_smul _ _ (-1)
  rw[neg_smul,one_smul]
  rw[Seg_nd.toVec_nd_of_reverse_eq_neg_toVec_nd]
  apply neg_eq_iff_eq_neg.mp
  rfl

-- reversing the toDir does not change the length
theorem length_eq_length_of_rev : seg.length = seg.reverse.length := by
-- sorry
  unfold Seg.length
  have h:Vec.norm seg.toVec=Vec.Norm.norm seg.toVec:=by
    rfl
  have h':Vec.norm seg.reverse.toVec=Vec.Norm.norm seg.reverse.toVec:=by
    rfl
  rw[←h,←h']
  rw[Seg.toVec_of_reverse_eq_neg_toVec]
  rw[Vec.norm_eq_abs_toComplex,Vec.norm_eq_abs_toComplex]
  have eq:Vec.toComplex (-Seg.toVec seg)=-Vec.toComplex (Seg.toVec seg):=by
    rfl
  rw[eq]
  norm_num

-- A point lies on the directed segment if and only if it lies on the ray associated to the segment and the ray associated to the reverse of this segment.
-- need to be refined
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
  unfold Dir.toVec Ray.toDir Seg_nd.toRay at h h'
  simp at h h'
  rw[Seg_nd.toDir_of_reverse_eq_neg_toDir] at h'
  have tria:(-Seg_nd.toDir seg_nd).1=(-1)•(Seg_nd.toDir seg_nd).1:=by
    rw[Dir.toVec_neg_eq_neg_toVec _]
    rw[neg_one_smul]
  unfold Dir.toVec at tria
  rw[tria] at h'
  simp only [Seg_nd.toDir] at h h'
  have trib:b • -1 • (Vec_nd.normalize (Seg_nd.toVec_nd seg_nd)).1=(-b)• (Vec_nd.normalize (Seg_nd.toVec_nd seg_nd)).1:=by
    simp
  unfold Dir.toVec at trib
  rw[trib] at h'
  set v:=(Vec_nd.normalize (Seg_nd.toVec_nd seg_nd)).1 with v_def
  unfold Dir.toVec at v_def
  simp only [Seg_nd.reverse,Seg.reverse] at h'
  rw[←v_def] at h h'
  have asumbv:(a+b)•v=VEC seg_nd.1.source seg_nd.1.target:=by
    rw[← vec_add_vec _ A _,←neg_vec seg_nd.1.target A,h,h',add_smul]
    simp
  have tri1:VEC seg_nd.1.source seg_nd.1.target=seg_nd.toVec_nd.1:=by
    rfl
  simp at asumbv
  rw[tri1,←Vec_nd.norm_smul_normalize_eq_self seg_nd.toVec_nd] at asumbv
  have tri2:(a+b-(Vec.norm seg_nd.toVec_nd))•(seg_nd.toDir).1=0:=by
    rw[sub_smul,asumbv]
    simp
  have asumb:a+b=(Vec.norm seg_nd.toVec_nd):=by
    have asumb:a+b-(Vec.norm seg_nd.toVec_nd)=0:=by
      rcases smul_eq_zero.mp tri2 with hyp1|hyp2
      exact hyp1
      exfalso
      apply Dir.toVec_ne_zero seg_nd.toDir
      assumption
    linarith
  
  have norm_pos_vec:0<Vec.norm seg_nd.toVec_nd:=by
    rw[Vec.norm_eq_abs_toComplex]
    unfold Complex.abs
    simp
    push_neg
    apply ne_zero_of_Vec_nd_toComplex
  have norm_nonzero:Vec.norm seg_nd.toVec_nd≠0:=by
    linarith
  have alenorm:a≤Vec.norm seg_nd.toVec_nd:=by
    linarith
  have tri3:1=Vec.norm seg_nd.toVec_nd*(Vec.norm seg_nd.toVec_nd)⁻¹:=by
    rw[mul_inv_cancel norm_nonzero]
  use a*(Vec.norm seg_nd.toVec_nd)⁻¹
  constructor
  apply mul_nonneg
  exact anneg
  simp
  linarith
  constructor
  rw[tri3]
  apply mul_le_mul
  exact alenorm
  trivial
  simp
  apply le_trans anneg
  exact alenorm
  apply le_trans anneg
  exact alenorm
  rw[h,mul_smul,tri1]
  nth_rw 2[←Vec_nd.norm_smul_normalize_eq_self]
  simp only [v_def]
  rw[smul_smul,smul_smul,mul_assoc,←smul_smul]
  rw[mul_comm] at tri3
  rw[←tri3]
  simp
  
end reverse

section extension

-- Define the extension ray from a nontrival segment
def Seg_nd.extension : Ray P := (seg_nd.reverse.toRay).reverse

theorem extn_eq_rev_toray_rev : seg_nd.extension = seg_nd.reverse.toRay.reverse := sorry

theorem eq_target_iff_lies_on_lies_on_extn {A : P} : (A LiesOn seg_nd.1) ∧ (A LiesOn seg_nd.extension) ↔ A = seg_nd.1.target := sorry

theorem target_lies_int_seg_source_pt_of_pt_lies_int_extn {A : P} (liesint : A LiesInt seg_nd.extension) : seg_nd.1.target LiesInt SEG seg_nd.1.source A := sorry

end extension

end EuclidGeom