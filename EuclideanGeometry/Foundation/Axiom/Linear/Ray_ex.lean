import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section
namespace EuclidGeom

variable {P: Type _} [EuclideanPlane P]

section reverse

-- Given a ray, this function returns the ray with the same source but with reversed direction.
def Ray.reverse (ray : Ray P): Ray P where
  source := ray.source
  toDir := - ray.toDir

-- Given a segment, this function returns the reverse of the segment, that is the swap the source and the target of the segment.
def Seg.reverse (seg : Seg P): Seg P where
  source := seg.target
  target := seg.source

-- Given a segment, if it is nondegenerate, then its reverse segment is also nondegenerate.
theorem nd_of_rev_of_nd {seg : Seg P} (nd : seg.is_nd) : seg.reverse.is_nd := by  
  simp only [Seg.is_nd]
  push_neg
  symm
  apply nd

-- Given a nondegenerate segment, this function returns the reversed nondegenerate segment, that is to swap the source and the target of the segment.
def Seg_nd.reverse (seg_nd : Seg_nd P) : Seg_nd P := ⟨seg_nd.1.reverse, nd_of_rev_of_nd seg_nd.2⟩ 

-- Given a nondegenerate segment $segnd$, first viewing $segnd$ as a segment and then reverse is the same as first reversing $segnd$ and then view it as a segment.
theorem Seg_nd.rev_toSeg_eq_toSeg_rev (seg_nd : Seg_nd P) : seg_nd.1.reverse = seg_nd.reverse.1 := rfl

-- Given a ray, reversing it twice gives back to itself.
@[simp]
theorem Ray.rev_rev_eq_self (ray : Ray P) : ray.reverse.reverse = ray := by
  simp only [reverse, neg_neg]

-- Given a segment, reversing it twice gives back to itself.
@[simp]
theorem Seg.rev_rev_eq_self (seg : Seg P) : seg.reverse.reverse = seg := rfl

-- Given a degenerate segment, reversing it twice gives back to itself.
@[simp]
theorem Seg_nd.rev_rev_eq_self (seg_nd : Seg_nd P)  : seg_nd.reverse.reverse = seg_nd := rfl

-- Given a ray, the direction of the reversed ray is the negative of the direction of the ray.
theorem Ray.toDir_of_rev_eq_neg_toDir {ray : Ray P} : ray.reverse.toDir = - ray.toDir := rfl

-- Given a ray, the projective direction of the reversed ray is the negative of the projective direction of the ray.
theorem Ray.toProj_of_rev_eq_toProj {ray : Ray P} : ray.reverse.toProj = ray.toProj := by
  --@HeRunming: Simply imitate the proof of theorem "eq_toProj_of_smul" in Vector.lean
  -- `??? Why not use that toProj is the quotient of toDir` see the definition of toProj
  apply (Dir.eq_toProj_iff ray.reverse.toDir ray.toDir).mpr
  right
  rfl

-- Given a segment, the vector associated to the reverse of the reversed segment is the negative of the vector associated to the segment.
theorem Seg.toVec_of_rev_eq_neg_toVec (seg : Seg P) : seg.reverse.toVec = - seg.toVec := by
  simp only [reverse,toVec,neg_vec]

-- Given a nondegenerate segment, the nondegenerate vector associated to the reversed nondegenerate segment is the negative of the nondegenerate vector associated to the nondegenerate segment.
theorem Seg_nd.toVec_nd_of_rev_eq_neg_toVec_nd (seg_nd : Seg_nd P) : seg_nd.reverse.toVec_nd = - seg_nd.toVec_nd := by
  apply Subtype.eq
  apply Seg.toVec_of_rev_eq_neg_toVec

-- Given a nondegenerate segment, the direction of the reversed nondegenerate segment is the negative direction of the nondegenerate segment.
theorem Seg_nd.toDir_of_rev_eq_neg_toDir (seg_nd : Seg_nd P) : seg_nd.reverse.toDir = - seg_nd.toDir := by
-- `exists a one=line proof?`
  rw[toDir,toDir,←neg_normalize_eq_normalize_eq,Seg_nd.toVec_nd_of_rev_eq_neg_toVec_nd]

-- Given a nondegenerate segment, the projective direction of the reversed nondegenerate segment is the negative projective direction of the nondegenerate segment.
theorem Seg_nd.toProj_of_rev_eq_toProj (seg_nd : Seg_nd P) : seg_nd.reverse.toProj = seg_nd.toProj := by
  --`follows from teh previous lemma directly?`
  apply (Dir.eq_toProj_iff seg_nd.reverse.toDir seg_nd.toDir).mpr
  right
  rw[Seg_nd.toDir_of_rev_eq_neg_toDir]

-- Given a segment and a point, the point lies on the segment if and only if it lies on the reverse of the segment.
theorem Seg.lies_on_iff_lies_on_rev {A : P} {seg : Seg P} : A LiesOn seg ↔  A LiesOn seg.reverse := by
  unfold lies_on Carrier.carrier instCarrierSeg
  simp only [Set.setOf_mem_eq]
  constructor
  · intro h
    rcases h with ⟨t, ⟨ h1, ⟨ h2, h3 ⟩⟩⟩
    use 1-t
    constructor
    linarith
    constructor
    linarith
    simp only [reverse]; rw [← vec_add_vec target source A, h3, ← neg_vec target source, smul_neg];
    apply add_neg_eq_iff_eq_add.mpr
    rw [add_comm]
    exact Eq.symm smul_add_one_sub_smul  
  · intro h
    rcases h with ⟨t, ⟨ h1, ⟨ h2, h3 ⟩⟩⟩
    use 1-t
    constructor
    linarith
    constructor
    linarith
    simp only [reverse] at h3
    rw [← vec_add_vec source target A, h3, ← neg_vec source target, smul_neg];
    apply add_neg_eq_iff_eq_add.mpr
    rw [add_comm]
    exact Eq.symm smul_add_one_sub_smul 

-- Given a segment and a point, the point lies in the interior of the segment if and only if it lies in the interior of the reverse of the segment.
theorem Seg.lies_int_iff_lies_int_rev {A : P} {seg : Seg P} : A LiesInt seg ↔  A LiesInt seg.reverse := by sorry


-- Given a ray and a point, the point is equal to the source of the ray if and only if it lies on the ray and it lies on the reverse of the ray.
theorem Ray.eq_source_iff_lies_on_and_lies_on_rev {A : P} {ray : Ray P} : A = ray.source ↔ (A LiesOn ray) ∧ (A LiesOn ray.reverse) := by
  constructor
  intro h
  constructor
  use 0
  simp only [le_refl, zero_smul, true_and]
  rw[h,vec_same_eq_zero]
  use 0
  simp only [le_refl, Dir.toVec_neg_eq_neg_toVec, smul_neg, zero_smul, neg_zero, true_and,Ray.reverse]
  rw[h,vec_same_eq_zero]
  simp only [and_imp]
  rintro ⟨a,⟨anneg,h⟩⟩ ⟨b,⟨bnneg,h'⟩⟩
  simp only [Ray.reverse,Dir.toVec_neg_eq_neg_toVec, smul_neg,h] at h'
  rw[←add_zero a,← sub_self b,add_sub,sub_smul] at h'
  simp only [sub_eq_neg_self, mul_eq_zero] at h' 
  have h'': a+b=0:=by
    contrapose! h'
    apply smul_ne_zero
    exact h'
    apply Dir.toVec_ne_zero
  have:a=0:=by
    linarith
  rw[this] at h
  simp only [zero_smul] at h 
  rw[eq_iff_vec_eq_zero,h]

-- Given a ray and a point, if the point lies in the interior of the reverse ray, then it does not lie on the ray.
theorem Ray.not_lies_on_of_lies_int_rev {A : P} {ray : Ray P} (liesint : A LiesInt ray.reverse) : ¬ A LiesOn ray := by
  by_contra h
  rcases liesint with ⟨h',nsource⟩
  have: A LiesOn ray.reverse:=by
    apply h'
  have :A=ray.source:=by
    rw [Ray.eq_source_iff_lies_on_and_lies_on_rev]
    constructor
    exact h
    exact this
  trivial

-- Given a ray and a point, if the point lies on of the reverse ray, then it does not lie in the interior of the ray. 
theorem Ray.not_lies_int_of_lies_on_rev {A : P} {ray : Ray P} (liesint : A LiesOn ray.reverse) : ¬ A LiesInt ray := by
  by_contra h
  rw [← Ray.rev_rev_eq_self ray] at h
  have:¬A LiesOn ray.reverse:=by
    apply not_lies_on_of_lies_int_rev 
    exact h
  trivial


-- Given a nondegenerate segment and a point, the point lies on the segment if and only if it lies on the ray associated to the segment and it lies on the ray assoicated to the reverse of the segment.
-- need to be refined
theorem lies_on_iff_lies_on_toRay_and_rev_toRay {A : P} {seg_nd : Seg_nd P} : A LiesOn seg_nd.1 ↔ (A LiesOn seg_nd.toRay) ∧ (A LiesOn seg_nd.reverse.toRay) := by
  constructor
  intro liesonseg
  constructor
  apply Seg_nd.lies_on_toRay_of_lies_on
  trivial
  apply Seg_nd.lies_on_toRay_of_lies_on
  apply Seg.lies_on_iff_lies_on_rev.mp
  trivial
  rintro ⟨⟨a,anneg,h⟩,b,bnneg,h'⟩
  rw[←Seg_nd.toDir_eq_toRay_toDir] at h h'
  simp only [Seg_nd.toRay] at h h'
  rw[Seg_nd.toDir_of_rev_eq_neg_toDir,Dir.toVec_neg_eq_neg_toVec,smul_neg] at h'
  simp only [Seg_nd.reverse,Seg.reverse] at h'
  have asumbvec:(a+b)•seg_nd.toDir.toVec_nd.1=seg_nd.toVec_nd.1:=by
    simp only [Seg_nd.toVec_nd,Dir.toVec_nd]
    rw[add_smul,←h,←vec_add_vec seg_nd.1.source A seg_nd.1.target,←neg_vec seg_nd.1.target A,h',neg_neg]
  have asumbeqnorm:a+b=(Vec_nd.norm seg_nd.toVec_nd):=by
    rw [←Vec_nd.norm_smul_normalize_eq_self seg_nd.toVec_nd] at asumbvec
    apply eq_of_smul_Vec_nd_eq_smul_Vec_nd asumbvec
  use a*(Vec_nd.norm seg_nd.toVec_nd)⁻¹
  have :VEC seg_nd.1.source seg_nd.1.target=seg_nd.toVec_nd:=by
    rfl
  constructor
  apply mul_nonneg anneg
  simp only [ne_eq, inv_nonneg]
  linarith
  constructor
  rw[←mul_inv_cancel (Vec_nd.norm_ne_zero seg_nd.toVec_nd)]
  apply mul_le_mul
  linarith
  trivial
  simp only[inv_nonneg]
  linarith
  linarith
  rw[h,mul_smul,this,←Vec_nd.norm_smul_normalize_eq_self seg_nd.toVec_nd,smul_smul,smul_smul,mul_assoc,←norm_of_Vec_nd_eq_norm_of_Vec_nd_fst,inv_mul_cancel (Vec_nd.norm_ne_zero seg_nd.toVec_nd),mul_one]

-- `This theorem really concerns about the total order on a line`
theorem lies_on_pt_toDir_of_pt_lies_on_rev {A B : P} {ray : Ray P} (hA : A LiesOn ray) (hB : B LiesOn ray.reverse) : A LiesOn Ray.mk B ray.toDir := by
  rcases hA with ⟨a,anonneg,ha⟩
  rcases hB with ⟨b,bnonneg,hb⟩
  simp only [Dir.toVec,Ray.reverse,smul_neg] at hb
  use a+b
  constructor
  linarith
  simp only
  rw[add_smul,←vec_sub_vec ray.source,ha,hb,sub_neg_eq_add]

-- reversing the toDir does not change the length
theorem length_eq_length_of_rev (seg : Seg P) : seg.length = seg.reverse.length := by
  unfold Seg.length
  have h:Vec.norm seg.toVec=norm seg.toVec:=by
    rfl
  have h':Vec.norm seg.reverse.toVec=norm seg.reverse.toVec:=by
    rfl
  rw[←h,←h']
  rw[Seg.toVec_of_rev_eq_neg_toVec]
  have eq: (-Seg.toVec seg)=-(Seg.toVec seg):=by
    rfl
  rw[eq]
  simp only [Vec.norm]
  norm_num

end reverse

section extension

-- Define the extension ray from a nontrival segment
def Seg_nd.extension (seg_nd : Seg_nd P) : Ray P := (seg_nd.reverse.toRay).reverse

theorem extn_eq_rev_toray_rev (seg_nd : Seg_nd P) : seg_nd.extension = seg_nd.reverse.toRay.reverse :=by
  rfl

theorem eq_target_iff_lies_on_lies_on_extn {A : P} {seg_nd : Seg_nd P} : (A LiesOn seg_nd.1) ∧ (A LiesOn seg_nd.extension) ↔ A = seg_nd.1.target := by
-- sorry
  constructor
  rintro ⟨hyp1,hyp2⟩
  have h:seg_nd.1.target=seg_nd.extension.source :=by rfl
  rw[h]
  apply Ray.eq_source_iff_lies_on_and_lies_on_rev.mpr
  constructor
  exact hyp2
  have h':seg_nd.reverse.toRay=seg_nd.extension.reverse:=by
    simp only [Seg_nd.extension,Ray.reverse,neg_neg]
  rw[←h']
  apply Seg_nd.lies_on_toRay_of_lies_on
  apply Seg.lies_on_iff_lies_on_rev.mp
  apply hyp1
  intro hyp
  constructor
  use 1
  simp only [zero_le_one, le_refl, one_smul, true_and]
  rw[hyp]
  use 0
  simp only [le_refl, Dir.toVec_neg_eq_neg_toVec, smul_neg, zero_smul, neg_zero, true_and]
  rw[hyp]
  have :(Seg_nd.extension seg_nd).source=seg_nd.1.target:=by
    rfl
  rw[this]
  simp only [vec_same_eq_zero]

theorem target_lies_int_seg_source_pt_of_pt_lies_int_extn {A : P} {seg_nd : Seg_nd P} (liesint : A LiesInt seg_nd.extension) : seg_nd.1.target LiesInt SEG seg_nd.1.source A :=
by 
  rcases liesint with ⟨⟨a,anonneg,ha⟩,nonsource⟩
  have raysourcesegtarget:seg_nd.1.target=seg_nd.extension.1:=by
    rfl
  have sourcetargetA:VEC seg_nd.1.source seg_nd.1.target+VEC seg_nd.1.target A=VEC seg_nd.1.source A:=by
    rw[vec_add_vec]
  have vec_ndtovec:VEC seg_nd.1.source seg_nd.1.target=seg_nd.toVec_nd.1:=by
    rfl
  have apos:0<a:=by
    contrapose! nonsource
    have:a=0:=by linarith
    rw[this] at ha
    simp only [Dir.toVec_neg_eq_neg_toVec, smul_neg, zero_smul, neg_zero] at ha
    apply (eq_iff_vec_eq_zero _ _).mpr
    exact ha
  have raysourcesource:seg_nd.extension.source=seg_nd.1.target:=by
    rfl
  have seg_pos:0< Vec_nd.norm (Seg_nd.toVec_nd seg_nd):=by
    simp only [ne_eq, norm_of_Vec_nd_eq_norm_of_Vec_nd_fst,Vec.norm]
    apply norm_pos_iff.mpr (seg_nd.toVec_nd.2)
  have seg_nonzero:Vec_nd.norm (Seg_nd.toVec_nd seg_nd)≠0:=by linarith
  have aseg_pos:0<Vec_nd.norm (Seg_nd.toVec_nd seg_nd)+a:=by
    linarith
  have aseg_nonzero:Vec_nd.norm (Seg_nd.toVec_nd seg_nd)+a≠ 0:=by
    linarith
  have raydir:seg_nd.extension.toDir.toVec=seg_nd.toVec_nd.normalize.toVec:=by
    rw[Ray.toDir_of_rev_eq_neg_toDir,←Seg_nd.toDir_eq_toRay_toDir,Seg_nd.toDir_of_rev_eq_neg_toDir,neg_neg]
  constructor
  use (seg_nd.toVec_nd.norm)*(seg_nd.toVec_nd.norm+a)⁻¹
  constructor
  apply mul_nonneg
  linarith[seg_pos]
  norm_num
  rw[←norm_of_Vec_nd_eq_norm_of_Vec_nd_fst]
  linarith
  constructor
  rw[←mul_inv_cancel aseg_nonzero]
  apply mul_le_mul
  linarith
  linarith
  norm_num
  rw[← norm_of_Vec_nd_eq_norm_of_Vec_nd_fst]
  linarith
  linarith
  simp only [Seg.target]
  rw[←raysourcesegtarget] at ha
  rw[←sourcetargetA,ha,vec_ndtovec,←Vec_nd.norm_smul_normalize_eq_self (seg_nd.toVec_nd),←norm_of_Vec_nd_eq_norm_of_Vec_nd_fst,raydir]
  rw[←add_smul,← mul_smul,mul_assoc,inv_mul_cancel,mul_one]
  linarith
  constructor
  exact seg_nd.2
  rw[←raysourcesegtarget] at nonsource
  symm
  exact nonsource
end extension
end EuclidGeom