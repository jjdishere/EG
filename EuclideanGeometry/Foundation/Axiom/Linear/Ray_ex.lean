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

-- Given a ray, the source of the reversed ray is the source of the ray.
theorem Ray.source_of_rev_eq_source {ray : Ray P} : ray.reverse.source = ray.source := rfl

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

theorem Ray.toVec_of_rev_eq_neg_toVec {ray : Ray P} : ray.reverse.toDir.toVec = - ray.toDir.toVec := rfl

-- Given a ray, the projective direction of the reversed ray is the negative of the projective direction of the ray.
theorem Ray.toProj_of_rev_eq_toProj {ray : Ray P} : ray.reverse.toProj = ray.toProj := by
  --@HeRunming: Simply imitate the proof of theorem "eq_toProj_of_smul" in Vector.lean
  -- `??? Why not use that toProj is the quotient of toDir` see the definition of toProj
  apply (Dir.eq_toProj_iff _ _).mpr
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

theorem Ray.source_lies_on_rev (ray : Ray P) : ray.source LiesOn ray.reverse := by sorry

theorem Seg.target_lies_on_rev (seg : Seg P) : seg.target LiesOn seg.reverse := by sorry

theorem Seg.source_lies_on_rev (seg : Seg P) : seg.source LiesOn seg.reverse := by sorry

-- Given a segment and a point, the point lies on the segment if and only if it lies on the reverse of the segment.
theorem Seg.lies_on_iff_lies_on_rev {A : P} {seg : Seg P} : A LiesOn seg ↔ A LiesOn seg.reverse := by
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
theorem Seg.lies_int_iff_lies_int_rev {A : P} {seg : Seg P} : A LiesInt seg ↔  A LiesInt seg.reverse := by 
  constructor
  rintro ⟨ha,⟨nonsource,nontarget⟩⟩
  exact ⟨Seg.lies_on_iff_lies_on_rev.mp ha,⟨nontarget,nonsource⟩⟩
  rintro ⟨ha,⟨nonrevsource,nonrevtarget⟩⟩
  exact ⟨Seg.lies_on_iff_lies_on_rev.mpr ha,⟨nonrevtarget,nonrevsource⟩⟩

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

-- Given two rays $ray_1$ and $ray_2$ with same direction, if the source of $ray_1$ lies on $ray_2$, then the source of $ray_2$ lies on the reverse of $ray_1$

theorem lies_on_iff_lies_on_rev_of_same_todir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = ray₂.toDir) : ray₁.source LiesOn ray₂ ↔ ray₂.source LiesOn ray₁.reverse := sorry


-- Given two rays $ray_1$ and $ray_2$ with same direction, if the source of $ray_1$ lies int $ray_2$, then the source of $ray_2$ lies int the reverse of $ray_1$

theorem lies_int_iff_lies_int_rev_of_same_todir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = ray₂.toDir) : ray₁.source LiesInt ray₂ ↔ ray₂.source LiesInt ray₁.reverse := sorry

-- Given two rays $ray_1$ and $ray_2$ with opposite direction, if the source of $ray_1$ lies on the reverse of $ray_2$, then the source of $ray_2$ lies on the reverse of $ray_1$

theorem lies_on_rev_iff_lies_on_rev_of_neg_todir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = - ray₂.toDir) : ray₁.source LiesOn ray₂.reverse ↔ ray₂.source LiesOn ray₁.reverse := sorry

-- Given two rays $ray_1$ and $ray_2$ with opposite direction, if the source of $ray_1$ lies int the reverse of $ray_2$, then the source of $ray_2$ lies int the reverse of $ray_1$

theorem lies_int_rev_iff_lies_int_rev_of_neg_todir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = - ray₂.toDir) : ray₁.source LiesInt ray₂.reverse ↔ ray₂.source LiesInt ray₁.reverse := sorry

-- Given two rays $ray_1$ and $ray_2$ with opposite direction, if the source of $ray_1$ lies on $ray_2$, then the source of $ray_2$ lies on $ray_1$

theorem lies_on_iff_lies_on_of_neg_todir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = - ray₂.toDir) : ray₁.source LiesOn ray₂ ↔ ray₂.source LiesOn ray₁ := sorry

-- Given two rays $ray_1$ and $ray_2$ with opposite direction, if the source of $ray_1$ lies int $ray_2$, then the source of $ray_2$ lies int $ray_1$

theorem lies_int_iff_lies_int_of_neg_todir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = - ray₂.toDir) : ray₁.source LiesInt ray₂ ↔ ray₂.source LiesInt ray₁ := sorry

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

theorem exist_real_vec_eq_smul_of_lies_on_or_rev {A : P} {ray : Ray P} (h : A LiesOn ray ∨ A LiesOn ray.reverse) : ∃ t : ℝ, VEC ray.source A = t • ray.2.1 := by
  rcases h with ⟨t, _, eq⟩ | ⟨t, _, eq⟩
  · use t, eq
  · use - t
    rw [Dir.toVec_neg_eq_neg_toVec, smul_neg, ← neg_smul] at eq
    exact eq

theorem ray_toProj_eq_mk_pt_pt_toProj {A B : P} {ray : Ray P} (h : B ≠ A) (ha : A LiesOn ray ∨ A LiesOn ray.reverse) (hb : B LiesOn ray ∨ B LiesOn ray.reverse) : ray.toProj = (RAY A B h).toProj := by
  rcases exist_real_vec_eq_smul_of_lies_on_or_rev ha with ⟨ta, eqa⟩
  rcases exist_real_vec_eq_smul_of_lies_on_or_rev hb with ⟨tb, eqb⟩
  have heq : VEC A B = (tb - ta) • ray.2.1 := by rw [← vec_sub_vec _ A B, eqa, eqb, sub_smul]
  calc
    _ = ray.2.toVec_nd.toProj := congrArg Dir.toProj (Dir.dir_toVec_nd_normalize_eq_self ray.2).symm
    _ = _ := eq_toProj_of_smul ray.2.toVec_nd ⟨VEC A B, (vsub_ne_zero.mpr h)⟩ heq

theorem Ray.in_carrier_iff_lies_on {p : P} {r : Ray P} : p ∈ r.carrier ↔ p LiesOn r := by
  rfl

theorem pt_lies_on_ray_iff_vec_same_dir {p : P} {r : Ray P} : p LiesOn r ↔ ∃t : ℝ, (t ≥ 0) ∧ VEC r.source p = t • r.toDir.toVec := by
  rw [← Ray.in_carrier_iff_lies_on, Ray.carrier, Set.mem_setOf, Ray.IsOn]

theorem pt_lies_on_ray_rev_iff_vec_opposite_dir {p : P} {r : Ray P} : p LiesOn r.reverse ↔ ∃t : ℝ, (t ≤ 0) ∧ VEC r.source p = t • r.toDir.toVec := by
  rw [pt_lies_on_ray_iff_vec_same_dir]
  constructor
  · rintro ⟨u, ⟨_, h⟩⟩
    use -u
    rw [Ray.toVec_of_rev_eq_neg_toVec, Ray.source_of_rev_eq_source] at h
    constructor
    · linarith
    · simp only [h, smul_neg, Complex.real_smul, neg_smul]
  · rintro ⟨u, ⟨_, h⟩⟩
    use -u
    rw [Ray.toVec_of_rev_eq_neg_toVec, Ray.source_of_rev_eq_source]
    constructor
    · linarith
    · simp only [h, Complex.real_smul, smul_neg, neg_smul, neg_neg]

-- A point `p` lies on the line determined by a ray `r` if and only if the vector `VEC r.source p` is parallel to the direction of `r`.
theorem pt_lies_on_line_from_ray_iff_vec_parallel {p : P} {r : Ray P} : (p LiesOn r ∨ p LiesOn r.reverse) ↔ ∃t : ℝ, VEC r.source p = t • r.toDir.toVec := by
  constructor
  · rintro (h | h)
    · rcases pt_lies_on_ray_iff_vec_same_dir.mp h with ⟨t, ⟨_, _⟩⟩
      use t
    · rcases pt_lies_on_ray_rev_iff_vec_opposite_dir.mp h with ⟨t, ⟨_, _⟩⟩
      use t
  · rintro ⟨t, h⟩
    by_cases g : t ≥ 0
    · left
      apply pt_lies_on_ray_iff_vec_same_dir.mpr
      use t
    · right
      apply pt_lies_on_ray_rev_iff_vec_opposite_dir.mpr
      use t
      exact ⟨le_of_lt (lt_of_not_ge g), h⟩

theorem dir_parallel_of_same_proj {x y : Ray P} (h : x.toProj = y.toProj) : ∃t : ℝ, y.toDir.toVec = t • x.toDir.toVec := by
  rcases (Dir.eq_toProj_iff _ _).mp h with xy | xy
  · use 1
    rw [one_smul, xy]
  · use -1
    rw [xy, Dir.toVec_neg_eq_neg_toVec, smul_neg, neg_smul, one_smul, neg_neg]

end reverse

section extension

-- Define the extension ray from a nontrival segment
def Seg_nd.extension (seg_nd : Seg_nd P) : Ray P := (seg_nd.reverse.toRay).reverse

theorem extn_eq_rev_toray_rev (seg_nd : Seg_nd P) : seg_nd.extension = seg_nd.reverse.toRay.reverse := rfl

theorem Seg_nd.extension_toDir (seg_nd : Seg_nd P) : seg_nd.extension.toDir = seg_nd.toRay.toDir := by
  rw [extension, Ray.toDir_of_rev_eq_neg_toDir]
  exact neg_eq_iff_eq_neg.mpr seg_nd.toDir_of_rev_eq_neg_toDir

theorem eq_target_iff_lies_on_lies_on_extn {A : P} {seg_nd : Seg_nd P} : (A LiesOn seg_nd.1) ∧ (A LiesOn seg_nd.extension) ↔ A = seg_nd.1.target := by
  constructor
  rintro ⟨hyp1,hyp2⟩
  have h:seg_nd.1.target=seg_nd.extension.source :=by rfl
  rw[h]
  apply Ray.eq_source_iff_lies_on_and_lies_on_rev.mpr
  constructor
  exact hyp2
  simp only[Seg_nd.extension,Ray.reverse,neg_neg]
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
  simp only [Seg_nd.extension,Ray.reverse,Seg_nd.toRay,Seg_nd.reverse,Seg.reverse,vec_same_eq_zero]

theorem target_lies_int_seg_source_pt_of_pt_lies_int_extn {A : P} {seg_nd : Seg_nd P} (liesint : A LiesInt seg_nd.extension) : seg_nd.1.target LiesInt SEG seg_nd.1.source A := by 
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

theorem lies_on_seg_nd_or_extension_of_lies_on_toRay {seg_nd : Seg_nd P} {A : P} 
    (h : A LiesOn seg_nd.toRay) : A LiesOn seg_nd.1 ∨ A LiesOn seg_nd.extension := by
  rcases h with ⟨t, tpos, eq⟩
  let v : Vec_nd := ⟨VEC seg_nd.1.1 seg_nd.1.2, (ne_iff_vec_ne_zero _ _).mp seg_nd.2⟩
  by_cases h : t > ‖v.1‖
  · refine' Or.inr ⟨t - ‖v.1‖, sub_nonneg.mpr (le_of_lt h), _⟩
    rw [seg_nd.extension_toDir, sub_smul, ← eq]
    refine' eq_sub_of_add_eq (add_eq_of_eq_sub' _)
    rw [vec_sub_vec']
    exact v.norm_smul_normalize_eq_self
  · have eq : VEC seg_nd.1.1 A = t * v.normalize.1 := eq
    exact Or.inl ⟨t * ‖v.1‖⁻¹, mul_nonneg tpos (inv_nonneg.mpr (norm_nonneg v.1)), 
      (mul_inv_le_iff (norm_pos_iff.2 v.2)).mpr (by rw [mul_one]; exact not_lt.mp h),
      by simpa only [eq, Vec_nd.normalize, ne_eq, Vec.norm, Complex.real_smul, Complex.ofReal_inv,
      Complex.norm_eq_abs, Complex.ofReal_mul] using by ring⟩

end extension
end EuclidGeom