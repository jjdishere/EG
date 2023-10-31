import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section
namespace EuclidGeom

variable {P: Type _} [EuclideanPlane P]

section MoreCoercionCompatibility

-- More theorem of this flavor, please formulate them on your own, following the instructions.  `But be careful that we introduced seg₁ and seg₂ using {}, this is because we want the computer to infer what they are; same applies to the point A.`

/- Given two segments $seg_1$ and $seg_2$, if the source and the target of the $seg_1$ both lie on $seg_2$, then every point of $seg_1$ lies on $seg_2$. -/
theorem every_pt_lies_on_seg_of_source_and_target_lies_on_seg {seg₁ seg₂ : Seg P} (h₁ : seg₁.source LiesOn seg₂) (h₂ : seg₁.target LiesOn seg₂) {A : P} (ha : A LiesOn seg₁) : (A LiesOn seg₂) :=by
  rcases h₁ with ⟨x,xnonneg,xle1,hx⟩
  rcases h₂ with ⟨y,ynonneg,yle1,hy⟩
  rcases ha with ⟨t,tnonneg,tleone,ht⟩
  rw[←vec_add_vec seg₁.source seg₂.source,←vec_add_vec seg₁.source seg₂.source seg₁.target,←neg_vec,hx,hy,neg_add_eq_iff_eq_add,←neg_smul,smul_add,smul_smul,smul_smul,←add_smul,←add_smul,←add_assoc,mul_neg,←sub_eq_add_neg,←one_mul x,←mul_assoc,←sub_mul,mul_one] at ht
  use ( (1- t) * x + t * y)
  constructor
  apply add_nonneg
  apply mul_nonneg
  linarith
  linarith
  apply mul_nonneg tnonneg ynonneg
  constructor
  nth_rw 2[←sub_add_cancel 1 t,←mul_one (1-t)]
  nth_rw 4[←mul_one t]
  apply add_le_add
  apply mul_le_mul _ xle1 xnonneg
  linarith
  simp only [le_refl]
  apply mul_le_mul _ yle1 ynonneg tnonneg
  simp only [le_refl]
  rw [ht]
  
/- Given two segments $seg_1$ and $seg_2$, if the source and the target of $seg_1$ both lie in the interior of $seg_2$, and if $A$ is a point on $seg_1$, then $A$ lies in the interior of $seg_2$. -/
theorem every_pt_lies_int_seg_of_source_and_target_lies_int_seg {seg₁ seg₂ : Seg P} (h₁ : seg₁.source LiesInt seg₂) (h₂ : seg₁.target LiesInt seg₂) {A : P} (ha : A LiesOn seg₁) : A LiesInt seg₂ := by
  rw[Seg.lies_int_iff]
  constructor
  apply ((Seg.lies_int_iff seg₁.source).mp h₁).1
  rw[Seg.lies_int_iff] at h₁ h₂
  rcases h₁ with ⟨ _ ,x,xpos,xlt1,hx⟩
  rcases h₂ with ⟨ _ ,y,ypos,ylt1,hy⟩
  rcases ha with ⟨t,tnonneg,tle1,ht⟩
  use ( (1- t) * x + t * y)
  by_cases 0=t
  constructor
  simp only [←h, sub_zero, one_mul, zero_mul, add_zero]
  exact xpos
  constructor
  simp only [←h, sub_zero, one_mul, zero_mul, add_zero]
  exact xlt1
  rw[←h,zero_smul,←eq_iff_vec_eq_zero] at ht
  simp only [← h, sub_zero, one_mul, zero_mul, add_zero,ht,hx]
  constructor
  apply lt_of_lt_of_le (mul_pos (lt_of_le_of_ne tnonneg h) ypos)
  simp only [le_add_iff_nonneg_left, gt_iff_lt, sub_pos]
  apply mul_nonneg
  linarith
  linarith
  constructor
  have: (1-t)*x+t*y<(1-t)*x+t:=by
    simp only [add_lt_add_iff_left, gt_iff_lt]
    nth_rw 2[←mul_one t]
    apply mul_lt_mul_of_pos_left ylt1 (lt_of_le_of_ne tnonneg h)
  apply lt_of_lt_of_le this
  have :1=1-t+t:=by norm_num
  nth_rw 2 [this]
  apply add_le_add
  nth_rw 2[←mul_one (1-t)]
  apply mul_le_mul
  linarith
  linarith
  linarith
  linarith
  linarith
  rw[←vec_add_vec seg₂.1 seg₁.1 A,ht,←vec_sub_vec seg₂.1 seg₁.1 seg₁.2,hy,hx,←sub_smul,smul_smul,←add_smul,←sub_eq_zero,←sub_smul,smul_eq_zero]
  left
  ring

/- Given two segments $seg_1$ and $seg_2$, if the source and the target of $seg_1$ both lie on $seg_2$, and if $A$ is a point in the interior of $seg_1$, then $A$ lies in the interior of $seg_2$. -/
theorem every_int_pt_lies_int_seg_of_source_and_target_lies_on_seg {seg₁ seg₂ : Seg P} (h₁ : seg₁.source LiesOn seg₂) (h₂ : seg₁.target LiesOn seg₂) {A : P} (ha : A LiesInt seg₁) : A LiesInt seg₂ := by
  apply (Seg.lies_int_iff A).mpr
  rcases h₁ with ⟨x,xnonneg,xle1,hx⟩
  rcases h₂ with ⟨y,ynonneg,yle1,hy⟩
  rcases (Seg.lies_int_iff A).mp ha with ⟨nd,t,tpos,tlt1,ht⟩
  constructor
  rw[Seg.is_nd,ne_iff_vec_ne_zero]
  contrapose! nd
  rw[nd,smul_zero,←eq_iff_vec_eq_zero] at hx hy
  rw[Seg.is_nd,not_not,eq_iff_vec_eq_zero,hx,hy,vec_same_eq_zero]
  rw[Seg.toVec,←vec_sub_vec seg₂.1,← vec_sub_vec seg₂.1 seg₁.1 seg₁.2,sub_eq_iff_eq_add,hx,hy,←sub_smul,smul_smul,←add_smul] at ht
  use ( (1- t) * x + t * y)
  have ynex:y≠x:= by
    contrapose! nd
    rw[Seg.is_nd,not_not,eq_iff_vec_eq_zero,←vec_sub_vec seg₂.1,hx,hy,←sub_smul,nd,sub_self,zero_smul]
  constructor
  by_cases 0=x
  rw[←h,mul_zero,zero_add]
  apply mul_pos
  exact tpos
  apply lt_of_le_of_ne
  exact ynonneg
  rw[h]
  symm
  exact ynex
  have :0<(1-t)*x:=by
    apply mul_pos
    linarith
    apply lt_of_le_of_ne xnonneg h
  apply lt_of_lt_of_le this
  simp only [le_add_iff_nonneg_right, gt_iff_lt]
  apply mul_nonneg
  linarith
  linarith
  constructor
  by_cases 1=x
  simp only [←h,mul_one,sub_add,sub_lt_iff_lt_add,lt_add_iff_pos_right, sub_pos, gt_iff_lt]
  nth_rw 2[←mul_one t]
  apply mul_lt_mul_of_pos_left
  apply lt_of_le_of_ne
  exact yle1
  rw[h]
  exact ynex
  exact tpos
  have :(1-t)*x+t*y<(1-t)+t*y:=by
    simp only [add_lt_add_iff_right, gt_iff_lt, sub_pos]
    nth_rw 2 [← mul_one (1-t)]
    apply mul_lt_mul_of_pos_left
    apply lt_of_le_of_ne xle1
    symm
    exact h
    linarith
  apply lt_of_lt_of_le this
  rw[sub_add,tsub_le_iff_right, le_add_iff_nonneg_right, sub_nonneg,←mul_one t,mul_assoc,one_mul]
  apply mul_le_mul _ yle1 ynonneg
  linarith
  linarith
  rw[ht,←sub_eq_zero,Seg.toVec,←sub_smul,smul_eq_zero]
  left
  ring

/- Given a segment and a ray, if the source and the target of the segment both lie on the ray, and if $A$ is a point on the segment, then $A$ lies on the ray. -/
theorem every_pt_lies_on_ray_of_source_and_target_lies_on_ray {seg : Seg P} {ray : Ray P} (h₁ : seg.source LiesOn ray) (h₂: seg.target LiesOn ray) {A : P} (ha : A LiesOn seg) : A LiesOn ray :=by
  rcases h₁ with ⟨x,xnonneg,hx⟩
  rcases h₂ with ⟨y,ynonneg,hy⟩
  rcases ha with ⟨t,tnonneg,tleone,ht⟩
  rw[←vec_add_vec seg.source ray.source,←vec_add_vec seg.source ray.source seg.target,←neg_vec,hx,hy,neg_add_eq_iff_eq_add,←neg_smul,smul_add,smul_smul,smul_smul,←add_smul,←add_smul,←add_assoc,mul_neg,←sub_eq_add_neg,←one_mul x,←mul_assoc,←sub_mul,mul_one] at ht
  use ( (1- t) * x + t * y)
  constructor
  apply add_nonneg
  apply mul_nonneg
  linarith
  linarith
  apply mul_nonneg
  linarith
  linarith
  rw[ht]

/- Given a segment and a ray, if the source and the target of the segment both lie in the interior of the ray, and if $A$ is a point on the segment, then $A$ lies in the interior of the ray.-/
theorem every_pt_lies_int_ray_of_source_and_target_lies_int_ray {seg : Seg P} {ray : Ray P}(h₁ : seg.source LiesInt ray) (h₂ : seg.target LiesInt ray) {A : P} (ha : A LiesOn seg) : A LiesInt ray := by
  rcases ((Ray.lies_int_iff seg.source).mp h₁) with ⟨x,xpos,hx⟩
  rcases ((Ray.lies_int_iff seg.target).mp h₂) with ⟨y,ypos,hy⟩
  apply (Ray.lies_int_iff A).mpr
  rcases ha with ⟨t,tnonneg,tle1,ht⟩
  rw[←vec_sub_vec ray.source,←vec_sub_vec ray.source seg.source seg.target,hx,hy,sub_eq_iff_eq_add,←sub_smul,smul_smul,←add_smul,mul_sub] at ht 
  use (t*y+(1-t)*x)
  constructor
  by_cases 0=t
  rw[←h]
  linarith
  apply lt_of_lt_of_le (mul_pos (lt_of_le_of_ne tnonneg h) ypos)
  simp only [le_add_iff_nonneg_right, gt_iff_lt, sub_pos]
  apply mul_nonneg
  linarith
  linarith
  rw[ht,←sub_eq_zero,←sub_smul,smul_eq_zero]
  left
  ring

/- Given a segment and a ray, if the source and the target of the segment both lie on the ray, and if $A$ is a point in the interior of the segment, then $A$ lies in the interior of the ray. -/
theorem every_int_pt_lies_int_ray_of_source_and_target_lies_on_ray {seg : Seg P} {ray : Ray P} (h₁ : seg.source LiesOn ray) (h₂ : seg.target LiesOn ray) {A : P} (ha : A LiesInt seg) : A LiesInt ray := by
  rcases h₁ with ⟨x,xnonneg,hx⟩
  rcases h₂ with ⟨y,ynonneg,hy⟩
  rcases (Seg.lies_int_iff A).mp ha with ⟨nd, t, tpos, tlt1, ht⟩
  simp only [Seg.toVec,←vec_sub_vec ray.1 seg.1,hx,hy,sub_eq_iff_eq_add,←sub_smul,smul_smul,←add_smul] at ht
  apply (Ray.lies_int_iff A).mpr
  use (1-t)*x+t*y
  have ynex:y≠x:= by
    contrapose! nd
    rw[Seg.is_nd,not_not,eq_iff_vec_eq_zero,←vec_sub_vec ray.1,hx,hy,←sub_smul,nd,sub_self,zero_smul]
  constructor
  by_cases 0=x
  rw[←h,mul_zero,zero_add]
  apply mul_pos
  exact tpos
  apply lt_of_le_of_ne
  exact ynonneg
  rw[h]
  symm
  exact ynex
  have :0<(1-t)*x:=by
    apply mul_pos
    linarith
    apply lt_of_le_of_ne xnonneg h
  apply lt_of_lt_of_le this
  simp only [le_add_iff_nonneg_right, gt_iff_lt]
  apply mul_nonneg
  linarith
  linarith
  rw[ht,←sub_eq_zero,←sub_smul,smul_eq_zero]
  left
  ring

/- Given two rays $ray_1$ and $ray_2$ with same direction, if the source of $ray_1$ lies on $ray_2$, and if $A$ is a point on $ray_1$, then $A$ lies on $ray_2$. -/
theorem every_pt_lies_on_ray_of_source_lies_on_ray_and_same_dir {ray₁ ray₂ : Ray P} (e : ray₁.toDir = ray₂.toDir) (h : ray₁.source LiesOn ray₂){A : P} (ha : A LiesOn ray₁) : A LiesOn ray₂ := by
  rcases h with ⟨x,xnonneg,hx⟩
  rcases ha with ⟨t,tnonneg,ht⟩
  use x+t
  constructor
  linarith
  rw[←vec_add_vec ray₂.source ray₁.source A,hx,ht,e,add_smul]

/- Given two rays $ray_1$ and $ray_2$ with same direction, if the source of $ray_1$ lies in the interior of $ray_2$, and if $A$ is a point on $ray_1$, then $A$ lies in the interior of $ray_2$. -/
theorem every_pt_lies_int_ray_of_source_lies_int_ray_and_same_dir {ray₁ ray₂ : Ray P} (e : ray₁.toDir = ray₂.toDir) (h : ray₁.source LiesInt ray₂) {A : P} (ha : A LiesOn ray₁) : A LiesInt ray₂ := by
  apply (Ray.lies_int_iff A).mpr
  rcases ha with ⟨t,tnonneg,ht⟩
  rcases (Ray.lies_int_iff ray₁.1).mp h with ⟨x, xpos, hx⟩
  rw[e] at ht
  use x+t
  constructor
  linarith
  rw[←vec_add_vec ray₂.1 ray₁.1,hx,ht,add_smul]

end MoreCoercionCompatibility

end EuclidGeom