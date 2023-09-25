import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section
namespace EuclidGeom

variable {P: Type _} [EuclideanPlane P]

section MoreCoercionCompatibility

-- More theorem of this flavor, please formulate them on your own, following the instructions.  `But be careful that we introduced seg₁ and seg₂ using {}, this is because we want the compute to infer what they are; same applies to the point A.`

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
  apply mul_nonneg
  linarith
  linarith
  constructor
  nth_rw 2[←sub_add_cancel 1 t,←mul_one (1-t)]
  nth_rw 4[←mul_one t]
  apply add_le_add
  apply mul_le_mul
  linarith
  linarith
  linarith
  linarith
  apply mul_le_mul
  linarith
  linarith
  linarith
  linarith
  rw [ht]
  
/- Given two segments $seg_1$ and $seg_2$, if the source and the target of $seg_1$ both lie in the interior of $seg_2$, and if $A$ is a point on $seg_1$, then $A$ lies in the interior of $seg_2$. -/

theorem every_pt_lies_int_seg_of_source_and_target_lies_int_seg {seg₁ seg₂ : Seg P} (h₂ : seg₁.source LiesInt seg₂) (h₂ : seg₁.target LiesInt seg₂) {A : P} (ha : A LiesOn seg₁) : A LiesInt seg₂ := sorry

/- Given two segments $seg_1$ and $seg_2$, if the source and the target of $seg_1$ both lie on $seg_2$, and if $A$ is a point in the interior of $seg_1$, then $A$ lies in the interior of $seg_2$. -/
theorem every_int_pt_lies_int_seg_of_source_and_target_lies_on_seg {seg₁ seg₂ : Seg P} (h₁ : seg₁.source LiesOn seg₂) (h₂ : seg₂.source LiesOn seg₂) {A : P} (ha : A LiesInt seg₁) : A LiesInt seg₂ := sorry

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
theorem every_pt_lies_int_ray_of_source_and_target_lies_int_ray {seg : Seg P} {ray : Ray P}(h₁ : seg.source LiesInt ray) (h₂ : seg.target LiesInt ray) {A : P} (ha : A LiesOn seg) : A LiesInt ray := sorry

/- Given a segment and a ray, if the source and the target of the segment both lie on the ray, and if $A$ is a point in the interior of the segment, then $A$ lies in the interior of the ray. -/
theorem every_int_pt_lies_int_ray_of_source_and_target_lies_on_ray {seg : Seg P} {ray : Ray P} (h₁ : seg.source LiesOn ray) (h₂ : seg.target LiesOn ray) {A : P} (ha : A LiesInt seg) : A LiesInt ray := sorry


/- Given two rays $ray_1$ and $ray_2$ with same direction, if the source of $ray_1$ lies on $ray_2$, and if $A$ is a point on $ray_1$, then $A$ lies on $ray_2$. -/
theorem every_pt_lies_on_ray_of_source_lies_on_ray_and_same_dir {ray₁ ray₂ : Ray P} (e : ray₁.toDir = ray₂.toDir) (h : ray₁.source LiesOn ray₂){A : P} (ha : A LiesOn ray₁) : A LiesOn ray₂ := sorry

/- Given two rays $ray_1$ and $ray_2$ with same direction, if the source of $ray_1$ lies in the interior of $ray_2$, and if $A$ is a point on $ray_1$, then $A$ lies in the interior of $ray_2$. -/
theorem every_pt_lies_int_ray_of_source_lies_int_ray_and_same_dir {ray₁ ray₂ : Ray P} (e : ray₁.toDir = ray₂.toDir) (h : ray₁.source LiesInt ray₂) {A : P} (ha : A LiesOn ray₁) : A LiesInt ray₂ := sorry



end MoreCoercionCompatibility



end EuclidGeom