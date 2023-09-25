import EuclideanGeometry.Foundation.Axiom.Linear.Ray
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex

noncomputable section
namespace EuclidGeom

variable {P: Type _} [EuclideanPlane P]

section MoreCoercionCompatibility

-- More theorem of this flavor, please formulate them on your own, following the instructions.  `But be careful that we introduced seg₁ and seg₂ using {}, this is because we want the compute to infer what they are; same applies to the point A.`

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

/- Given two segments $seg_1$ and $seg_2$, if the source and the target of the $seg_1$ both lie on $seg_2$, then every point of $seg_1$ lies on $seg_2$. -/
theorem every_pt_lies_on_seg_of_source_and_target_lies_on_seg {seg₁ seg₂ : Seg P} (h₁ : seg₁.source LiesOn seg₂) (h₂ : seg₁.target LiesOn seg₂) {A : P} (ha : A LiesOn seg₁) : (A LiesOn seg₂) :=by
  by_cases seg₂.is_nd
  set seg_nd:=Seg_nd.mk seg₂.source seg₂.target h
  have: seg₂=seg_nd.1:=by rfl
  rw[this]
  apply lies_on_iff_lies_on_toRay_and_rev_toRay.mpr
  constructor
  apply every_pt_lies_on_ray_of_source_and_target_lies_on_ray
  apply Seg_nd.lies_on_toRay_of_lies_on
  apply h₁
  apply Seg_nd.lies_on_toRay_of_lies_on
  apply h₂
  exact ha
  apply every_pt_lies_on_ray_of_source_and_target_lies_on_ray
  apply Seg_nd.lies_on_toRay_of_lies_on
  apply Seg.lies_on_iff_lies_on_rev.mp
  exact h₁
  apply Seg_nd.lies_on_toRay_of_lies_on
  apply Seg.lies_on_iff_lies_on_rev.mp
  exact h₂
  exact ha
  simp only [Seg.is_nd] at h
  push_neg at h
  rcases h₁ with ⟨x,_,_,hx⟩
  rcases h₂ with ⟨y,ynonneg,yle1,hy⟩
  rcases ha with ⟨t,tnonneg,tle1,ht⟩
  rw[h,vec_same_eq_zero,smul_zero,←eq_iff_vec_eq_zero] at hx hy
  rw[hx,hy,vec_same_eq_zero,smul_zero,←eq_iff_vec_eq_zero] at ht
  use 0
  simp only [le_refl, zero_le_one, zero_smul, true_and]
  rw[← eq_iff_vec_eq_zero,ht]

/- Given two segments $seg_1$ and $seg_2$, if the source and the target of $seg_1$ both lie in the interior of $seg_2$, and if $A$ is a point on $seg_1$, then $A$ lies in the interior of $seg_2$. -/
theorem every_pt_lies_int_seg_of_source_and_target_lies_int_seg {seg₁ seg₂ : Seg P} (h₂ : seg₁.source LiesInt seg₂) (h₂ : seg₁.target LiesInt seg₂) {A : P} (ha : A LiesOn seg₁) : A LiesInt seg₂ := sorry

/- Given two segments $seg_1$ and $seg_2$, if the source and the target of $seg_1$ both lie on $seg_2$, and if $A$ is a point in the interior of $seg_1$, then $A$ lies in the interior of $seg_2$. -/
theorem every_int_pt_lies_int_seg_of_source_and_target_lies_on_seg {seg₁ seg₂ : Seg P} (h₁ : seg₁.source LiesOn seg₂) (h₂ : seg₂.source LiesOn seg₂) {A : P} (ha : A LiesInt seg₁) : A LiesInt seg₂ := sorry

/- Given two rays $ray_1$ and $ray_2$ with same direction, if the source of $ray_1$ lies on $ray_2$, and if $A$ is a point on $ray_1$, then $A$ lies on $ray_2$. -/
theorem every_pt_lies_on_ray_of_source_lies_on_ray_and_same_dir {ray₁ ray₂ : Ray P} (e : ray₁.toDir = ray₂.toDir) (h : ray₁.source LiesOn ray₂){A : P} (ha : A LiesOn ray₁) : A LiesOn ray₂ := sorry

/- Given two rays $ray_1$ and $ray_2$ with same direction, if the source of $ray_1$ lies in the interior of $ray_2$, and if $A$ is a point on $ray_1$, then $A$ lies in the interior of $ray_2$. -/
theorem every_pt_lies_int_ray_of_source_lies_int_ray_and_same_dir {ray₁ ray₂ : Ray P} (e : ray₁.toDir = ray₂.toDir) (h : ray₁.source LiesInt ray₂) {A : P} (ha : A LiesOn ray₁) : A LiesInt ray₂ := sorry



end MoreCoercionCompatibility



end EuclidGeom