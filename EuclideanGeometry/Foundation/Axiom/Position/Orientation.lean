import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Linear.Colinear
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash

/- This file discuss the relative positions of points and rays on a plane. -/
noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P]

/- Definition of the wedge of three points.-/

section wedge

def wedge (A B C : P) : ℝ := det (VEC A B) (VEC A C)

def oarea (A B C : P) : ℝ := wedge A B C / 2

theorem wedge213 (A B C : P) : wedge B A C = - wedge A B C := by
  unfold wedge
  rw [← neg_vec A B, ← neg_one_smul ℝ, det_smul_left_eq_mul_det, det_eq_neg_det, det_eq_neg_det (VEC A B) _, neg_one_mul, neg_neg, neg_neg, ← vec_sub_vec A B C, det_sub_eq_det]

theorem wedge132 (A B C : P) : wedge A C B = - wedge A B C := by
  apply det_symm

theorem wedge312 (A B C : P) : wedge C A B = wedge A B C := by
  rw [wedge213, wedge132, neg_neg]

theorem wedge231 (A B C : P) : wedge B C A = wedge A B C := by rw [wedge312, wedge312]

theorem wedge321 (A B C : P) : wedge C B A = - wedge A B C := by rw [wedge213, wedge231]

theorem wedge_eq_sine_mul_length_mul_length (A B C : P) (bnea : B ≠ A) (cnea : C ≠ A) : wedge A B C = (Real.sin (Angle.mk_pt_pt_pt B A C bnea cnea).value * (SEG A B).length *(SEG A C).length) := by
  unfold wedge
  have h0 : (Angle.mk_pt_pt_pt B A C bnea cnea).value = Vec_nd.angle (VEC_nd A B bnea) (VEC_nd A C cnea)  := rfl
  rw [h0]
  apply det_eq_sin_mul_norm_mul_norm (VEC_nd A B bnea) (VEC_nd A C cnea)

theorem colinear_iff_wedge_eq_zero (A B C : P) : (colinear A B C) ↔ (wedge A B C = 0) := by
  dsimp only [wedge]
  by_cases B ≠ A
  have vecabnd : VEC A B ≠ 0 := by
    exact (ne_iff_vec_ne_zero A B).mp h
  constructor
  intro k
  apply (det_eq_zero_iff_eq_smul (VEC A B) (VEC A C) vecabnd).mpr
  exact (colinear_iff_eq_smul_vec_of_ne h).mp k
  intro k
  apply (det_eq_zero_iff_eq_smul (VEC A B) (VEC A C) vecabnd).mp at k
  exact (colinear_iff_eq_smul_vec_of_ne h).mpr k
  simp at h
  have vecab0 : VEC A B = 0 := by
    exact (eq_iff_vec_eq_zero A B).mp h
  constructor
  intro
  dsimp only [det]
  field_simp [vecab0]
  intro
  rw [h]
  exact triv_colinear A C

theorem wedge_pos_iff_angle_pos (A B C : P) (nd : ¬colinear A B C) : (0 < wedge A B C) ↔ (0 < (Angle.mk_pt_pt_pt B A C (ne_of_not_colinear nd).2.2 (ne_of_not_colinear nd).2.1.symm).value ∧ (Angle.mk_pt_pt_pt B A C (ne_of_not_colinear nd).2.2 (ne_of_not_colinear nd).2.1.symm).value < π) := by
  have h1 : 0 < (SEG A B).length := by
      have abnd : (SEG A B).is_nd := (ne_of_not_colinear nd).2.2
      exact length_pos_iff_nd.mpr (abnd)
  have h2 : 0 < (SEG A C).length := by
      have acnd : (SEG A C).is_nd := (ne_of_not_colinear nd).2.1.symm
      exact length_pos_iff_nd.mpr (acnd)
  constructor
  · intro h0
    rw[wedge_eq_sine_mul_length_mul_length A B C (ne_of_not_colinear nd).2.2 (ne_of_not_colinear nd).2.1.symm] at h0
    have h3 : 0 < Real.sin ((Angle.mk_pt_pt_pt B A C (ne_of_not_colinear nd).2.2 (ne_of_not_colinear nd).2.1.symm).value) := by
      field_simp at h0
      exact h0
    rw [sin_pos_iff_angle_pos] at h3
    exact h3
  rw[wedge_eq_sine_mul_length_mul_length A B C (ne_of_not_colinear nd).2.2 (ne_of_not_colinear nd).2.1.symm]
  intro h0
  have h3 : 0 < Real.sin ((Angle.mk_pt_pt_pt B A C (ne_of_not_colinear nd).2.2 (ne_of_not_colinear nd).2.1.symm).value) := (sin_pos_iff_angle_pos (Angle.mk_pt_pt_pt B A C (ne_of_not_colinear nd).2.2 (ne_of_not_colinear nd).2.1.symm)).mpr h0
  field_simp
  exact h2

end wedge

/- Oriented distance-/
section oriented_distance

def odist' (A : P) (ray : Ray P) : ℝ := det ray.2.1 (VEC ray.1 A)

theorem odist'_eq_zero_iff_exist_real_vec_eq_smul {A : P} {ray : Ray P} : odist' A ray = 0 ↔ (∃ t : ℝ, VEC ray.1 A = t • ray.2.1) := by
  constructor
  intro k
  dsimp only [odist'] at k
  apply (det_eq_zero_iff_eq_smul (ray.2.1) (VEC ray.1 A) (Dir.tovec_ne_zero ray.2)).mp
  exact k
  intro e
  apply (det_eq_zero_iff_eq_smul (ray.2.1) (VEC ray.1 A) (Dir.tovec_ne_zero ray.2)).mpr
  exact e

theorem odist'_eq_sine_mul_length (A : P) (ray : Ray P) (h : A ≠ ray.source) : odist' A ray = Real.sin ((Angle.mk_ray_pt ray A h).value) * (SEG ray.source A).length := by
  rw [odist',Angle.value]
  have h0 : (Angle.mk_ray_pt ray A h).value = Vec_nd.angle ray.2.toVec_nd (VEC_nd ray.source A h) := angle_value_eq_angle A ray h
  have h1 : ray.2.toVec_nd.1 = ray.2.1 := rfl
  have h2 : (VEC_nd ray.source A h).1=VEC ray.source A := rfl
  have h3 : Vec.norm (Dir.toVec_nd (ray.toDir)) = 1 := by apply Dir.norm_of_dir_tovec_eq_one
  have h4 : (SEG ray.source A).length = Vec.norm (VEC_nd ray.source A h) := rfl
  rw [← h1, ← h2, det_eq_sin_mul_norm_mul_norm ray.2.toVec_nd (VEC_nd ray.source A h),h3,h4,← h0]
  ring_nf
  rw [mul_comm]
  rfl

theorem wedge_eq_odist'_mul_length (A B C : P) (bnea : B ≠ A) : (wedge A B C) = ((odist' C (RAY A B bnea)) * (SEG A B).length) := by
  by_cases p : C ≠ A
  rw [wedge_eq_sine_mul_length_mul_length A B C bnea p,odist'_eq_sine_mul_length C (RAY A B bnea),mul_assoc (Real.sin ((Angle.mk_ray_pt (RAY A B bnea) C p).value)) ((SEG (RAY A B bnea).source C).length) ((SEG A B).length),mul_comm ((SEG (RAY A B bnea).source C).length) ((SEG A B).length),←mul_assoc (Real.sin ((Angle.mk_ray_pt (RAY A B bnea) C p).value)) ((SEG A B).length) ((SEG (RAY A B bnea).source C).length)]
  congr
  have vecrayc0 : VEC (RAY A B bnea).source C = 0 := (eq_iff_vec_eq_zero A C).mp (not_not.1 p)
  dsimp only [wedge, odist', det]
  field_simp [(eq_iff_vec_eq_zero A C).mp (not_not.1 p), vecrayc0]

theorem odist'_eq_odist'_of_to_dirline_eq_to_dirline (A : P) (ray ray' : Ray P) (h : same_dir_line ray ray') : odist' A ray = odist' A ray' := by
  have h₁ : ray.2.1 =ray'.2.1 := by
    congr 1
    exact h.1
  have h₂ : ∃ t : ℝ, VEC ray.1 ray'.1 = t • ray.2.1 := lies_on_or_rev_iff_exist_real_vec_eq_smul.mp h.2
  have h₃ : ∃ t : ℝ, VEC ray.1 A = t • ray.2.1 + VEC ray'.1 A := by
    rw [←vec_add_vec ray.1 ray'.1 A]
    choose t₁ ht using h₂
    use t₁
    congr
  dsimp only [odist']
  choose t₂ kt using h₃
  rw [kt,det_add_right_eq_add_det ray.2.1 (t₂ • ray.2.1) (VEC ray'.1 A)]
  rw [(det_eq_zero_iff_eq_smul ray.2.1 (t₂ • ray.2.1) (Dir.tovec_ne_zero ray.2)).mpr _]
  field_simp[h₁]
  use t₂

def odist (A : P) [DirFig α] (l : α P) : ℝ := Quotient.lift (s := same_dir_line.setoid) (fun ray => odist' A ray) (odist'_eq_odist'_of_to_dirline_eq_to_dirline A) (toDirLine l)

theorem odist_reverse_eq_neg_odist (A : P) [DirFig α] (dl : α P) : odist A (DirFig.reverse dl) = - odist A dl := sorry

theorem wedge_eq_wedge_iff_odist_eq_odist_of_ne (A B C D : P) (bnea : B ≠ A) : (odist C (Seg_nd.mk A B bnea) = odist D (Seg_nd.mk A B bnea)) ↔ (wedge A B C = wedge A B D) := sorry

end oriented_distance

/- Positions of points on a line, ray, oriented segments. -/

section point_toray

def odist_sign (A : P) [DirFig α] (df : α P) : ℝ := by
  by_cases 0 < odist A df
  · exact 1
  by_cases odist A df < 0
  · exact -1
  exact 0

def IsOnLeftSide (A : P) [DirFig α] (df : α P) : Prop := by
  by_cases 0 < odist A df
  · exact True
  · exact False

def IsOnRightSide (A : P) [DirFig α] (df : α P) : Prop := by
  by_cases odist A df < 0
  · exact True
  · exact False

def OnLine (A : P) [DirFig α] (df : α P) : Prop := by
  by_cases odist A df = 0
  · exact True
  · exact False

def OffLine (A : P) [DirFig α] (df : α P) : Prop := by
  by_cases odist A df = 0
  · exact False
  · exact True

theorem online_iff_online (A : P) (ray : Ray P) : OnLine A ray ↔ Line.IsOn A ray.toLine := by
  dsimp only [OnLine]
  by_cases h : odist' A ray = 0
  · simp
    constructor
    intro
    exact lies_on_or_rev_iff_exist_real_vec_eq_smul.mpr (odist'_eq_zero_iff_exist_real_vec_eq_smul.mp h)
    intro
    exact h
  simp
  constructor
  intro k
  absurd h k
  exact (h k).elim
  dsimp only [Line.IsOn]
  intro p
  rw [Ray.toline_carrier_eq_ray_carrier_union_rev_carrier ray] at p
  exact (odist'_eq_zero_iff_exist_real_vec_eq_smul).mpr (lies_on_or_rev_iff_exist_real_vec_eq_smul.mp p)

theorem online_iff_lies_on_line (A : P) [DirFig α] (df : α P) : Line.IsOn A (toLine df) ↔ odist A df = 0 := sorry

theorem off_line_iff_not_online (A : P) [DirFig α] (df : α P) : OffLine A df ↔ ¬OnLine A df := sorry

/- Relation of position of points on a ray and directed distance-/

end point_toray

section oriented_area

theorem oarea_eq_length_mul_odist_div_2 (A B C : P) (bnea : B ≠ A) : (oarea A B C) = ((odist C (Seg_nd.mk A B bnea)) * (SEG A B).length) / 2:= sorry

theorem oarea_eq_oarea_iff_odist_eq_odist_of_ne (A B C D : P) (bnea : B ≠ A) : (odist C (Seg_nd.mk A B bnea) = odist D (Seg_nd.mk A B bnea)) ↔ oarea A B C = oarea A B D := sorry

theorem oarea_eq_sine_mul_length_mul_length_div_2 (A B C : P) (bnea : B ≠ A) (cnea : C ≠ A) : oarea A B C = (Real.sin (Angle.mk_pt_pt_pt B A C bnea cnea).value * (SEG A B).length *(SEG A C).length) / 2 := sorry

theorem oarea_eq_zero_of_colinear (A B C : P) : oarea A B C = 0 ↔ colinear A B C := sorry

theorem oarea_tri_nd_ne_zero (A B C : P) (trind : ¬ colinear A B C) : oarea A B C ≠ 0 := sorry

end oriented_area

section cooperation_with_parallel

theorem odist_eq_odist_of_parallel' (A B : P) (ray : Ray P) (bnea : B ≠ A) (para : parallel (SEG_nd A B bnea) ray) : odist A ray =odist B ray := by
  unfold odist
  have h1 : det ray.2.1 (VEC ray.1 B) = det ray.2.1 (VEC ray.1 A) + det ray.2.1 (VEC A B) := by
    rw [←vec_add_vec ray.1 A B]
    rw [det_add_right_eq_add_det]
  have h2 : det ray.2.1 (VEC A B) = 0 := by
    unfold parallel at para
    have h3 : Dir.toProj ray.2 = Vec_nd.toProj (⟨(VEC A B) , (VEC_nd A B bnea).2⟩ : Vec_nd) := para.symm
    have h4 : Vec_nd.toProj ray.2.toVec_nd = Vec_nd.toProj (⟨(VEC A B) , (VEC_nd A B bnea).2⟩ : Vec_nd) := by
      rw [← h3]
      exact dir_toVec_nd_toProj_eq_dir_toProj ray.2
    exact det_eq_zero_of_toProj_eq (⟨ray.2.1 , Dir.tovec_ne_zero ray.2⟩ : Vec_nd) (⟨(VEC A B) , (VEC_nd A B bnea).2⟩ : Vec_nd) h4
  rw [h2] at h1
  rw [add_zero] at h1
  exact h1.symm

theorem odist_eq_odist_of_parallel (A B : P) [DirFig α] (df : α P) (bnea : B ≠ A) (para : parallel (Seg_nd.mk A B bnea) df) : odist A df = odist B df := sorry

theorem wedge_eq_wedge_iff_parallel_of_ne_ne (A B C D : P) (bnea : B ≠ A) (dnec : D ≠ C) : (parallel (Seg_nd.mk A B bnea) (Seg_nd.mk C D dnec)) ↔ wedge A B C = wedge A B D := sorry

theorem odist_eq_odist_iff_parallel_ne (A B : P) [DirFig α] (df : α P) (bnea : B ≠ A) : (parallel (Seg_nd.mk A B bnea) df) ↔ odist A df = odist B df := sorry

theorem oarea_eq_oarea_iff_parallel_ne (A B C D : P) (bnea : B ≠ A) (dnec : D ≠ C) : (parallel (Seg_nd.mk A B bnea) (Seg_nd.mk C D dnec)) ↔ oarea A B C = oarea A B D := sorry

end cooperation_with_parallel

scoped infix : 50 "LiesOnLeft" => IsOnLeftSide
scoped infix : 50 "LiesOnRight" => IsOnRightSide

section handside

theorem same_sign_of_parallel (A B : P) (ray : Ray P) (bnea : B ≠ A) (para : parallel (RAY A B bnea)  ray) : odist_sign A ray = odist_sign B ray := by
  unfold odist_sign
  rw [odist_eq_odist_of_parallel' A B ray bnea para]

theorem same_odist_sign_of_same_odist_sign (A B : P) (l : DirLine P) (signeq : odist_sign A l = odist_sign B l) : ∀ (C : P) , Seg.IsOn C (SEG A B) → odist_sign C l = odist_sign A l := sorry

theorem no_intersect_of_same_odist_sign (A B : P) (l : DirLine P) (signeq : odist_sign A l * odist_sign B l = 1) : ∀ (C : P) , Seg.IsOn C (SEG A B) → ¬ Line.IsOn C l := sorry

theorem intersect_of_diff_odist_sign (A B : P) (l : DirLine P) (signdiff : odist_sign A l * odist_sign B l = -1) : ∃ (C : P), Seg.IsOn C (SEG A B) ∧ Line.IsOn C l := sorry

end handside

/- Position of two rays -/
section ray_toray

/- Statement of his theorem should change, since ray₀.source ≠ ray₂.source. -/
theorem intersect_of_ray_on_left_iff (ray₁ ray₂ : Ray P) (h : ray₂.source ≠ ray₁.source) : let ray₀ := Ray.mk_pt_pt ray₁.source ray₂.source h; (0 < value_of_angle_of_two_ray_of_eq_source ray₀ ray₁ rfl) ∧ (value_of_angle_of_two_ray_of_eq_source ray₀ ray₁ rfl < value_of_angle_of_two_ray_of_eq_source ray₀ ray₂ sorry) ∧ (value_of_angle_of_two_ray_of_eq_source ray₀ ray₂ sorry < π) ↔ (∃ A : P, (A LiesOn ray₁) ∧ (A LiesOn ray₂) ∧ (A LiesOnLeft ray₀))  := sorry

end ray_toray



/- Position of two lines; need a function to take the intersection of two lines (when they intersect). -/


/- A lot more theorems regarding positions -/
/- e.g. 180 degree implies colinear -/

end EuclidGeom
