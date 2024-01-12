import EuclideanGeometry.Foundation.Axiom.Linear.Colinear
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel
import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash

/- This file discuss the relative positions of points and rays on a plane. -/
noncomputable section
namespace EuclidGeom

open Classical AngValue

variable {P : Type*} [EuclideanPlane P]

/- Definition of the wedge of three points.-/

section wedge

def wedge (A B C : P) : ℝ := Vec.det (VEC A B) (VEC A C)

def oarea (A B C : P) : ℝ := wedge A B C / 2

theorem wedge213 (A B C : P) : wedge B A C = - wedge A B C := by
  unfold wedge
  rw [← neg_vec A B,← vec_sub_vec A B C, map_sub]
  simp only [map_neg, LinearMap.neg_apply, Vec.det_self, neg_zero, sub_zero]

theorem wedge132 (A B C : P) : wedge A C B = - wedge A B C := by
  unfold wedge
  rw [Vec.det_skew]

theorem wedge312 (A B C : P) : wedge C A B = wedge A B C := by
  rw [wedge213, wedge132, neg_neg]

theorem wedge231 (A B C : P) : wedge B C A = wedge A B C := by rw [wedge312, wedge312]

theorem wedge321 (A B C : P) : wedge C B A = - wedge A B C := by rw [wedge213, wedge231]

theorem wedge_eq_length_mul_length_mul_sin (A B C : P) [bnea : PtNe B A] [cnea : PtNe C A] : wedge A B C = (SEG A B).length * (SEG A C).length * sin (ANG B A C).value := by
  unfold wedge
  have h0 : (ANG B A C).value = VecND.angle (VEC_nd A B) (VEC_nd A C)  := rfl
  rw [h0]
  rw [Seg.length_eq_norm_toVec, Seg.length_eq_norm_toVec]
  exact (VecND.norm_mul_sin (VEC_nd A B) (VEC_nd A C)).symm

theorem colinear_iff_wedge_eq_zero (A B C : P) : (colinear A B C) ↔ (wedge A B C = 0) := by
  dsimp only [wedge]
  by_cases h : PtNe B A
  · have vecabnd : VEC A B ≠ 0 := by
      exact (ne_iff_vec_ne_zero A B).mp h.out
    rw [← Vec.det_skew, neg_eq_zero, Vec.det_eq_zero_iff_eq_smul_right]
    simp only [vecabnd, false_or]
    constructor
    · intro k
      exact colinear_iff_eq_smul_vec_of_ne.mp k
    · intro k
      exact colinear_iff_eq_smul_vec_of_ne.mpr k
  · simp [PtNe, fact_iff] at h
    have vecab0 : VEC A B = 0 := by
      exact (eq_iff_vec_eq_zero A B).mp h
    constructor
    intro
    field_simp [vecab0]
    intro
    rw [h]
    exact triv_colinear A C

theorem not_colinear_iff_wedge_ne_zero (A B C : P) : (¬ colinear A B C) ↔ (wedge A B C ≠ 0) := by
  rw [colinear_iff_wedge_eq_zero]

theorem wedge_pos_iff_angle_pos (A B C : P) (nd : ¬colinear A B C) : (0 < wedge A B C) ↔ (Angle.mk_pt_pt_pt B A C (ne_of_not_colinear nd).2.2 (ne_of_not_colinear nd).2.1.symm).value.IsPos := by
  have h1 : 0 < dist A B := by
      have abnd : (SEG A B).IsND := (ne_of_not_colinear nd).2.2
      exact dist_pos.mpr (abnd.symm)
  have h2 : 0 < dist A C := by
      have acnd : (SEG A C).IsND := (ne_of_not_colinear nd).2.1.symm
      exact dist_pos.mpr (acnd.symm)
  constructor
  · intro h0
    rw [wedge_eq_length_mul_length_mul_sin (bnea := ⟨(ne_of_not_colinear nd).2.2⟩) (cnea := ⟨(ne_of_not_colinear nd).2.1.symm⟩)] at h0
    have h3 : 0 < sin (Angle.mk_pt_pt_pt B A C (ne_of_not_colinear nd).2.2 (ne_of_not_colinear nd).2.1.symm).value := by
      field_simp at h0
      exact h0
    rw [sin_pos_iff_angle_pos] at h3
    exact h3
  rw [wedge_eq_length_mul_length_mul_sin (bnea := ⟨(ne_of_not_colinear nd).2.2⟩) (cnea := ⟨(ne_of_not_colinear nd).2.1.symm⟩)]
  intro h0
  have h3 : 0 < sin ((Angle.mk_pt_pt_pt B A C (ne_of_not_colinear nd).2.2 (ne_of_not_colinear nd).2.1.symm).value) := (sin_pos_iff_angle_pos (Angle.mk_pt_pt_pt B A C (ne_of_not_colinear nd).2.2 (ne_of_not_colinear nd).2.1.symm)).mpr h0
  field_simp
  exact h3

end wedge

/- Oriented distance-/
section oriented_distance

def odist' (A : P) (ray : Ray P) : ℝ := Vec.det ray.2.unitVec (VEC ray.1 A)

theorem odist'_eq_zero_iff_exist_real_vec_eq_smul {A : P} {ray : Ray P} : odist' A ray = 0 ↔ (∃ t : ℝ, VEC ray.1 A = t • ray.2.unitVec) := by
  dsimp only [odist']
  rw [Vec.det_eq_zero_iff_eq_smul_left]
  simp

theorem odist'_eq_length_mul_sin (A : P) (ray : Ray P) [h : PtNe A ray.source] : odist' A ray = (SEG ray.source A).length * sin ((Angle.mk_ray_pt ray A h.out).value) := by
  rw [odist',Angle.value]
  have h0 : (Angle.mk_ray_pt ray A h.out).value = VecND.angle ray.2.unitVecND (VEC_nd ray.source A) := angle_value_eq_angle A ray
  have h2 : (VEC_nd ray.source A).1 = VEC ray.source A := rfl
  have h3 : ‖ray.toDir.unitVecND‖ = 1 := by simp
  have h4 : (SEG ray.source A).length = ‖VEC_nd ray.source A‖ := Seg.length_eq_norm_toVec
  rw [← h2, ← VecND.norm_mul_sin ray.2.unitVecND (VEC_nd ray.source A),h3,h4,← h0]
  ring_nf
  rfl

theorem wedge_eq_length_mul_odist' (A B C : P) [bnea : PtNe B A] : (wedge A B C) = (SEG A B).length * odist' C (RAY A B) := by
  by_cases p : C = A
  · have vecrayc0 : VEC (RAY A B).source C = 0 := (eq_iff_vec_eq_zero A C).mp p
    dsimp only [wedge, odist']
    field_simp [(eq_iff_vec_eq_zero A C).mp p, vecrayc0]
  · haveI cnea : PtNe C A := ⟨p⟩
    rw [wedge_eq_length_mul_length_mul_sin,
      @odist'_eq_length_mul_sin _ _ C (RAY A B) cnea, ← mul_assoc]
    rfl


theorem odist'_eq_odist'_of_to_dirline_eq_to_dirline (A : P) (ray ray' : Ray P) (h : same_dir_line ray ray') : odist' A ray = odist' A ray' := by
  have h₁ : ray.2.unitVec = ray'.2.unitVec := by
    congr 1
    exact h.1
  have h₂ : ∃ t : ℝ, VEC ray.1 ray'.1 = t • ray.2.unitVec := lies_on_or_rev_iff_exist_real_vec_eq_smul.mp h.2
  have h₃ : ∃ t : ℝ, VEC ray.1 A = t • ray.2.unitVec + VEC ray'.1 A := by
    rw [←vec_add_vec ray.1 ray'.1 A]
    choose t₁ ht using h₂
    use t₁
    congr
  dsimp only [odist']
  choose t₂ kt using h₃
  rw [kt, map_add, map_smul]
  simp [h₁]

def odist {α} [DirFig α P] (A : P) (l : α) : ℝ := Quotient.lift (s := same_dir_line.setoid) (fun ray => odist' A ray) (odist'_eq_odist'_of_to_dirline_eq_to_dirline A) (toDirLine l)

theorem odist_reverse_eq_neg_odist' (A : P) (ray : Ray P) : odist A (Ray.reverse ray) = - odist A ray := by
  show odist' A (Ray.reverse ray) = - odist' A ray
  unfold odist'
  have h0 : (ray.reverse).toDir.unitVec = -ray.toDir.unitVec := by
    simp only [Ray.reverse_toDir, Dir.neg_unitVec]
  rw [h0, map_neg]
  rfl

theorem odist_reverse_eq_neg_odist'' (A : P) (dl : DirLine P) : odist A (DirLine.reverse dl) = - odist A dl := by
  rcases (Quotient.exists_rep dl) with ⟨ray , h0⟩
  have h1 : odist A dl = odist A ray := by
    rw [← h0]
    rfl
  have h2 : DirLine.reverse dl = Quotient.mk same_dir_line.setoid (Ray.reverse ray) := by
    rw [← h0]
    rfl
  rw [h1, h2, ← odist_reverse_eq_neg_odist' A ray]
  rfl

theorem odist_reverse_eq_neg_odist {α} (A : P) [DirFig α P] (df : α) : odist A (DirFig.reverse df) = - odist A df := by
  have h0 : odist A (DirFig.reverse df) = odist A (toDirLine (DirFig.reverse df)) := rfl
  rw [← DirFig.toDirLine_rev_eq_to_rev_toDirLine] at h0
  rw [h0]
  rw [odist_reverse_eq_neg_odist'' A (toDirLine df)]
  rfl

theorem wedge_eq_wedge_iff_odist_eq_odist_of_ne (A B C D : P) [bnea : PtNe B A] : (odist C (SEG_nd A B) = odist D (SEG_nd A B)) ↔ (wedge A B C = wedge A B D) := by
  rw [wedge_eq_length_mul_odist' A B C, wedge_eq_length_mul_odist' A B D]
  have h0 : 0 ≠ Seg.length (SEG A B) := by
    rw [length_ne_zero_iff_nd]
    exact bnea.out
  field_simp
  tauto

end oriented_distance

/- Positions of points on a line, ray, oriented segments. -/

section point_toRay
variable {α} [DirFig α P]

def odist_sign (A : P) (df : α) : ℝ := SignType.sign (odist A df)

def IsOnLeftSide (A : P) (df : α) : Prop := 0 < odist A df

def IsOnRightSide (A : P) (df : α) : Prop := odist A df < 0

def OnLine (A : P) (df : α) : Prop := odist A df = 0

def OffLine (A : P) (df : α) : Prop := ¬ odist A df = 0

theorem online_iff_online (A : P) (ray : Ray P) : OnLine A ray ↔ Line.IsOn A ray.toLine := by
  dsimp only [OnLine]
  by_cases h : odist' A ray = 0
  · constructor
    intro
    exact lies_on_or_rev_iff_exist_real_vec_eq_smul.mpr (odist'_eq_zero_iff_exist_real_vec_eq_smul.mp h)
    intro
    assumption
  constructor
  intro k
  absurd h k
  exact (h k).elim
  dsimp only [Line.IsOn]
  intro p
  rw [Ray.toLine_carrier_eq_ray_carrier_union_rev_carrier ray] at p
  exact (odist'_eq_zero_iff_exist_real_vec_eq_smul).mpr (lies_on_or_rev_iff_exist_real_vec_eq_smul.mp p)

theorem online_iff_lies_on_line' (A : P) (dl : DirLine P) :Line.IsOn A (toLine dl) ↔ odist A dl = 0 := by
  rcases (Quotient.exists_rep dl) with ⟨ray , h0⟩
  have h2 : toLine dl = toLine ray := by
    rw[← h0]
    rfl
  rw[h2]
  have h3 : Line.IsOn A (toLine ray) ↔ OnLine A ray := (online_iff_online A ray).symm
  unfold OnLine at h3
  rw[h3]
  have h4 : odist A dl = odist A ray := by
    rw[← h0]
    rfl
  rw[h4]

theorem online_iff_lies_on_line (A : P) [DirFig α P] (df : α) : Line.IsOn A (toLine df) ↔ odist A df = 0 := by
  have h1 : toLine (toDirLine df) = toLine df := toDirLine_toLine_eq_toLine
  have h2 : odist A df = odist A (toDirLine df) := rfl
  rw[← h1,h2]
  exact online_iff_lies_on_line' A (toDirLine df)

theorem off_line_iff_not_online (A : P) [DirFig α P] (df : α) : OffLine A df ↔ ¬OnLine A df := by
  rfl

/- Relation of position of points on a ray and directed distance-/

end point_toRay

section oriented_area

theorem oarea_eq_length_mul_odist_div_two (A B C : P) [bnea : PtNe B A] : oarea A B C = (SEG A B).length * odist C (SEG_nd A B) / 2 := by
  unfold oarea
  rw [wedge_eq_length_mul_odist' A B C]
  have h0 : toDirLine (SEG_nd A B) = toDirLine (RAY A B) := rfl
  have h1 : odist C (RAY A B) = odist C (SEG_nd A B) := by
    unfold odist
    rw[h0]
  have h2 : odist C (RAY A B) = odist' C (RAY A B) := rfl
  rw [h2] at h1
  rw [h1]

theorem oarea_eq_oarea_iff_odist_eq_odist_of_ne (A B C D : P) [bnea : PtNe B A] : odist C (SEG_nd A B) = odist D (SEG_nd A B) ↔ oarea A B C = oarea A B D := by
  unfold oarea
  field_simp
  exact wedge_eq_wedge_iff_odist_eq_odist_of_ne A B C D

theorem oarea_eq_sin_mul_length_mul_length_div_two (A B C : P) [bnea : PtNe B A] [cnea : PtNe C A] : oarea A B C = (SEG A B).length * (SEG A C).length * sin (ANG B A C).value / 2 := by
  unfold oarea
  rw [wedge_eq_length_mul_length_mul_sin A B C]

theorem oarea_eq_zero_iff_colinear (A B C : P) : oarea A B C = 0 ↔ colinear A B C := by
  unfold oarea
  field_simp
  exact (colinear_iff_wedge_eq_zero A B C).symm

theorem oarea_tri_nd_ne_zero (A B C : P) (trind : ¬ colinear A B C) : oarea A B C ≠ 0 := by
  rw[← oarea_eq_zero_iff_colinear A B C] at trind
  tauto

end oriented_area

section cooperation_with_parallel

theorem odist_eq_odist_of_parallel' (A B : P) (ray : Ray P) [bnea : PtNe B A] (para : parallel (SEG_nd A B) ray) : odist A ray =odist B ray := by
  unfold odist
  have h1 : Vec.det ray.2.unitVec (VEC ray.1 B) = Vec.det ray.2.unitVec (VEC ray.1 A) + Vec.det ray.2.unitVec (VEC A B)
  · rw [← map_add, ←vec_add_vec ray.1 A B]
  have h2 : Vec.det ray.2.unitVec (VEC A B) = 0
  · unfold parallel at para
    have h3 : Dir.toProj ray.2 = (VEC_nd A B).toProj := para.symm
    have h4 : VecND.toProj ray.2.unitVecND = (VEC_nd A B).toProj := by
      rw [← h3]
      simp
    have := VecND.det_eq_zero_iff_toProj_eq_toProj (u := ray.toDir.unitVecND) (v := VEC_nd A B)
    dsimp at this
    rw [this]
    exact h4
  rw [h2] at h1
  rw [add_zero] at h1
  exact h1.symm

theorem odist_eq_odist_of_parallel {α} [DirFig α P] (A B : P) (df : α) [bnea : PtNe B A] (para : parallel (SEG_nd A B) df) : odist A df = odist B df := sorry

theorem wedge_eq_wedge_iff_parallel_of_ne_ne (A B C D : P) [bnea : PtNe B A] [dnec : PtNe D C] : (parallel (SEG_nd A B) (SEG_nd C D)) ↔ wedge A B C = wedge A B D := sorry

theorem odist_eq_odist_iff_parallel_ne {α} [DirFig α P] (A B : P) (df : α) [bnea : PtNe B A] : (parallel (SEG_nd A B) df) ↔ odist A df = odist B df := sorry

theorem oarea_eq_oarea_iff_parallel_ne (A B C D : P) [bnea : PtNe B A] [dnec : PtNe D C] : (parallel (SEG_nd A B) (SEG_nd C D)) ↔ oarea A B C = oarea A B D := sorry

end cooperation_with_parallel

scoped infix : 50 " LiesOnLeft " => IsOnLeftSide
scoped infix : 50 " LiesOnRight " => IsOnRightSide

section handside

theorem same_sign_of_parallel (A B : P) (ray : Ray P) [bnea : PtNe B A] (para : parallel (RAY A B)  ray) : odist_sign A ray = odist_sign B ray := by
  unfold odist_sign
  rw [odist_eq_odist_of_parallel' A B ray para]

theorem same_odist_sign_of_same_odist_sign (A B : P) (l : DirLine P) (signeq : odist_sign A l = odist_sign B l) : ∀ (C : P) , Seg.IsOn C (SEG A B) → odist_sign C l = odist_sign A l := sorry

theorem no_intersect_of_same_odist_sign (A B : P) (l : DirLine P) (signeq : odist_sign A l * odist_sign B l = 1) : ∀ (C : P) , Seg.IsOn C (SEG A B) → ¬ Line.IsOn C l := sorry

theorem intersect_of_diff_odist_sign (A B : P) (l : DirLine P) (signdiff : odist_sign A l * odist_sign B l = -1) : ∃ (C : P), Seg.IsOn C (SEG A B) ∧ Line.IsOn C l := sorry

lemma ne_of_isonleft_of_lieson (A B : P) (r : DirLine P) (aliesonr : Line.IsOn A r) (bliesonleft : IsOnLeftSide B r) : B ≠ A := by
  intro h0
  rw[← h0] at aliesonr
  have h1 : DirLine.toLine r = toLine r := rfl
  rw [h1, online_iff_lies_on_line] at aliesonr
  have h2 : ¬ 0 < odist B r := by
    rw [aliesonr]
    linarith
  tauto

theorem isonleft_of_isintray_of_isonleft (r : DirLine P) (A B C: P) (aliesonr : Line.IsOn A r) (bliesonleft : IsOnLeftSide B r) (conab : Ray.IsInt C (RAY A B (ne_of_isonleft_of_lieson A B r aliesonr bliesonleft))) : IsOnLeftSide C r := sorry

end handside

/- Position of two rays -/
section ray_toRay

/- Statement of his theorem should change, since ray₀.source ≠ ray₂.source. -/
theorem intersect_of_ray_on_left_iff (ray₁ ray₂ : Ray P) (h : ray₂.source ≠ ray₁.source) : let ray₀ := Ray.mk_pt_pt ray₁.source ray₂.source h; (0 < (Angle.mk ray₀ ray₁ rfl).value.toReal) ∧ ((Angle.mk ray₀ ray₁ rfl).value.toReal < (Angle.mk ray₀ ray₂ sorry).value.toReal) ∧ ((Angle.mk ray₀ ray₂ sorry).value.toReal < π) ↔ (∃ A : P, (A LiesOn ray₁) ∧ (A LiesOn ray₂) ∧ (A LiesOnLeft ray₀))  := sorry

end ray_toRay



/- Position of two lines; need a function to take the intersection of two lines (when they intersect). -/


/- A lot more theorems regarding positions -/
/- e.g. 180 degree implies colinear -/

end EuclidGeom
