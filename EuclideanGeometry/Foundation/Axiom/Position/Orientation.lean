import EuclideanGeometry.Foundation.Axiom.Linear.Colinear
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel
import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Line_trash

/- This file discuss the relative positions of points and rays on a plane. -/
noncomputable section
namespace EuclidGeom

open Classical AngValue Angle

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
    rw [sin_pos_iff_isPos] at h3
    exact h3
  rw [wedge_eq_length_mul_length_mul_sin (bnea := ⟨(ne_of_not_colinear nd).2.2⟩) (cnea := ⟨(ne_of_not_colinear nd).2.1.symm⟩)]
  intro h0
  have h3 : 0 < sin ((Angle.mk_pt_pt_pt B A C (ne_of_not_colinear nd).2.2 (ne_of_not_colinear nd).2.1.symm).value) := (sin_pos_iff_isPos (Angle.mk_pt_pt_pt B A C (ne_of_not_colinear nd).2.2 (ne_of_not_colinear nd).2.1.symm)).mpr h0
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

--LiesOnLeft and LiesOnRight and LiesOn should be correct for exact one

theorem LiesOnLeft_or_LiesOnRight_or_LiesOn (A : P) [DirFig α P] (df : α) : (IsOnLeftSide A df) ∨ (IsOnRightSide A df) ∨ (A LiesOn (toLine df)) := by
  have h : (odist A df > 0) ∨ (odist A df < 0) ∨ (odist A df = 0) := by
    by_contra h'
    have nl : ¬ (odist A df > 0) := by
      by_contra nl'
      absurd h'
      simp only [gt_iff_lt, nl', true_or]
    have nr : ¬ (odist A df < 0) := by
      by_contra nr'
      absurd h'
      simp only [gt_iff_lt, nr', true_or, or_true]
    have no : ¬ (odist A df = 0) := by
      by_contra no'
      absurd h'
      simp only [no', gt_iff_lt, lt_self_iff_false, or_true]
    simp at nl
    simp at nr
    have : odist A df = 0 := by
      linarith [nl,nr]
    absurd this
    exact no
  rcases h with l|R
  · have : IsOnLeftSide A df := by exact l
    simp only [this, true_or]
  · rcases R with r|o
    · have : IsOnRightSide A df := by exact r
      simp only [this, true_or, or_true]
    · have : Line.IsOn A (toLine df) := by
        apply (online_iff_lies_on_line A df).mpr
        exact o
      have : A LiesOn (toLine df) := by exact this
      simp only [this, or_true]

--theorem not_LiesOnRight_and_not_LiesOn_of_LiesOnLeft

--theorem not_LiesOnRight_and_not_LiesOn_of_LiesOnRight

--theorem not_LiesOnTight_and_not_LiesOnRight_of_LiesOn

theorem not_colinear_of_LiesOnLeft_or_LiesOnRight (A B C : P) [bnea : PtNe B A] (hlr : (IsOnLeftSide C (RAY A B)) ∨ (IsOnRightSide C (RAY A B))) : ¬ colinear A B C := by
  apply (not_colinear_iff_wedge_ne_zero A B C).mpr
  have hw : (wedge A B C) = (SEG A B).length * odist' C (RAY A B) := by
    exact wedge_eq_length_mul_odist' A B C
  have pos : (SEG A B).length > 0 := by
    calc
      _=(SEG_nd A B).length := by rfl
      _>0 := by apply EuclidGeom.length_pos
  rcases hlr with l|r
  · unfold IsOnLeftSide at l
    have : (wedge A B C) > 0 := by
      simp only [hw]
      positivity
    linarith
  · unfold IsOnRightSide at r
    have : -odist C (RAY A B) >0 := by
      linarith [r]
    have : -(wedge A B C) > 0 := by
      simp only [hw]
      calc
        _=-odist' C (RAY A B) * (SEG A B).length := by ring
        _>0 := by positivity
    linarith

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

scoped infix : 55 " LiesOnLeft " => IsOnLeftSide
scoped infix : 55 " LiesOnRight " => IsOnRightSide

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
theorem intersect_of_ray_on_left_iff (ray₁ ray₂ : Ray P) (h : ray₂.source ≠ ray₁.source) : let ray₀ := Ray.mk_pt_pt ray₁.source ray₂.source h; (0 < (Angle.mk_two_ray_of_eq_source ray₀ ray₁ rfl).value.toReal) ∧ ((Angle.mk_two_ray_of_eq_source ray₀ ray₁ rfl).value.toReal < (Angle.mk_two_ray_of_eq_source ray₀ ray₂ sorry).value.toReal) ∧ ((Angle.mk_two_ray_of_eq_source ray₀ ray₂ sorry).value.toReal < π) ↔ (∃ A : P, (A LiesOn ray₁) ∧ (A LiesOn ray₂) ∧ (A LiesOnLeft ray₀))  := sorry

end ray_toRay

section relative_side

/-
This section would define "LiesOn_same_side" and "LiesOn_opposite_side" for all linear figures.
(it doesn't need to distinguish the reverse)
This should be used to determine the unique graph with the least information,to lessen the dependent on graph.

Further properties of "LiesOn_same_side" and "LiesOn_opposite_side would be show along with cclock in Folder Triangle.

-/

def IsOnSameSide' (A B : P) (ray : Ray P) : Prop := ((A LiesOnLeft ray) ∧ (B LiesOnLeft ray)) ∨ ((A LiesOnRight ray) ∧ (B LiesOnRight ray))

def IsOnOppositeSide' (A B : P) (ray : Ray P) : Prop := ((A LiesOnLeft ray) ∧ (B LiesOnRight ray)) ∨ ((A LiesOnRight ray) ∧ (B LiesOnLeft ray))

theorem LiesOnSameSide'_of_toLine_eq_toLine' (A B : P) (ray ray' : Ray P) (h : ray.toLine = ray'.toLine) : IsOnSameSide' A B ray → IsOnSameSide' A B ray' := by
  have Dir : ray.toDirLine = ray'.toDirLine ∨ ray.toDirLine = ray'.toDirLine.reverse := by
    apply EuclidGeom.DirLine.eq_or_eq_rev_of_toLine_eq
    simp only [← Ray.toLine_eq_toDirLine_toLine (ray := ray),← Ray.toLine_eq_toDirLine_toLine (ray := ray')]
    exact h
  rcases Dir with same|rev
  · intro P
    rcases P with Pl|Pr
    · unfold IsOnLeftSide at Pl
      have hal₁: A LiesOnLeft ray' := by
        unfold IsOnLeftSide
        calc
          odist A ray' = odist A ray'.toDirLine := by rfl
          _=odist A ray.toDirLine := by congr 1;exact same.symm
          _=odist A ray := by rfl
          _>0 := by linarith
      have hbl₁: B LiesOnLeft ray' := by
        unfold IsOnLeftSide
        calc
          odist B ray' = odist B ray'.toDirLine := by rfl
          _=odist B ray.toDirLine := by congr 1;exact same.symm
          _=odist B ray := by rfl
          _>0 := by linarith
      unfold IsOnSameSide'
      simp only [hal₁, hbl₁, and_self, true_or]
    · unfold IsOnRightSide at Pr
      have har₁: A LiesOnRight ray' := by
        unfold IsOnRightSide
        calc
          odist A ray' = odist A ray'.toDirLine := by rfl
          _=odist A ray.toDirLine := by congr 1;exact same.symm
          _=odist A ray := by rfl
          _<0 := by linarith
      have hbr₁: B LiesOnRight ray' := by
        unfold IsOnRightSide
        calc
          odist B ray' = odist B ray'.toDirLine := by rfl
          _=odist B ray.toDirLine := by congr 1;exact same.symm
          _=odist B ray := by rfl
          _<0 := by linarith
      unfold IsOnSameSide'
      simp only [har₁, hbr₁, and_self, or_true]
  · intro P
    rcases P with Pl|Pr
    · unfold IsOnLeftSide at Pl
      have har₂: A LiesOnRight ray' := by
        unfold IsOnRightSide
        calc
          odist A ray' = odist A ray'.toDirLine := by rfl
          _=-odist A ray'.toDirLine.reverse := by
            simp only [odist_reverse_eq_neg_odist'' (dl := ray'.toDirLine), neg_neg]
          _=-odist A ray.toDirLine := by congr;exact id rev.symm
          _=-odist A ray := by rfl
          _<0 := by linarith
      have hbr₂: B LiesOnRight ray' := by
        unfold IsOnRightSide
        calc
          odist B ray' = odist B ray'.toDirLine := by rfl
          _=-odist B ray'.toDirLine.reverse := by
            simp only [odist_reverse_eq_neg_odist'' (dl := ray'.toDirLine), neg_neg]
          _=-odist B ray.toDirLine := by congr;exact id rev.symm
          _=-odist B ray := by rfl
          _<0 := by linarith
      unfold IsOnSameSide'
      simp only [har₂, hbr₂, and_self, or_true]
    · unfold IsOnRightSide at Pr
      have hal₂: A LiesOnLeft ray' := by
        unfold IsOnLeftSide
        calc
          odist A ray' = odist A ray'.toDirLine := by rfl
          _=-odist A ray'.toDirLine.reverse := by
            simp only [odist_reverse_eq_neg_odist'' (dl := ray'.toDirLine), neg_neg]
          _=-odist A ray.toDirLine := by congr;exact id rev.symm
          _=-odist A ray := by rfl
          _>0 := by linarith
      have hbl₂: B LiesOnLeft ray' := by
        unfold IsOnLeftSide
        calc
          odist B ray' = odist B ray'.toDirLine := by rfl
          _=-odist B ray'.toDirLine.reverse := by
            simp only [odist_reverse_eq_neg_odist'' (dl := ray'.toDirLine), neg_neg]
          _=-odist B ray.toDirLine := by congr;exact id rev.symm
          _=-odist B ray := by rfl
          _>0 := by linarith
      unfold IsOnSameSide'
      simp only [hal₂, hbl₂, and_self, true_or]

theorem LiesOnSameSide'_of_toLine_eq_toLine (A B : P) (ray ray' : Ray P) (h : ray.toLine = ray'.toLine) : IsOnSameSide' A B ray = IsOnSameSide' A B ray' := by
  simp only [eq_iff_iff]
  constructor
  · apply LiesOnSameSide'_of_toLine_eq_toLine' (h := h)
  · apply LiesOnSameSide'_of_toLine_eq_toLine' (h := h.symm)

theorem LiesOnOppositeSide'_of_toLine_eq_toLine' (A B : P) (ray ray' : Ray P) (h : ray.toLine = ray'.toLine) : IsOnOppositeSide' A B ray → IsOnOppositeSide' A B ray' := by
  have Dir : ray.toDirLine = ray'.toDirLine ∨ ray.toDirLine = ray'.toDirLine.reverse := by
    apply EuclidGeom.DirLine.eq_or_eq_rev_of_toLine_eq
    simp only [← Ray.toLine_eq_toDirLine_toLine (ray := ray),← Ray.toLine_eq_toDirLine_toLine (ray := ray')]
    exact h
  rcases Dir with same|rev
  · intro P
    rcases P with Pl|Pr
    · unfold IsOnLeftSide at Pl
      unfold IsOnRightSide at Pl
      have hal₁: A LiesOnLeft ray' := by
        unfold IsOnLeftSide
        calc
          odist A ray' = odist A ray'.toDirLine := by rfl
          _=odist A ray.toDirLine := by congr 1;exact same.symm
          _=odist A ray := by rfl
          _>0 := by linarith
      have hbr₁: B LiesOnRight ray' := by
        unfold IsOnRightSide
        calc
          odist B ray' = odist B ray'.toDirLine := by rfl
          _=odist B ray.toDirLine := by congr 1;exact same.symm
          _=odist B ray := by rfl
          _<0 := by linarith
      unfold IsOnOppositeSide'
      simp only [hal₁, hbr₁, and_self, true_or]
    · unfold IsOnRightSide at Pr
      unfold IsOnLeftSide at Pr
      have har₁: A LiesOnRight ray' := by
        unfold IsOnRightSide
        calc
          odist A ray' = odist A ray'.toDirLine := by rfl
          _=odist A ray.toDirLine := by congr 1;exact same.symm
          _=odist A ray := by rfl
          _<0 := by linarith
      have hbl₁: B LiesOnLeft ray' := by
        unfold IsOnLeftSide
        calc
          odist B ray' = odist B ray'.toDirLine := by rfl
          _=odist B ray.toDirLine := by congr 1;exact same.symm
          _=odist B ray := by rfl
          _>0 := by linarith
      unfold IsOnOppositeSide'
      simp only [har₁, hbl₁, and_self, or_true]

  · intro P
    rcases P with Pl|Pr
    · unfold IsOnLeftSide at Pl
      unfold IsOnRightSide at Pl
      have har₂: A LiesOnRight ray' := by
        unfold IsOnRightSide
        calc
          odist A ray' = odist A ray'.toDirLine := by rfl
          _=-odist A ray'.toDirLine.reverse := by
            simp only [odist_reverse_eq_neg_odist'' (dl := ray'.toDirLine), neg_neg]
          _=-odist A ray.toDirLine := by congr;exact id rev.symm
          _=-odist A ray := by rfl
          _<0 := by linarith
      have hbr₂: B LiesOnLeft ray' := by
        unfold IsOnLeftSide
        calc
          odist B ray' = odist B ray'.toDirLine := by rfl
          _=-odist B ray'.toDirLine.reverse := by
            simp only [odist_reverse_eq_neg_odist'' (dl := ray'.toDirLine), neg_neg]
          _=-odist B ray.toDirLine := by congr;exact id rev.symm
          _=-odist B ray := by rfl
          _>0 := by linarith
      unfold IsOnOppositeSide'
      simp only [har₂, hbr₂, and_self, or_true]
    · unfold IsOnRightSide at Pr
      unfold IsOnLeftSide at Pr
      have hal₂: A LiesOnLeft ray' := by
        unfold IsOnLeftSide
        calc
          odist A ray' = odist A ray'.toDirLine := by rfl
          _=-odist A ray'.toDirLine.reverse := by
            simp only [odist_reverse_eq_neg_odist'' (dl := ray'.toDirLine), neg_neg]
          _=-odist A ray.toDirLine := by congr;exact id rev.symm
          _=-odist A ray := by rfl
          _>0 := by linarith
      have hbl₂: B LiesOnRight ray' := by
        unfold IsOnRightSide
        calc
          odist B ray' = odist B ray'.toDirLine := by rfl
          _=-odist B ray'.toDirLine.reverse := by
            simp only [odist_reverse_eq_neg_odist'' (dl := ray'.toDirLine), neg_neg]
          _=-odist B ray.toDirLine := by congr;exact id rev.symm
          _=-odist B ray := by rfl
          _<0 := by linarith
      unfold IsOnOppositeSide'
      simp only [hal₂, hbl₂, and_self, true_or]

theorem LiesOnOppositeSide'_of_toLine_eq_toLine (A B : P) (ray ray' : Ray P) (h : ray.toLine = ray'.toLine) : IsOnOppositeSide' A B ray = IsOnOppositeSide' A B ray' := by
  simp only [eq_iff_iff]
  constructor
  · apply LiesOnOppositeSide'_of_toLine_eq_toLine' (h := h)
  · apply LiesOnOppositeSide'_of_toLine_eq_toLine' (h := h.symm)

def IsOnSameSide {α} [ProjFig α P] (A B : P) (l : α) : Prop := Quotient.lift (s := same_extn_line.setoid) (fun ray : Ray P => IsOnSameSide' A B ray) (fun _ _ h => LiesOnSameSide'_of_toLine_eq_toLine A B _ _ (Quotient.sound h) ) (toLine l)

def IsOnOppositeSide {α} [ProjFig α P] (A B : P) (l : α) : Prop := Quotient.lift (s := same_extn_line.setoid) (fun ray : Ray P => IsOnOppositeSide' A B ray) (fun _ _ h => LiesOnOppositeSide'_of_toLine_eq_toLine A B _ _ (Quotient.sound h) ) (toLine l)

--symm and trans of same_side

theorem IsOnSameSide_symm' (A B : P) (ray : Ray P) : IsOnSameSide A B ray →  IsOnSameSide B A ray := by
  unfold IsOnSameSide
  unfold IsOnSameSide'
  intro P
  rcases P with l|r
  · show (B LiesOnLeft ray ∧ A LiesOnLeft ray) ∨ (B LiesOnRight ray ∧ A LiesOnRight ray)
    simp only [l.2, l.1, and_self, true_or]
  · show (B LiesOnLeft ray ∧ A LiesOnLeft ray) ∨ (B LiesOnRight ray ∧ A LiesOnRight ray)
    simp only [r.2, r.1, and_self, or_true]

theorem IsOnSameSide_symm'' (A B : P) (l : Line P) : IsOnSameSide A B l  →  IsOnSameSide B A l := by
    rcases (Quotient.exists_rep l) with ⟨ray , h0⟩
    intro P
    simp only [← h0] at P
    have h₁ : IsOnSameSide A B ray := by
      exact P
    have h₂ : IsOnSameSide B A ray := by
      apply IsOnSameSide_symm' A B ray
      exact h₁
    simp only [← h0]
    exact h₂

theorem IsOnSameSide_symm {α} [ProjFig α P] (A B : P) (l : α) : IsOnSameSide A B l = IsOnSameSide B A l := by
  have h₁ : IsOnSameSide A B l = IsOnSameSide A B (toLine l) := by rfl
  have h₂ : IsOnSameSide B A l = IsOnSameSide B A (toLine l) := by rfl
  simp only [eq_iff_iff]
  simp only [h₁,h₂]
  constructor
  · exact IsOnSameSide_symm'' A B (toLine l)
  · exact IsOnSameSide_symm'' B A (toLine l)


theorem IsOnOppositeSide_symm' (A B : P) (ray : Ray P) : IsOnOppositeSide A B ray →  IsOnOppositeSide B A ray := by
  unfold IsOnOppositeSide
  unfold IsOnOppositeSide'
  intro P
  rcases P with l|r
  · show (B LiesOnLeft ray ∧ A LiesOnRight ray) ∨ (B LiesOnRight ray ∧ A LiesOnLeft ray)
    simp only [l.2, l.1, and_self, or_true]
  · show (B LiesOnLeft ray ∧ A LiesOnRight ray) ∨ (B LiesOnRight ray ∧ A LiesOnLeft ray)
    simp only [r.2, r.1, and_self, true_or]

theorem IsOnOppositeSide_symm'' (A B : P) (l : Line P) : IsOnOppositeSide A B l  →  IsOnOppositeSide B A l := by
    rcases (Quotient.exists_rep l) with ⟨ray , h0⟩
    intro P
    simp only [← h0] at P
    have h₁ : IsOnOppositeSide A B ray := by
      exact P
    have h₂ : IsOnOppositeSide B A ray := by
      apply IsOnOppositeSide_symm' A B ray
      exact h₁
    simp only [← h0]
    exact h₂

theorem IsOnOppositeSide_symm {α} [ProjFig α P] (A B : P) (l : α) : IsOnOppositeSide A B l = IsOnOppositeSide B A l := by
  have h₁ : IsOnOppositeSide A B l = IsOnOppositeSide A B (toLine l) := by rfl
  have h₂ : IsOnOppositeSide B A l = IsOnOppositeSide B A (toLine l) := by rfl
  simp only [eq_iff_iff]
  simp only [h₁,h₂]
  constructor
  · exact IsOnOppositeSide_symm'' A B (toLine l)
  · exact IsOnOppositeSide_symm'' B A (toLine l)

/-
trans:
Basic properties:
  LiesOn_same_side of LiesOn_same_side and LiesOn_same_side
  LiesOn_opposite_side of LiesOn_same_side and LiesOn_opposite_side
  LiesOn_opposite_side of LiesOn_opposite_side and LiesOn_same_side
-/

theorem IsOnSameSide_trans' (A B C : P) (l : Line P) (h₁ : IsOnSameSide A B l) (h₂ : IsOnSameSide B C l) : IsOnSameSide A C l := by
  rcases (Quotient.exists_rep l) with ⟨ray , h0⟩
  simp only [← h0] at h₁
  simp only [← h0] at h₂
  have h1 : IsOnSameSide A B ray := by exact h₁
  have h2 : IsOnSameSide B C ray := by exact h₂
  have : IsOnSameSide A C ray = IsOnSameSide A C l := by
    simp only [← h0]
    rfl
  simp only [←this]
  --Converted to ray
  unfold IsOnSameSide
  unfold IsOnSameSide'
  unfold IsOnSameSide at h1
  unfold IsOnSameSide' at h1
  unfold IsOnSameSide at h2
  unfold IsOnSameSide' at h2
  show A LiesOnLeft ray ∧ C LiesOnLeft ray ∨ A LiesOnRight ray ∧ C LiesOnRight ray
  rcases h1 with l|r
  · rcases h2 with l'|r'
    · simp only [l.1, l'.2, and_self, true_or]
    · absurd r'
      have : ¬ B LiesOnRight ray := by
        unfold IsOnRightSide
        unfold IsOnLeftSide at l
        linarith [l.2]
      simp only [this, false_and, not_false_eq_true]
  · rcases h2 with l'|r'
    · absurd l'
      have : ¬ B LiesOnLeft ray := by
        unfold IsOnLeftSide
        unfold IsOnRightSide at r
        linarith [r.2]
      simp only [this, false_and, not_false_eq_true]
    · simp only [r.1, r'.2, and_self, or_true]

theorem IsOnSameSide_trans {α} [ProjFig α P] (A B C : P) (l : α) (h₁ : IsOnSameSide A B l) (h₂ : IsOnSameSide B C l) : IsOnSameSide A C l := by
  have h1 : IsOnSameSide A B (toLine l) = IsOnSameSide A B l := by rfl
  have h2 : IsOnSameSide B C (toLine l) = IsOnSameSide B C l := by rfl
  have h3 : IsOnSameSide A C (toLine l) = IsOnSameSide A C l := by rfl
  simp only [← h1] at h₁
  simp only [← h2] at h₂
  simp only [← h3]
  apply IsOnSameSide_trans' A B C (toLine l)
  · exact h₁
  · exact h₂

theorem IsOnOppositeSide_of_IsOnOppositeSide_and_IsOnSameSide' (A B C : P) (l : Line P) (h₁ : IsOnSameSide A B l) (h₂ : IsOnOppositeSide B C l) : IsOnOppositeSide A C l := by
  rcases (Quotient.exists_rep l) with ⟨ray , h0⟩
  simp only [← h0] at h₁
  simp only [← h0] at h₂
  have h1 : IsOnSameSide A B ray := by exact h₁
  have h2 : IsOnOppositeSide B C ray := by exact h₂
  have : IsOnOppositeSide A C ray = IsOnOppositeSide A C l := by
    simp only [← h0]
    rfl
  simp only [←this]
  --Converted to ray
  unfold IsOnOppositeSide
  unfold IsOnOppositeSide'
  unfold IsOnSameSide at h1
  unfold IsOnSameSide' at h1
  unfold IsOnOppositeSide at h2
  unfold IsOnOppositeSide' at h2
  show A LiesOnLeft ray ∧ C LiesOnRight ray ∨ A LiesOnRight ray ∧ C LiesOnLeft ray
  rcases h1 with l|r
  · rcases h2 with l'|r'
    · simp only [l.1, l'.2, and_self, true_or]
    · absurd r'
      have : ¬ B LiesOnRight ray := by
        unfold IsOnRightSide
        unfold IsOnLeftSide at l
        linarith [l.2]
      simp only [this, false_and, not_false_eq_true]
  · rcases h2 with l'|r'
    · absurd l'
      have : ¬ B LiesOnLeft ray := by
        unfold IsOnLeftSide
        unfold IsOnRightSide at r
        linarith [r.2]
      simp only [this, false_and, not_false_eq_true]
    · simp only [r.1, r'.2, and_self, or_true]

theorem IsOnOppositeSide_of_IsOnOppositeSide_and_IsOnSameSide {α} [ProjFig α P] (A B C : P) (l : α) (h₁ : IsOnSameSide A B l) (h₂ : IsOnOppositeSide B C l) : IsOnOppositeSide A C l := by
  have h1 : IsOnSameSide A B (toLine l) = IsOnSameSide A B l := by rfl
  have h2 : IsOnOppositeSide B C (toLine l) = IsOnOppositeSide B C l := by rfl
  have h3 : IsOnOppositeSide A C (toLine l) = IsOnOppositeSide A C l := by rfl
  simp only [← h1] at h₁
  simp only [← h2] at h₂
  simp only [← h3]
  apply IsOnOppositeSide_of_IsOnOppositeSide_and_IsOnSameSide' A B C (toLine l)
  · exact h₁
  · exact h₂

theorem IsOnOppositeSide_of_IsOnSameSide_and_IsOnOppositeSide {α} [ProjFig α P] (A B C : P) (l : α) (h₁ : IsOnOppositeSide A B l) (h₂ : IsOnSameSide B C l) : IsOnOppositeSide A C l := by
  have h1 : IsOnOppositeSide B A l = IsOnOppositeSide A B l := by
    exact IsOnOppositeSide_symm B A l
  have h2 : IsOnSameSide C B l = IsOnSameSide B C l := by
    exact IsOnSameSide_symm C B l
  simp only [←h1] at h₁
  simp only [←h2] at h₂
  have h : IsOnOppositeSide A C l = IsOnOppositeSide C A l := by
    exact IsOnOppositeSide_symm A C l
  simp only [h]
  apply IsOnOppositeSide_of_IsOnOppositeSide_and_IsOnSameSide C B A l
  · exact h₂
  · exact h₁

theorem IsOnSameSide_of_IsOnOppositeSide_and_IsOnOppositeSide' (A B C : P) (l : Line P) (h₁ : IsOnOppositeSide A B l) (h₂ : IsOnOppositeSide B C l) : IsOnSameSide A C l := by
  rcases (Quotient.exists_rep l) with ⟨ray , h0⟩
  simp only [← h0] at h₁
  simp only [← h0] at h₂
  have h1 : IsOnOppositeSide A B ray := by exact h₁
  have h2 : IsOnOppositeSide B C ray := by exact h₂
  have : IsOnSameSide A C ray = IsOnSameSide A C l := by
    simp only [← h0]
    rfl
  simp only [←this]
  --Converted to ray
  unfold IsOnSameSide
  unfold IsOnSameSide'
  unfold IsOnOppositeSide at h1
  unfold IsOnOppositeSide' at h1
  unfold IsOnOppositeSide at h2
  unfold IsOnOppositeSide' at h2
  show A LiesOnLeft ray ∧ C LiesOnLeft ray ∨ A LiesOnRight ray ∧ C LiesOnRight ray
  rcases h1 with l|r
  · rcases h2 with l'|r'
    · absurd l'
      have : ¬ B LiesOnLeft ray := by
        unfold IsOnLeftSide
        unfold IsOnRightSide at l
        linarith [l.2]
      simp only [this, false_and, not_false_eq_true]
    · simp only [l.1, r'.2, and_self, true_or]
  · rcases h2 with l'|r'
    · simp only [r.1, l'.2, and_self, or_true]
    · absurd r'
      have : ¬ B LiesOnRight ray := by
        unfold IsOnRightSide
        unfold IsOnLeftSide at r
        linarith [r.2]
      simp only [this, false_and, not_false_eq_true]

theorem IsOnSameSide_of_IsOnOppositeSide_and_IsOnOppositeSide {α} [ProjFig α P] (A B C : P) (l : α) (h₁ : IsOnOppositeSide A B l) (h₂ : IsOnOppositeSide B C l) : IsOnSameSide A C l := by
  have h1 : IsOnOppositeSide A B (toLine l) = IsOnOppositeSide A B l := by rfl
  have h2 : IsOnOppositeSide B C (toLine l) = IsOnOppositeSide B C l := by rfl
  have h3 : IsOnSameSide A C (toLine l) = IsOnSameSide A C l := by rfl
  simp only [← h1] at h₁
  simp only [← h2] at h₂
  simp only [← h3]
  apply IsOnSameSide_of_IsOnOppositeSide_and_IsOnOppositeSide' A B C (toLine l)
  · exact h₁
  · exact h₂

--this theorem is for the moving of LiesOnLeftSide by IsOnSameSide

theorem LiesOnLeft_iff_LiesOnLeft_of_IsOnSameSide' (A B : P) (dl : DirLine P) (h : IsOnSameSide A B dl) : A LiesOnLeft dl → B LiesOnLeft dl := by
  intro P
  rcases (Quotient.exists_rep dl) with ⟨ray , h0⟩
  simp only [← h0] at P
  simp only [← h0]
  have : A LiesOnLeft ray := by
    exact P
  have h₁ : ¬ A LiesOnRight ray := by
    unfold IsOnRightSide
    unfold IsOnLeftSide at this
    linarith
  have h₂ : IsOnSameSide A B ray := by
    simp only [← h0] at h
    exact h
  rcases h₂ with l|r
  · exact l.2
  · absurd r
    simp only [h₁, false_and, not_false_eq_true]

theorem LiesOnLeft_iff_LiesOnLeft_of_IsOnSameSide (A B : P) (dl : DirLine P) (h : IsOnSameSide A B dl) : A LiesOnLeft dl = B LiesOnLeft dl := by
  simp only [eq_iff_iff]
  have h' : IsOnSameSide B A dl := by
    apply (IsOnSameSide_symm A B dl).mp
    exact h
  constructor
  · exact LiesOnLeft_iff_LiesOnLeft_of_IsOnSameSide' (h:=h)
  · exact LiesOnLeft_iff_LiesOnLeft_of_IsOnSameSide' (h:=h')

theorem LiesOnLeft_iff_LiesOnLeft_rev_of_IsOnOppositeSide' (A B : P) (dl : DirLine P) (h : IsOnOppositeSide A B dl) : A LiesOnLeft dl → B LiesOnLeft dl.reverse := by
  intro P
  rcases (Quotient.exists_rep dl) with ⟨ray , h0⟩
  simp only [← h0] at P
  simp only [← h0]
  have : A LiesOnLeft ray := by
    exact P
  have h₁ : ¬ A LiesOnRight ray := by
    unfold IsOnRightSide
    unfold IsOnLeftSide at this
    linarith
  have h₂ : IsOnOppositeSide A B ray := by
    simp only [← h0] at h
    exact h
  rcases h₂ with l|r
  · have : odist B ray.reverse >0 := by
      calc
        _=-odist B ray := by apply odist_reverse_eq_neg_odist B ray
        _>0 := by
          simp
          unfold IsOnRightSide at l
          exact l.2
    exact this
  · absurd r
    simp [h₁]

theorem LiesOnLeft_iff_LiesOnLeft_rev_of_IsOnOppositeSide (A B : P) (dl : DirLine P) (h : IsOnOppositeSide A B dl) : A LiesOnLeft dl = B LiesOnLeft dl.reverse := by
  simp only [eq_iff_iff]
  have h' : IsOnOppositeSide B A dl.reverse := by
    apply (IsOnOppositeSide_symm A B dl.reverse).mp
    have : dl.reverse.toLine = dl.toLine := by
      exact EuclidGeom.DirLine.rev_toLine_eq_toLine dl
    have eq : IsOnOppositeSide A B dl.reverse = IsOnOppositeSide A B dl := by
      calc
        IsOnOppositeSide A B dl.reverse = IsOnOppositeSide A B dl.reverse.toLine := by rfl
        _= IsOnOppositeSide A B dl.toLine := by simp only [this]
        _= IsOnOppositeSide A B dl := by rfl
    simp only [eq]
    exact h
  constructor
  · exact LiesOnLeft_iff_LiesOnLeft_rev_of_IsOnOppositeSide' (h:=h)
  · have h0 : B LiesOnLeft dl.reverse → A LiesOnLeft dl.reverse.reverse := by
      exact LiesOnLeft_iff_LiesOnLeft_rev_of_IsOnOppositeSide' (h:=h')
    have : dl.reverse.reverse = dl := by
      exact  EuclidGeom.DirLine.rev_rev_eq_self
    simp [this] at h0
    exact h0

theorem not_colinear_of_IsOnSameSide (A B C D : P) [bnea : PtNe B A] (h : IsOnSameSide C D (RAY A B)) : (¬ colinear A B C) ∧ (¬ colinear A B D) := by
  have hlr : (IsOnLeftSide C (RAY A B)) ∨ (IsOnRightSide C (RAY A B)) := by
    rcases h with l|r
    · simp only [l.1, true_or]
    · simp only [r.1, or_true]
  have hlr' : (IsOnLeftSide D (RAY A B)) ∨ (IsOnRightSide D (RAY A B)) := by
    rcases h with l|r
    · simp only [l.2, true_or]
    · simp only [r.2, or_true]
  have c : ¬ colinear A B C := by
    apply not_colinear_of_LiesOnLeft_or_LiesOnRight
    exact hlr
  have d : ¬ colinear A B D := by
    apply not_colinear_of_LiesOnLeft_or_LiesOnRight
    exact hlr'
  simp only [c, not_false_eq_true, d, and_self]

theorem not_colinear_of_IsOnOppositeSide (A B C D : P) [bnea : PtNe B A] (h : IsOnOppositeSide C D (RAY A B)) : (¬ colinear A B C) ∧ (¬ colinear A B D) := by
  have hlr : (IsOnLeftSide C (RAY A B)) ∨ (IsOnRightSide C (RAY A B)) := by
    rcases h with l|r
    · simp only [l.1, true_or]
    · simp only [r.1, or_true]
  have hlr' : (IsOnLeftSide D (RAY A B)) ∨ (IsOnRightSide D (RAY A B)) := by
    rcases h with l|r
    · simp only [l.2, or_true]
    · simp only [r.2, true_or]
  have c : ¬ colinear A B C := by
    apply not_colinear_of_LiesOnLeft_or_LiesOnRight
    exact hlr
  have d : ¬ colinear A B D := by
    apply not_colinear_of_LiesOnLeft_or_LiesOnRight
    exact hlr'
  simp only [c, not_false_eq_true, d, and_self]

end relative_side

/- Position of two lines; need a function to take the intersection of two lines (when they intersect). -/


/- A lot more theorems regarding positions -/
/- e.g. 180 degree implies colinear -/

end EuclidGeom
