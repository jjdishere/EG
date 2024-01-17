import EuclideanGeometry.Foundation.Axiom.Linear.Collinear
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

theorem collinear_iff_wedge_eq_zero (A B C : P) : (collinear A B C) ↔ (wedge A B C = 0) := by
  dsimp only [wedge]
  by_cases h : PtNe B A
  · have vecabnd : VEC A B ≠ 0 := by
      exact (ne_iff_vec_ne_zero A B).mp h.out
    rw [← Vec.det_skew, neg_eq_zero, Vec.det_eq_zero_iff_eq_smul_right]
    simp only [vecabnd, false_or]
    constructor
    · intro k
      exact collinear_iff_eq_smul_vec_of_ne.mp k
    · intro k
      exact collinear_iff_eq_smul_vec_of_ne.mpr k
  · simp [PtNe, fact_iff] at h
    have vecab0 : VEC A B = 0 := by
      exact (eq_iff_vec_eq_zero A B).mp h
    constructor
    intro
    field_simp [vecab0]
    intro
    rw [h]
    exact triv_collinear A C

theorem not_collinear_iff_wedge_ne_zero (A B C : P) : (¬ collinear A B C) ↔ (wedge A B C ≠ 0) := by
  rw [collinear_iff_wedge_eq_zero]

theorem wedge_pos_iff_angle_pos (A B C : P) (nd : ¬collinear A B C) : (0 < wedge A B C) ↔ (Angle.mk_pt_pt_pt B A C (ne_of_not_collinear nd).2.2 (ne_of_not_collinear nd).2.1.symm).value.IsPos := by
  have h1 : 0 < dist A B := by
      have abnd : (SEG A B).IsND := (ne_of_not_collinear nd).2.2
      exact dist_pos.mpr (abnd.symm)
  have h2 : 0 < dist A C := by
      have acnd : (SEG A C).IsND := (ne_of_not_collinear nd).2.1.symm
      exact dist_pos.mpr (acnd.symm)
  constructor
  · intro h0
    rw [wedge_eq_length_mul_length_mul_sin (bnea := ⟨(ne_of_not_collinear nd).2.2⟩) (cnea := ⟨(ne_of_not_collinear nd).2.1.symm⟩)] at h0
    have h3 : 0 < sin (Angle.mk_pt_pt_pt B A C (ne_of_not_collinear nd).2.2 (ne_of_not_collinear nd).2.1.symm).value := by
      field_simp at h0
      exact h0
    rw [sin_pos_iff_isPos] at h3
    exact h3
  rw [wedge_eq_length_mul_length_mul_sin (bnea := ⟨(ne_of_not_collinear nd).2.2⟩) (cnea := ⟨(ne_of_not_collinear nd).2.1.symm⟩)]
  field_simp
  exact sin_pos_iff_isPos.mpr

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
  have h2 : (VEC_nd ray.source A).1 = VEC ray.source A := rfl
  have h3 : ‖ray.toDir.unitVecND‖ = 1 := by rw [Dir.norm_unitVecND]
  have h4 : (SEG ray.source A).length = ‖VEC_nd ray.source A‖ := Seg.length_eq_norm_toVec
  rw [← h2, ← VecND.norm_mul_sin ray.2.unitVecND (VEC_nd ray.source A), h3, h4, one_mul]
  simp only [mk_ray_pt_dir₂, mk_ray_pt_dir₁, mul_eq_mul_left_iff, VecND.norm_ne_zero, or_false]
  congr
  nth_rw 2 [← Dir.unitVecND_toDir ray.toDir]
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

theorem online_iff_lies_on_line (A : P) [DirFig α P] (df : α) :  A LiesOn (toLine df) ↔ odist A df = 0 := by
  have h1 : toLine (toDirLine df) = toLine df := toDirLine_toLine_eq_toLine
  have h2 : odist A df = odist A (toDirLine df) := rfl
  rw[← h1,h2]
  exact online_iff_lies_on_line' A (toDirLine df)

theorem off_line_iff_not_online (A : P) [DirFig α P] (df : α) : OffLine A df ↔ ¬OnLine A df := by
  rfl

--LiesOnLeft and LiesOnRight and LiesOn should be correct for exact one

theorem LiesOn_or_LiesOnLeft_or_LiesOnRight (A : P) [DirFig α P] (df : α) : (A LiesOn (toLine df)) ∨ (IsOnLeftSide A df) ∨ (IsOnRightSide A df) := by
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
  rcases h with l|ro
  · have : IsOnLeftSide A df := by exact l
    simp only [this, true_or, or_true]
  · rcases ro with r|o
    · have : IsOnRightSide A df := by exact r
      simp only [this, true_or, or_true]
    · have : A LiesOn (toLine df) := by
        apply (online_iff_lies_on_line A df).mpr
        exact o
      simp only [this, true_or]


theorem not_LiesOnRight_and_not_LiesOn_Line_of_LiesOnLeft (A : P) [DirFig α P] (df : α) (h : IsOnLeftSide A df) : (¬ IsOnRightSide A df) ∧ (¬ A LiesOn (toLine df)) := by
  have nr : ¬ IsOnRightSide A df := by
    unfold IsOnRightSide
    unfold IsOnLeftSide at h
    simp only [not_lt]
    linarith
  have no : ¬ A LiesOn (toLine df) := by
    apply (online_iff_lies_on_line A df).not.mpr
    unfold IsOnLeftSide at h
    linarith
  simp only [nr, not_false_eq_true, no, and_self]

theorem not_LiesOnLeft_and_not_LiesOn_Line_of_LiesOnRight (A : P) [DirFig α P] (df : α) (h : IsOnRightSide A df) : (¬ IsOnLeftSide A df) ∧ (¬ A LiesOn (toLine df)) := by
  have nl : ¬ IsOnLeftSide A df := by
    unfold IsOnLeftSide
    unfold IsOnRightSide at h
    simp only [not_lt]
    linarith
  have no : ¬ A LiesOn (toLine df) := by
    apply (online_iff_lies_on_line A df).not.mpr
    unfold IsOnRightSide at h
    linarith
  simp only [nl, not_false_eq_true, no, and_self]

theorem not_LiesOnLeftt_and_not_LiesOnRight_of_LiesOn_Line (A : P) [DirFig α P] (df : α) (h : A LiesOn (toLine df)) : (¬ IsOnLeftSide A df) ∧ (¬ IsOnRightSide A df) := by
  have o : odist A df = 0 := by
    apply (online_iff_lies_on_line A df).mp
    exact h
  have nl : ¬ IsOnLeftSide A df := by
    unfold IsOnLeftSide
    linarith
  have nr : ¬ IsOnRightSide A df := by
    unfold IsOnRightSide
    linarith
  simp only [nl, not_false_eq_true, nr, and_self]

lemma lies_on_of_lies_on_toline (A : P) [DirFig α P] (df : α) : A LiesOn df → A LiesOn (toLine df) := by
  apply ProjFig.carrier_subset_toLine

theorem not_LiesOnRight_and_not_LiesOn_of_LiesOnLeft (A : P) [DirFig α P] (df : α) (h : IsOnLeftSide A df) : (¬ IsOnRightSide A df) ∧ (¬ A LiesOn df) := by
  have nr : ¬ IsOnRightSide A df := by
    exact (not_LiesOnRight_and_not_LiesOn_Line_of_LiesOnLeft A df h).1
  have no' : ¬ A LiesOn (toLine df) := by
    exact (not_LiesOnRight_and_not_LiesOn_Line_of_LiesOnLeft A df h).2
  have no : ¬ A LiesOn df := by
    apply (lies_on_of_lies_on_toline A df).mt
    exact no'
  simp only [nr, not_false_eq_true, no, and_self]

theorem not_LiesOnLeft_and_not_LiesOn_of_LiesOnRight (A : P) [DirFig α P] (df : α) (h : IsOnRightSide A df) : (¬ IsOnLeftSide A df) ∧ (¬ A LiesOn df) := by
  have nl : ¬ IsOnLeftSide A df := by
    exact (not_LiesOnLeft_and_not_LiesOn_Line_of_LiesOnRight A df h).1
  have no' : ¬ A LiesOn (toLine df) := by
    exact (not_LiesOnLeft_and_not_LiesOn_Line_of_LiesOnRight A df h).2
  have no : ¬ A LiesOn df := by
    apply (lies_on_of_lies_on_toline A df).mt
    exact no'
  simp only [nl, not_false_eq_true, no, and_self]

theorem not_LiesOnLeft_and_not_LiesOnRight_of_LiesOn (A : P) [DirFig α P] (df : α) (h : A LiesOn df) : (¬ IsOnLeftSide A df) ∧ (¬ IsOnRightSide A df) := by
  have o : A LiesOn (toLine df) := by
    apply lies_on_of_lies_on_toline
    exact h
  exact not_LiesOnLeftt_and_not_LiesOnRight_of_LiesOn_Line A df o

theorem LiesOnLeft_or_LiesOnRight_of_not_LiesOn {A : P} [DirFig α P] {df : α} (h : ¬ A LiesOn (toLine df)): (IsOnLeftSide A df) ∨ (IsOnRightSide A df) := by
  have : (A LiesOn (toLine df)) ∨ (IsOnLeftSide A df) ∨ (IsOnRightSide A df) := by
    exact LiesOn_or_LiesOnLeft_or_LiesOnRight A df
  rcases this with o|lr
  · absurd h
    exact o
  · exact lr


theorem not_collinear_of_LiesOnLeft_or_LiesOnRight (A B C : P) [bnea : PtNe B A] (hlr : (IsOnLeftSide C (RAY A B)) ∨ (IsOnRightSide C (RAY A B))) : ¬ collinear A B C := by
  apply (not_collinear_iff_wedge_ne_zero A B C).mpr
  have hw : (wedge A B C) = (SEG A B).length * odist' C (RAY A B) :=
    wedge_eq_length_mul_odist' A B C
  have _ : (SEG A B).length > 0 := (SEG_nd A B).length_pos
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

theorem oarea_eq_zero_iff_collinear (A B C : P) : oarea A B C = 0 ↔ collinear A B C := by
  unfold oarea
  field_simp
  exact (collinear_iff_wedge_eq_zero A B C).symm

theorem oarea_tri_nd_ne_zero (A B C : P) (trind : ¬ collinear A B C) : oarea A B C ≠ 0 := by
  rw[← oarea_eq_zero_iff_collinear A B C] at trind
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

--theorem odist_eq_odist_of_parallel {α} [DirFig α P] (A B : P) (df : α) [bnea : PtNe B A] (para : parallel (SEG_nd A B) df) : odist A df = odist B df := sorry

theorem odist_eq_odist_iff_parallel_ne {α} [DirFig α P] (A B : P) (df : α) [bnea : PtNe B A] : (parallel (SEG_nd A B) df) ↔ odist A df = odist B df := by
  have coer1 : (parallel (SEG_nd A B) df) = (parallel (SEG_nd A B) (toDirLine df)) := by
    unfold parallel
    have : toProj df = toProj (toDirLine df) := by
      simp only [← DirObj.toDir_toProj_eq_toProj]
      congr
      apply DirFig.toDirLine_toDir_eq_toDir.symm
    simp only [this]
  have coer2 : (odist A df = odist B df) = (odist A (toDirLine df) = odist B (toDirLine df)) := by
    have a : odist A df = odist A (toDirLine df) := by rfl
    have b : odist B df = odist B (toDirLine df) := by rfl
    simp only [a,b]
  simp only [coer1,coer2]
  rcases (Quotient.exists_rep (toDirLine df)) with ⟨ray , h0⟩
  simp only [← h0]
  show SEG_nd A B ∥ ray ↔ odist A ray = odist B ray
  have h : (odist A ray = odist B ray) = (Vec.det ray.toDir.unitVecND (VEC_nd A B) = 0) := by
    unfold odist
    unfold odist'
    show ((Vec.det ray.toDir.unitVecND) (VEC ray.source A) = Vec.det ray.toDir.unitVecND (VEC ray.source B)) = (Vec.det ray.toDir.unitVecND (VEC_nd A B) = 0)
    have : Vec.det ray.toDir.unitVecND (VEC_nd A B) =Vec.det ray.toDir.unitVecND (VEC ray.source B) - Vec.det ray.toDir.unitVecND (VEC ray.source A):= by
      calc
        _= Vec.det ray.toDir.unitVecND (VEC A ray.source + VEC ray.source B):= by simp
        _= Vec.det ray.toDir.unitVecND (VEC A ray.source) + Vec.det ray.toDir.unitVecND (VEC ray.source B) := by
          apply LinearMap.map_add
        _= -Vec.det ray.toDir.unitVecND (VEC ray.source A) + Vec.det ray.toDir.unitVecND (VEC ray.source B) := by
          simp only [ne_eq, Dir.coe_unitVecND, add_left_inj]
          calc
            _=Vec.det ray.toDir.unitVec (-(VEC ray.source A)) := by simp
            _=_ := by simp only [LinearMap.map_neg]
        _=_ := by ring
    simp only  [this]
    simp only [eq_iff_iff]
    constructor
    · intro p
      simp [p]
    · intro p
      symm
      calc
        _= ((Vec.det ↑ray.toDir.unitVecND) (VEC ray.source B) - (Vec.det ↑ray.toDir.unitVecND) (VEC ray.source A)) + (Vec.det ↑ray.toDir.unitVecND) (VEC ray.source A) := by ring
        _=_ := by simp only [ne_eq, Dir.coe_unitVecND, p, zero_add]
  have h' : (Vec.det ray.toDir.unitVecND (VEC_nd A B) = 0) = (ray.toDir.unitVecND.toProj = (VEC_nd A B).toProj) := by
    simp only [eq_iff_iff]
    exact VecND.det_eq_zero_iff_toProj_eq_toProj (u := ray.toDir.unitVecND) (v := VEC_nd A B)
  simp only [h,h']
  unfold parallel
  have : toProj (SEG_nd A B) = (VEC_nd A B).toProj := by rfl
  constructor
  · intro p
    simp only [this] at p
    simp only [p]
    simp only [Dir.unitVecND_toProj]
    rfl
  · intro p
    simp only [this,←p]
    simp only [Dir.unitVecND_toProj]
    rfl

theorem wedge_eq_wedge_iff_parallel_of_ne_ne (A B C D : P) [bnea : PtNe B A] [dnec : PtNe D C] : (parallel (SEG_nd A B) (SEG_nd C D)) ↔ wedge A B C = wedge A B D := by
  have : (wedge A B C = wedge A B D) = (odist C (SEG_nd A B) = odist D (SEG_nd A B)) := by
    symm
    simp only [eq_iff_iff]
    exact wedge_eq_wedge_iff_odist_eq_odist_of_ne A B C D
  simp only [this]
  have : (parallel (SEG_nd A B) (SEG_nd C D)) = (parallel (SEG_nd C D) (SEG_nd A B)) := by
    unfold parallel
    simp only [eq_iff_iff]
    constructor
    · intro P
      exact P.symm
    · intro P
      exact P.symm
  simp only [this]
  exact odist_eq_odist_iff_parallel_ne C D (SEG_nd A B)

theorem oarea_eq_oarea_iff_parallel_ne (A B C D : P) [bnea : PtNe B A] [dnec : PtNe D C] : (parallel (SEG_nd A B) (SEG_nd C D)) ↔ oarea A B C = oarea A B D := by
  unfold oarea
  have : (wedge A B C / 2 = wedge A B D / 2) = (wedge A B C = wedge A B D) := by
    simp only [eq_iff_iff]
    constructor
    · intro P
      calc
        _= wedge A B C /2 *2 := by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          div_mul_cancel]
        _= wedge A B D /2 *2 := by simp only [P]
        _=_ := by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_mul_cancel]
    · intro P
      simp only [P]
  simp only [this]
  exact wedge_eq_wedge_iff_parallel_of_ne_ne A B C D

end cooperation_with_parallel

scoped infix : 55 " LiesOnLeft " => IsOnLeftSide
scoped infix : 55 " LiesOnRight " => IsOnRightSide

section handside

theorem same_sign_of_parallel (A B : P) (ray : Ray P) [bnea : PtNe B A] (para : parallel (RAY A B)  ray) : odist_sign A ray = odist_sign B ray := by
  unfold odist_sign
  rw [odist_eq_odist_of_parallel' A B ray para]

--Is discussed with IsOnSameSide only except odist_sign = 0
theorem same_odist_sign_of_same_odist_sign (A B : P) (l : DirLine P) (signeq : odist_sign A l = odist_sign B l) : ∀ (C : P) , Seg.IsOn C (SEG A B) → odist_sign C l = odist_sign A l := sorry

--Is discussed with relative side
--theorem no_intersect_of_same_odist_sign (A B : P) (l : DirLine P) (signeq : odist_sign A l * odist_sign B l = 1) : ∀ (C : P) , Seg.IsOn C (SEG A B) → ¬ Line.IsOn C l := sorry

--theorem intersect_of_diff_odist_sign (A B : P) (l : DirLine P) (signdiff : odist_sign A l * odist_sign B l = -1) : ∃ (C : P), Seg.IsOn C (SEG A B) ∧ Line.IsOn C l := sorry

/-
--this is proven later after relative side and stronger

lemma ne_of_isonleft_of_lieson (A B : P) (r : DirLine P) (aliesonr : A LiesOn r) (bliesonleft : IsOnLeftSide B r) : B ≠ A := by
  intro h0
  have : odist A r = 0 := by sorry
  simp only [h0] at bliesonleft
  unfold IsOnLeftSide at bliesonleft
  linarith

theorem isonleft_of_isintray_of_isonleft (r : DirLine P) (A B C: P) (aliesonr : Line.IsOn A r) (bliesonleft : IsOnLeftSide B r) (conab : Ray.IsInt C (RAY A B (ne_of_isonleft_of_lieson A B r aliesonr bliesonleft))) : IsOnLeftSide C r := sorry
-/

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

theorem not_collinear_of_IsOnSameSide (A B C D : P) [bnea : PtNe B A] (h : IsOnSameSide C D (RAY A B)) : (¬ collinear A B C) ∧ (¬ collinear A B D) := by
  have hlr : (IsOnLeftSide C (RAY A B)) ∨ (IsOnRightSide C (RAY A B)) := by
    rcases h with l|r
    · simp only [l.1, true_or]
    · simp only [r.1, or_true]
  have hlr' : (IsOnLeftSide D (RAY A B)) ∨ (IsOnRightSide D (RAY A B)) := by
    rcases h with l|r
    · simp only [l.2, true_or]
    · simp only [r.2, or_true]
  have c : ¬ collinear A B C := by
    apply not_collinear_of_LiesOnLeft_or_LiesOnRight
    exact hlr
  have d : ¬ collinear A B D := by
    apply not_collinear_of_LiesOnLeft_or_LiesOnRight
    exact hlr'
  simp only [c, not_false_eq_true, d, and_self]

theorem not_collinear_of_IsOnOppositeSide (A B C D : P) [bnea : PtNe B A] (h : IsOnOppositeSide C D (RAY A B)) : (¬ collinear A B C) ∧ (¬ collinear A B D) := by
  have hlr : (IsOnLeftSide C (RAY A B)) ∨ (IsOnRightSide C (RAY A B)) := by
    rcases h with l|r
    · simp only [l.1, true_or]
    · simp only [r.1, or_true]
  have hlr' : (IsOnLeftSide D (RAY A B)) ∨ (IsOnRightSide D (RAY A B)) := by
    rcases h with l|r
    · simp only [l.2, or_true]
    · simp only [r.2, true_or]
  have c : ¬ collinear A B C := by
    apply not_collinear_of_LiesOnLeft_or_LiesOnRight
    exact hlr
  have d : ¬ collinear A B D := by
    apply not_collinear_of_LiesOnLeft_or_LiesOnRight
    exact hlr'
  simp only [c, not_false_eq_true, d, and_self]

lemma lies_on_of_lies_on_toline' {α} (A : P) [ProjFig α P] (df : α) : A LiesOn df → A LiesOn (toLine df) := by
  apply ProjFig.carrier_subset_toLine

theorem not_LiesOn_of_IsOnSameSide' {α} [ProjFig α P] (A B : P) (l : α) (h : IsOnSameSide A B l) : ¬ A LiesOn l := by
  have h' : IsOnSameSide A B (toLine l) =  IsOnSameSide A B l := by rfl
  simp only [← h'] at h
  rcases (Quotient.exists_rep (toLine l)) with ⟨ray , h0⟩
  simp only [← h0] at h
  have h'' : IsOnSameSide A B ray := by exact h
  unfold IsOnSameSide at h''
  unfold IsOnSameSide' at h''
  have llrr :  A LiesOnLeft ray ∧ B LiesOnLeft ray ∨ A LiesOnRight ray ∧ B LiesOnRight ray := by exact h''
  have lr : A LiesOnLeft ray ∨ A LiesOnRight ray := by
    rcases llrr with ll|rr
    · simp only [ll.1, true_or]
    · simp only [rr.1, or_true]
  have : ¬ A LiesOn (toLine ray) := by
    rcases lr with l|r
    · exact (not_LiesOnRight_and_not_LiesOn_Line_of_LiesOnLeft A ray l).2
    · exact (not_LiesOnLeft_and_not_LiesOn_Line_of_LiesOnRight A ray r).2
  apply (lies_on_of_lies_on_toline' A l).mt
  simp only [← h0]
  exact this

theorem not_LiesOn_of_IsOnSameSide {α} [ProjFig α P] (A B : P) (l : α) (h : IsOnSameSide A B l) : (¬ A LiesOn l) ∧ (¬ B LiesOn l) := by
  have h' : IsOnSameSide B A l := by
    have : IsOnSameSide B A l = IsOnSameSide A B l := by
      exact IsOnSameSide_symm B A l
    simp only [this]
    exact h
  have a: ¬ A LiesOn l := by
    exact not_LiesOn_of_IsOnSameSide' A B l h
  have b: ¬ B LiesOn l := by
    exact not_LiesOn_of_IsOnSameSide' B A l h'
  simp only [a, not_false_eq_true, b, and_self]

theorem not_LiesOn_of_IsOnOppositeSide' {α} [ProjFig α P] (A B : P) (l : α) (h : IsOnOppositeSide A B l) : ¬ A LiesOn l := by
  have h' : IsOnOppositeSide A B (toLine l) =  IsOnOppositeSide A B l := by rfl
  simp only [← h'] at h
  rcases (Quotient.exists_rep (toLine l)) with ⟨ray , h0⟩
  simp only [← h0] at h
  have h'' : IsOnOppositeSide A B ray := by exact h
  unfold IsOnOppositeSide at h''
  unfold IsOnOppositeSide' at h''
  have llrr :  A LiesOnLeft ray ∧ B LiesOnRight ray ∨ A LiesOnRight ray ∧ B LiesOnLeft ray := by exact h''
  have lr : A LiesOnLeft ray ∨ A LiesOnRight ray := by
    rcases llrr with ll|rr
    · simp only [ll.1, true_or]
    · simp only [rr.1, or_true]
  have : ¬ A LiesOn (toLine ray) := by
    rcases lr with l|r
    · exact (not_LiesOnRight_and_not_LiesOn_Line_of_LiesOnLeft A ray l).2
    · exact (not_LiesOnLeft_and_not_LiesOn_Line_of_LiesOnRight A ray r).2
  apply (lies_on_of_lies_on_toline' A l).mt
  simp only [← h0]
  exact this

theorem not_LiesOn_of_IsOnOppositeSide {α} [ProjFig α P] (A B : P) (l : α) (h : IsOnOppositeSide A B l) : (¬ A LiesOn l) ∧ (¬ B LiesOn l) := by
  have h' : IsOnOppositeSide B A l := by
    have : IsOnOppositeSide B A l = IsOnOppositeSide A B l := by
      exact IsOnOppositeSide_symm B A l
    simp only [this]
    exact h
  have a: ¬ A LiesOn l := by
    exact not_LiesOn_of_IsOnOppositeSide' A B l h
  have b: ¬ B LiesOn l := by
    exact not_LiesOn_of_IsOnOppositeSide' B A l h'
  simp only [a, not_false_eq_true, b, and_self]

theorem IsOnSameSide_or_IsOnOppositeSide_of_not_LiesOn (A B : P) (l : Line P) (a : ¬ A LiesOn l) (b : ¬ B LiesOn l) : IsOnSameSide A B l ∨ IsOnOppositeSide A B l := by
  rcases (Quotient.exists_rep l) with ⟨ray , h0⟩
  simp only [← h0]
  have coer : (toLine ray) = l := by exact h0
  simp only [←coer] at a
  simp only [←coer] at b
  have : IsOnSameSide A B ray ∨ IsOnOppositeSide A B ray := by
    have alr : A LiesOnLeft ray ∨ A LiesOnRight ray := by
      exact LiesOnLeft_or_LiesOnRight_of_not_LiesOn a
    have blr : B LiesOnLeft ray ∨ B LiesOnRight ray := by
      exact LiesOnLeft_or_LiesOnRight_of_not_LiesOn b
    unfold IsOnSameSide
    unfold IsOnOppositeSide
    unfold IsOnSameSide'
    unfold IsOnOppositeSide'
    show (A LiesOnLeft ray ∧ B LiesOnLeft ray ∨ A LiesOnRight ray ∧ B LiesOnRight ray) ∨ (A LiesOnLeft ray ∧ B LiesOnRight ray ∨ A LiesOnRight ray ∧ B LiesOnLeft ray)
    rcases alr with al|ar
    · rcases blr with bl|br
      · simp only [al, bl, and_self, true_or, true_and, and_true]
      · simp only [al, true_and, br, and_true, and_self, true_or, or_true]
    · rcases blr with bl|br
      · simp only [bl, and_true, ar, true_and, and_self, or_true]
      · simp only [ar, br, and_self, or_true, and_true, true_and, true_or]
  exact this

end relative_side

section relative_side_with_seg_and_ray

/-
In this section,we will discuss the compatibility with seg and ray.
-/

lemma ne_of_not_lies_on {α} [ProjFig α P] {A B : P} (l : α) (ha : A LiesOn l) (hb : ¬ B LiesOn l) : B ≠ A := by
  have : A ≠ B := by
    by_contra h
    simp only [h] at ha
    absurd ha
    exact hb
  symm
  exact this

theorem same_side_of_line_passing_source (A B C : P) (l : Line P) (ha : A LiesOn l) (hb : ¬ B LiesOn l) (hc : C LiesInt (RAY A B (ne_of_not_lies_on l ha hb))) : IsOnSameSide B C l := by
  have c_ne_a : C ≠ A := by
    exact hc.2
  have b_ne_a : B ≠ A := ne_of_not_lies_on l ha hb
  have eqDir : (VEC_nd A C c_ne_a).toDir = (VEC_nd A B b_ne_a).toDir := by
    calc
      _=(RAY A C c_ne_a).toDir := by rfl
      _=(RAY A B b_ne_a).toDir := by
        congr 1
        exact Ray.pt_pt_eq_ray hc
      _=_ := by rfl
  have eqDir' : (VEC_nd A C c_ne_a).SameDir (VEC_nd A B b_ne_a) := by
    apply VecND.toDir_eq_toDir_iff.mp
    exact eqDir
  unfold VecND.SameDir at eqDir'
  rcases eqDir' with ⟨x,h⟩
  have x_pos : x > 0 := h.1
  rcases l.exist_rep_ray_source_eq_pt ha with ⟨r,p⟩
  have : IsOnSameSide B C r = IsOnSameSide B C l := by
    calc
      _= IsOnSameSide B C r.toLine := by rfl
      _=_ := by congr; exact p.2
  simp only [← this]
  have ratio : odist C r = x * odist B r := by
    unfold odist
    show odist' C r = x * odist' B r
    unfold odist'
    simp only [p.1]
    calc
      _= Vec.det r.toDir.unitVec (VEC_nd A C c_ne_a) := by rfl
      _= Vec.det r.toDir.unitVec (x • (VEC_nd A B b_ne_a)) := by congr;exact h.2
      _= x * Vec.det r.toDir.unitVec (VEC_nd A B b_ne_a) := by
        simp only [LinearMap.map_smul]
        rfl
      _=_ := by rfl
  have lr : (B LiesOnLeft r) ∨ (B LiesOnRight r) := by
    have n : ¬ B LiesOn (toLine r) := by
      have : B LiesOn (toLine r) = B LiesOn l := by
        congr; exact p.2
      simp only [this]
      exact hb
    exact LiesOnLeft_or_LiesOnRight_of_not_LiesOn n
  unfold IsOnSameSide
  unfold IsOnSameSide'
  show B LiesOnLeft r ∧ C LiesOnLeft r ∨ B LiesOnRight r ∧ C LiesOnRight r
  rcases lr with bl|br
  · have cl : C LiesOnLeft r := by
      unfold IsOnLeftSide at bl
      unfold IsOnLeftSide
      simp only [ratio]
      positivity
    simp only [bl, cl, and_self, true_or]
  · have cr : C LiesOnRight r := by
      unfold IsOnRightSide at br
      unfold IsOnRightSide
      simp only [ratio]
      have b : -odist B r > 0 := by linarith
      have : -x * odist B r > 0 := by
        calc
          _= x * (-odist B r) := by simp only [neg_mul, mul_neg]
          _>0 := by positivity
      linarith
    simp only [br, cr, and_self, or_true]

lemma linear_comb_of_lies_on (A B C D : P) {t : ℝ} (h : (VEC A C) = t • (VEC A B)) : (VEC D C) = (1-t) • (VEC D A) + t • (VEC D B) := by
  calc
      _= VEC D A + VEC A C := by simp only [vec_add_vec]
      _= VEC D A + t • (VEC A B) := by simp only [h]
      _= VEC D A + t • (VEC A D + VEC D B)  := by simp only [vec_add_vec]
      _= VEC D A + t • VEC A D + t • VEC D B := by
        have : t • (VEC A D + VEC D B) = t • VEC A D + t • VEC D B := by
          exact smul_add t (VEC A D) (VEC D B)
        simp only [this]
        show (VEC D A + (t • VEC A D + t • VEC D B) = VEC D A + t • VEC A D + t • VEC D B)
        rw [add_assoc]
      _= (1 : ℝ) • VEC D A + (-t) • VEC D A + t • VEC D B := by
        simp only [one_smul, neg_smul, add_left_inj, add_right_inj]
        calc
          _= t • VEC A D := by rfl
          _= t • -VEC D A := by congr;simp only [neg_vec]
          _= -(t • VEC D A) := by
            apply smul_neg
          _=_ := by rfl
      _=_ := by
        have : (1 : ℝ) • VEC D A + (-t) • VEC D A = (1 + (-t)) • VEC D A := by
          symm
          exact add_smul (x := VEC D A) (r := (1 : ℝ)) (s := -t)
        simp only [this]
        have : (1 + -t) = (1 - t) := by ring
        simp only [this]

lemma L_of_vertices_LL {ray : Ray P} {A B C : P} (al : A LiesOnLeft ray) (bl : B LiesOnLeft ray) (c_on : C LiesOn (SEG A B)) : C LiesOnLeft ray := by
  rcases (c_on) with ⟨t,ge0,le1,h'⟩
  have h : VEC A C = t • (VEC A B) := by exact h'
  let D : P := ray.source
  let v : Vec := ray.toDir.unitVec
  unfold IsOnLeftSide at al
  unfold odist at al
  have al' : odist' A ray > 0 := by exact al
  unfold odist' at al'
  have a : Vec.det v (VEC D A) > 0 := by exact al'
  unfold IsOnLeftSide at bl
  unfold odist at bl
  have bl' : odist' B ray > 0 := by exact bl
  unfold odist' at bl'
  have f : (VEC D C) = (1-t) • (VEC D A) + t • (VEC D B) := by
    exact linear_comb_of_lies_on A B C D h
  unfold IsOnLeftSide
  unfold odist
  show odist' C ray > 0
  unfold odist'
  show Vec.det v (VEC D C) > 0
  simp only [f]
  show Vec.det v ((1-t) • (VEC D A) + t • (VEC D B)) > 0
  have gt_or_0 : t > 0 ∨ 0 = t := by
    simp only [gt_iff_lt]
    have : (0 < t ∨ 0 = t) = (0 ≤ t) := by
      symm
      simp only [eq_iff_iff]
      exact le_iff_lt_or_eq (a:= 0) (b:= t)
    simp [this]
    simp only [ge0]
  have n : 1-t ≥ 0 :=by
    linarith
  calc
    _= (1-t) * Vec.det v (VEC D A) + t * Vec.det v (VEC D B) := by
      simp only [map_add, map_smul, smul_eq_mul]
    _> 0 := by
      rcases gt_or_0 with gt|eq0
      · have : (1-t) * Vec.det v (VEC D A) ≥ 0 := by
          positivity
        have : t * Vec.det v (VEC D B) > 0 := by
          positivity
        linarith
      · symm at eq0
        simp only [eq0, sub_zero, one_mul, zero_mul, add_zero, gt_iff_lt]
        show Vec.det v (VEC D A) > 0
        exact a

theorem IsOnSameSide_of_vertices_SameSide' {A B C : P} {l : Line P} (h : IsOnSameSide A B l) (c_on : C LiesOn (SEG A B)) : IsOnSameSide C A l := by
  rcases (Quotient.exists_rep l) with ⟨ray , h0⟩
  simp only [← h0] at h
  unfold IsOnSameSide at h
  unfold IsOnSameSide' at h
  have llrr : A LiesOnLeft ray ∧ B LiesOnLeft ray ∨ A LiesOnRight ray ∧ B LiesOnRight ray := by exact h
  simp only [←h0]
  show IsOnSameSide C A ray
  unfold IsOnSameSide
  unfold IsOnSameSide'
  show C LiesOnLeft ray ∧ A LiesOnLeft ray ∨ C LiesOnRight ray ∧ A LiesOnRight ray
  rcases llrr with ll|rr
  · have cl : C LiesOnLeft ray := by
      exact L_of_vertices_LL ll.1 ll.2 c_on
    simp only [cl, ll.1, and_self, true_or]
  · have ar₀ := rr.1
    unfold IsOnRightSide at rr
    have ar := rr.1
    have br := rr.2
    have al' : A LiesOnLeft ray.reverse := by
      unfold IsOnLeftSide
      show odist A ray.reverse > 0
      calc
        _= -odist A ray := by exact odist_reverse_eq_neg_odist' A ray
        _> 0 := by linarith
    have bl' : B LiesOnLeft ray.reverse := by
      unfold IsOnLeftSide
      show odist B ray.reverse > 0
      calc
        _= -odist B ray := by exact odist_reverse_eq_neg_odist' B ray
        _> 0 := by linarith
    have cl' : C LiesOnLeft ray.reverse := by
      exact L_of_vertices_LL al' bl' c_on
    unfold IsOnLeftSide at cl'
    have cr : C LiesOnRight ray := by
      unfold IsOnRightSide
      calc
        _=-odist C ray.reverse := by
          simp [odist_reverse_eq_neg_odist' C ray]
        _< 0 := by linarith
    simp [ar₀,cr]

theorem IsOnSameSide_of_vertices_SameSide {α} [ProjFig α P] {A B C : P} {l : α} (h : IsOnSameSide A B l) (c_on : C LiesOn (SEG A B)) : IsOnSameSide C A l := by
  have h' : IsOnSameSide A B (toLine l) := by exact h
  have goal' : IsOnSameSide C A (toLine l) := by
    exact IsOnSameSide_of_vertices_SameSide' h' c_on
  exact goal'

theorem not_IsOnSameSide_of_exist_inx (A B C : P) (l : Line P) (h : C IsInxOf (SEG A B) l) : ¬ IsOnSameSide A B l := by
  by_contra s
  have : C LiesOn (SEG A B) ∧ C LiesOn l := by exact h
  have c1 := this.1
  have c2 := this.2
  have same: IsOnSameSide C A l := by
    exact IsOnSameSide_of_vertices_SameSide s c1
  absurd c2
  exact (not_LiesOn_of_IsOnSameSide C A l same).1

lemma ne_odist_of_IsOnOppositeSide {A B : P} {ray : Ray P} (h : IsOnOppositeSide A B ray) : odist A ray ≠ odist B ray := by
  by_contra eq
  unfold IsOnOppositeSide at h
  unfold IsOnOppositeSide' at h
  have llrr : A LiesOnLeft ray ∧ B LiesOnRight ray ∨ A LiesOnRight ray ∧ B LiesOnLeft ray := by exact h
  rcases llrr with lr|rl
  · have al: odist A ray > 0 := by exact lr.1
    have br: odist B ray < 0 := by exact lr.2
    simp only [eq] at al
    linarith
  · have ar : odist A ray < 0 := by exact rl.1
    have bl : odist B ray > 0 := by exact rl.2
    simp only [eq] at ar
    linarith

theorem exist_inx_int_of_IsOnOppositeSide (A B : P) (l : Line P) (h : IsOnOppositeSide A B l) : ∃ C : P , (C IsInxOf (SEG A B) l) ∧ (C LiesInt (SEG A B)) := by
  rcases (Quotient.exists_rep l) with ⟨ray , h0⟩
  simp only [← h0] at h
  have h' : IsOnOppositeSide A B ray := by exact h
  have b_ne_a : B ≠ A := by
    by_contra H
    have : odist A ray ≠ odist B ray := ne_odist_of_IsOnOppositeSide h
    simp only [H] at this
    absurd this
    rfl
  haveI : PtNe B A := ⟨b_ne_a⟩
  let x : ℝ := odist A ray / (odist A ray - odist B ray)
  have ne0 : (odist A ray - odist B ray) ≠ 0 := by
    by_contra e0
    have : odist A ray = odist B ray := by
      calc
        _= (odist A ray - odist B ray) + odist B ray := by ring
        _=_ := by simp only [e0, zero_add]
    absurd this
    show odist A ray ≠ odist B ray
    exact ne_odist_of_IsOnOppositeSide h
  have gt0_lt1: (x > 0) ∧ (x < 1) := by
    unfold IsOnOppositeSide at h'
    unfold IsOnOppositeSide' at h'
    have llrr : A LiesOnLeft ray ∧ B LiesOnRight ray ∨ A LiesOnRight ray ∧ B LiesOnLeft ray := by exact h'
    let a : ℝ := odist A ray
    let b : ℝ := odist B ray
    have t₁ : x = a / (a - b) := by rfl
    have t₂ : 1 - x = -b / (a - b) := by field_simp
    rcases llrr with lr|rl
    · unfold IsOnLeftSide at lr
      unfold IsOnRightSide at lr
      have apos : a > 0 := by exact lr.1
      have bneg : -b > 0 := by linarith
      have : a - b > 0 := by linarith
      have gt0 : x > 0 := by
        simp only [t₁]
        positivity
      have lt1' : 1 - x > 0 := by
        simp only [t₂]
        positivity
      have lt1 : x < 1 := by linarith
      simp only [gt_iff_lt, gt0, lt1, and_self]
    · unfold IsOnLeftSide at rl
      unfold IsOnRightSide at rl
      have aneg : -a > 0 := by linarith
      have bpos : b > 0 := by linarith
      have : - (a - b) > 0 := by linarith
      have gt0 : x > 0 := by
        calc
          _= a / (a - b) := by simp only [t₁]
          _= -a / -(a - b) := by
            simp only [div_neg,neg_div,neg_neg]
          _> 0 := by positivity
      have lt1' : 1 - x > 0 := by
        calc
          _= -b / (a - b) := by simp only [t₂]
          _= b / -(a - b) := by
            simp only [div_neg,neg_div,neg_neg]
          _> 0 := by positivity
      have lt1 : x < 1 := by linarith
      simp only [gt_iff_lt, gt0, lt1, and_self]
  have gt0 : x > 0 := gt0_lt1.1
  have lt1 : x < 1 := gt0_lt1.2
  let C : P := x • (VEC A B) +ᵥ A
  have vec : (VEC A C) = x • (VEC A B) := by simp only [vec_of_pt_vadd_pt_eq_vec]
  have c_on' : odist C ray = 0 := by
    unfold odist
    show odist' C ray = 0
    unfold odist'
    let D : P := ray.source
    let v : Vec := ray.toDir.unitVec
    show Vec.det v (VEC D C) = 0
    have : (VEC D C) = (1 - x) • (VEC D A) + x • (VEC D B) := by
      exact linear_comb_of_lies_on A B C D vec
    simp only [this]
    calc
      _= Vec.det v ((1 - x) • (VEC D A)) + Vec.det v (x • (VEC D B)) := by apply LinearMap.map_add
      _= (1 - x) * Vec.det v (VEC D A) + x * Vec.det v (VEC D B) := by
        have smul1 : Vec.det v ((1 - x) • (VEC D A)) = (1 - x) * Vec.det v (VEC D A) := by
          apply LinearMap.map_smul
        have smul2 : Vec.det v (x • (VEC D B)) = x * Vec.det v (VEC D B) := by
          apply LinearMap.map_smul
        simp only [smul1,smul2]
      _= (1 - (odist A ray / (odist A ray - odist B ray))) * odist A ray + (odist A ray / (odist A ray - odist B ray)) * odist B ray := by rfl
      _= (-odist B ray) / (odist A ray - odist B ray) * odist A ray + (odist A ray / (odist A ray - odist B ray)) * odist B ray := by
        have : 1 - (odist A ray / (odist A ray - odist B ray)) = (-odist B ray) / (odist A ray - odist B ray) := by field_simp
        simp only [this]
      _=0 := by
        field_simp
        ring_nf
  unfold is_inx
  use C
  have c_on : C LiesOn (toLine ray) := by
    apply (online_iff_lies_on_line C ray).mpr
    exact c_on'
  have c_int : C LiesInt (SEG A B) := by
    show C LiesInt (SEG_nd A B)
    apply SegND.lies_int_iff.mpr
    use x
    simp [gt0,lt1]
    show (VEC A C) = x • (VEC_nd A B)
    exact vec
  have C_on : C LiesOn (SEG A B) := by
    simp only [c_int, Seg.lies_on_of_lies_int]
  simp only [c_int,C_on]
  simp only [true_and, and_true]
  simp only [← h0]
  exact c_on

end relative_side_with_seg_and_ray

scoped notation A:max "and" B:max " LiesOnSameSide " C:max => IsOnSameSide A B C

variable (A B : P) [EuclideanPlane P] (l : Line P)

#check A and B LiesOnSameSide l

scoped notation:5 A:max "and" B:max " LiesOnOppositeSide " C:max => IsOnOppositeSide A B C


-- @[inherit_doc IsOnSameSide]
-- scoped syntax term:max ws term:max ws " LiesOnSameSide " ws term:max : term

/- Position of two lines; need a function to take the intersection of two lines (when they intersect). -/


/- A lot more theorems regarding positions -/
/- e.g. 180 degree implies collinear -/

end EuclidGeom
