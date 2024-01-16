import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Circle.CCPosition
import EuclideanGeometry.Foundation.Axiom.Circle.LCPosition
import EuclideanGeometry.Foundation.Axiom.Circle.IncribedAngle

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

open DirLC CC Angle

namespace Circle

-- Define the power of a point P relative to a circle ω with center O and radius r to be OP ^ 2 - r ^ 2
def power (ω : Circle P) (p : P) : ℝ := dist ω.center p ^ 2 - ω.radius ^ 2

theorem inside_circle_iff_power_npos (p : P) (ω : Circle P) : p LiesIn ω ↔ ω.power p ≤ 0 := by
  apply Iff.trans _ sub_nonpos.symm
  unfold Circle.IsInside
  apply Iff.trans _ sq_le_sq.symm
  rw [abs_of_nonneg dist_nonneg, abs_of_pos ω.rad_pos]

theorem interior_of_circle_iff_power_neg (p : P) (ω : Circle P) : p LiesInt ω ↔ ω.power p < 0 := by
  apply Iff.trans _ sub_neg.symm
  unfold lies_int Interior.interior instInteriorCircle Circle.interior Circle.IsInt
  simp
  apply Iff.trans _ sq_lt_sq.symm
  rw [abs_of_nonneg dist_nonneg, abs_of_pos ω.rad_pos]

theorem lies_on_circle_iff_power_zero (p : P) (ω : Circle P) : p LiesOn ω ↔ ω.power p = 0 := by
  apply Iff.trans _ sub_eq_zero.symm
  unfold lies_on Fig.carrier instFigCircle Circle.carrier Circle.IsOn
  simp
  apply Iff.trans _ (sq_eq_sq dist_nonneg _).symm
  rfl
  apply le_iff_lt_or_eq.mpr
  left; exact ω.rad_pos

theorem outside_circle_iff_power_pos (p : P) (ω : Circle P) : p LiesOut ω ↔ 0 < ω.power p  := by
  apply Iff.trans _ sub_pos.symm
  unfold Circle.IsOutside
  apply Iff.trans _ sq_lt_sq.symm
  rw [abs_of_nonneg dist_nonneg, abs_of_pos ω.rad_pos]

end Circle

section tangent

namespace Circle

@[ext]
structure Tangents (P : Type _) [EuclideanPlane P] where
  left : P
  right : P

lemma tangent_circle_intersected {ω : Circle P} {p : P} (h : p LiesOut ω) : Circle.mk_pt_pt_diam (A := p) (B := ω.center) (_h := (pt_liesout_ne_center h)) Intersect ω := by
  unfold Circle.mk_pt_pt_diam
  constructor
  · simp; exact ω.rad_pos
  simp
  by_cases hi : ω.radius - dist (SEG p ω.center).midpoint ω.center ≥ 0
  · rw [abs_of_nonneg hi]
    apply sub_lt_iff_lt_add.mpr
    rw [← two_mul]
    unfold Seg.midpoint
    rw [NormedAddTorsor.dist_eq_norm', ← show ‖(2 : ℝ)‖ = 2 by norm_num, ← norm_smul, vadd_vsub_assoc, smul_add, smul_smul]
    norm_num
    rw [two_smul, ← add_assoc, ← Vec.mkPtPt, vec_add_vec, vec_same_eq_zero, zero_add, Vec.mkPtPt, ← NormedAddTorsor.dist_eq_norm', dist_comm]
    exact h
  push_neg at hi
  rw [abs_of_neg hi, ← zero_sub]
  apply sub_lt_iff_lt_add.mpr
  simp; exact ω.rad_pos

def pt_tangent_circle_pts {ω : Circle P} {p : P} (h : p LiesOut ω) : Tangents P where
  left := (Inxpts (tangent_circle_intersected h)).left
  right := (Inxpts (tangent_circle_intersected h)).right

theorem tangents_lieson_circle {ω : Circle P} {p : P} (h : p LiesOut ω) : ((pt_tangent_circle_pts h).left LiesOn ω) ∧ ((pt_tangent_circle_pts h).right LiesOn ω) := by
  rcases inx_pts_lieson_circles (tangent_circle_intersected h) with ⟨_, ⟨h₂, ⟨_, h₄⟩⟩⟩
  exact ⟨h₂, h₄⟩

lemma tangents_ne_pt {ω : Circle P} {p : P} (h : p LiesOut ω) : ((pt_tangent_circle_pts h).left ≠ p) ∧ ((pt_tangent_circle_pts h).right ≠ p) := by
  constructor
  · intro hp
    have h₁ : ω.radius < dist ω.center p := h
    have : (pt_tangent_circle_pts h).left LiesOn ω := (tangents_lieson_circle h).1
    rw [hp] at this
    have h₂ : dist ω.center p = ω.radius := this
    linarith
  intro hp
  have h₁ : ω.radius < dist ω.center p := h
  have : (pt_tangent_circle_pts h).right LiesOn ω := (tangents_lieson_circle h).2
  rw [hp] at this
  have h₂ : dist ω.center p = ω.radius := this
  linarith

lemma tangents_ne_center {ω : Circle P} {p : P} (h : p LiesOut ω) : ((pt_tangent_circle_pts h).left ≠ ω.center) ∧ ((pt_tangent_circle_pts h).right ≠ ω.center) := by
  have hpos₁ : dist ω.center (pt_tangent_circle_pts h).left > 0 := by
    calc
      _ = ω.radius := (tangents_lieson_circle h).1
      _ > 0 := ω.rad_pos
  have hpos₂ : dist ω.center (pt_tangent_circle_pts h).right > 0 := by
    calc
      _ = ω.radius := (tangents_lieson_circle h).2
      _ > 0 := ω.rad_pos
  constructor
  · apply dist_pos.mp
    rw [dist_comm]; exact hpos₁
  apply dist_pos.mp
  rw [dist_comm]; exact hpos₂

lemma tangents_perp₁ {ω : Circle P} {p : P} (h : p LiesOut ω) : (DLIN p (pt_tangent_circle_pts h).left (tangents_ne_pt h).1) ⟂ (DLIN ω.center (pt_tangent_circle_pts h).left (tangents_ne_center h).1) := by
  haveI : PtNe ω.center p := (Circle.pt_liesout_ne_center h).symm
  haveI : PtNe (pt_tangent_circle_pts h).left ω.center := ⟨(tangents_ne_center h).1⟩
  haveI : PtNe (pt_tangent_circle_pts h).left p := ⟨(tangents_ne_pt h).1⟩
  have heq₁ : ∠ p (pt_tangent_circle_pts h).left ω.center = ∡[π / 2] := by
    apply inscribed_angle_of_diameter_eq_mod_pi_pt_pt_pt
    · exact (inx_pts_lieson_circles (tangent_circle_intersected h)).1
    exact Arc.mk_pt_pt_diam_isantipode
  show (DLIN p (pt_tangent_circle_pts h).left).toProj = (DLIN ω.center (pt_tangent_circle_pts h).left).toProj.perp
  calc
    _ = (RAY p (pt_tangent_circle_pts h).left).toProj := rfl
    _ = (RAY (pt_tangent_circle_pts h).left p).toProj := by apply Ray.toProj_eq_toProj_of_mk_pt_pt
    _ = (RAY (pt_tangent_circle_pts h).left ω.center).toProj.perp := dir_perp_iff_dvalue_eq_pi_div_two.mpr heq₁
    _ = (RAY ω.center (pt_tangent_circle_pts h).left).toProj.perp := by rw [Ray.toProj_eq_toProj_of_mk_pt_pt]
    _ = (DLIN ω.center (pt_tangent_circle_pts h).left).toProj.perp := rfl

lemma tangents_perp₂ {ω : Circle P} {p : P} (h : p LiesOut ω) : (DLIN p (pt_tangent_circle_pts h).right (tangents_ne_pt h).2) ⟂ (DLIN ω.center (pt_tangent_circle_pts h).right (tangents_ne_center h).2) := by
  haveI : PtNe ω.center p := (Circle.pt_liesout_ne_center h).symm
  haveI : PtNe (pt_tangent_circle_pts h).right p := ⟨(tangents_ne_pt h).2⟩
  haveI : PtNe ω.center (pt_tangent_circle_pts h).right := ⟨(tangents_ne_center h).2.symm⟩
  have heq₂ : ∠ p (pt_tangent_circle_pts h).right ω.center = ∡[π / 2] := by
    apply inscribed_angle_of_diameter_eq_mod_pi_pt_pt_pt
    · exact (inx_pts_lieson_circles (tangent_circle_intersected h)).2.2.1
    apply Arc.mk_pt_pt_diam_isantipode
  show (DLIN p (pt_tangent_circle_pts h).right).toProj = (DLIN ω.center (pt_tangent_circle_pts h).right).toProj.perp
  calc
    _ = (RAY p (pt_tangent_circle_pts h).right).toProj := rfl
    _ = (RAY (pt_tangent_circle_pts h).right p).toProj := by apply Ray.toProj_eq_toProj_of_mk_pt_pt
    _ = (RAY (pt_tangent_circle_pts h).right ω.center).toProj.perp := dir_perp_iff_dvalue_eq_pi_div_two.mpr heq₂
    _ = (RAY ω.center (pt_tangent_circle_pts h).right).toProj.perp := by rw [Ray.toProj_eq_toProj_of_mk_pt_pt]
    _ = (DLIN ω.center (pt_tangent_circle_pts h).right).toProj.perp := rfl

theorem line_tangent_circle {ω : Circle P} {p : P} (h : p LiesOut ω) : ((DLIN p (pt_tangent_circle_pts h).left (tangents_ne_pt h).1) Tangent ω) ∧ ((DLIN p (pt_tangent_circle_pts h).right (tangents_ne_pt h).2) Tangent ω) := by
  constructor
  · apply pt_pt_perp_tangent h (tangents_lieson_circle h).1 (tangents_perp₁ h)
  apply pt_pt_perp_tangent h (tangents_lieson_circle h).2 (tangents_perp₂ h)

theorem tangent_pts_eq_tangents {ω : Circle P} {p : P} (h : p LiesOut ω) : (Tangentpt (line_tangent_circle h).1 = (pt_tangent_circle_pts h).left) ∧ (Tangentpt (line_tangent_circle h).2 = (pt_tangent_circle_pts h).right) := by
  constructor
  · symm
    apply pt_pt_perp_eq_tangent_pt h (tangents_lieson_circle h).1 (tangents_perp₁ h)
  symm
  apply pt_pt_perp_eq_tangent_pt h (tangents_lieson_circle h).2 (tangents_perp₂ h)

lemma tangent_length_sq_eq_power {p : P} {l : DirLine P} {ω : Circle P} (h₁ : l Tangent ω) (h₂ : p LiesOn l) : (dist p (Tangentpt h₁)) ^ 2 = power ω p := by
  calc
    _ = (dist p (perp_foot ω.center l)) ^ 2 := by rw [tangent_pt_eq_perp_foot]
    _ = (dist ω.center p) ^ 2 - (dist ω.center (perp_foot ω.center l)) ^ 2 := by
      rw [eq_sub_iff_add_eq, add_comm, ← Seg.length_eq_dist, ← Seg.length_eq_dist, ← Seg.length_eq_dist]
      apply Pythagoras_of_perp_foot _ _ h₂
    _ = (dist ω.center p) ^ 2 - (dist ω.center (Tangentpt h₁)) ^ 2 := by rw [tangent_pt_eq_perp_foot]
    _ = (dist ω.center p) ^ 2 - ω.radius ^ 2 := by
      congr
      exact (inx_pts_lieson_circle (intersect_iff_tangent_or_secant.mpr (Or.inl h₁))).1
    _ = power ω p := rfl

theorem length_of_tangent {ω : Circle P} {p : P} (h : p LiesOut ω) : dist p (pt_tangent_circle_pts h).left = dist p (pt_tangent_circle_pts h).right := by
  apply (sq_eq_sq (by exact dist_nonneg) (by exact dist_nonneg)).mp
  haveI : PtNe (pt_tangent_circle_pts h).left p := ⟨(tangents_ne_pt h).1⟩
  haveI : PtNe (pt_tangent_circle_pts h).right p := ⟨(tangents_ne_pt h).2⟩
  have hl₁ : p LiesOn (DLIN p (pt_tangent_circle_pts h).left) := DirLine.fst_pt_lies_on_mk_pt_pt
  have hl₂ : p LiesOn (DLIN p (pt_tangent_circle_pts h).right) := DirLine.fst_pt_lies_on_mk_pt_pt
  rw [← (tangent_pts_eq_tangents h).1, tangent_length_sq_eq_power _ hl₁, ← (tangent_pts_eq_tangents h).2, tangent_length_sq_eq_power _ hl₂]

end Circle

end tangent

section position

namespace Circle

lemma liesout_ne_inxpts {ω : Circle P} {p : P} {l : DirLine P} (h₁ : DirLine.IsIntersected l ω) (_h₂ : p LiesOn l) (h₃ : p LiesOut ω) : (p ≠ (Inxpts h₁).front) ∧ (p ≠ (Inxpts h₁).back) := by
  constructor
  · apply (pt_liesout_ne_pt_lieson h₃ (inx_pts_lieson_circle h₁).1).out
  apply (pt_liesout_ne_pt_lieson h₃ (inx_pts_lieson_circle h₁).2).out

lemma liesint_ne_inxpts {ω : Circle P} {p : P} {l : DirLine P} (h₁ : DirLine.IsIntersected l ω) (_h₂ : p LiesOn l) (h₃ : p LiesInt ω) : (p ≠ (Inxpts h₁).front) ∧ (p ≠ (Inxpts h₁).back) := by
  constructor
  · apply (pt_liesint_ne_pt_lieson h₃ (inx_pts_lieson_circle h₁).1).out
  apply (pt_liesint_ne_pt_lieson h₃ (inx_pts_lieson_circle h₁).2).out

theorem liesout_back_lieson_ray_front {ω : Circle P} {p : P} {l : DirLine P} (h₁ : DirLine.IsIntersected l ω) (h₂ : p LiesOn l) (h₃ : p LiesOut ω) : (Inxpts h₁).back LiesOn (RAY p (Inxpts h₁).front (liesout_ne_inxpts h₁ h₂ h₃).1.symm) := by
  haveI : PtNe p (Inxpts h₁).front := ⟨(liesout_ne_inxpts h₁ h₂ h₃).1⟩
  by_cases heq : (Inxpts h₁).front = (Inxpts h₁).back
  · simp_rw [← heq]
    apply Ray.snd_pt_lies_on_mk_pt_pt
  haveI : PtNe (Inxpts h₁).front (Inxpts h₁).back := ⟨heq⟩
  have eq₁ : LIN (Inxpts h₁).front (Inxpts h₁).back = l := Line.eq_line_of_pt_pt_of_ne (inx_pts_lieson_dlin h₁).1 (inx_pts_lieson_dlin h₁).2
  have h₂' : p LiesOn (LIN (Inxpts h₁).front (Inxpts h₁).back) := by
    rw [eq₁]
    exact h₂
  have eq₂ : perp_foot ω.center l = (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint := by
    rw [← pts_lieson_circle_perpfoot_eq_midpoint (inx_pts_lieson_circle h₁).1 (inx_pts_lieson_circle h₁).2, eq₁]
  have trieq₁ : (dist p (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint) ^ 2 = (dist ω.center p) ^ 2 - (dist ω.center (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint) ^ 2 := by
    rw [← eq₂, eq_sub_iff_add_eq, add_comm, ← Seg.length_eq_dist, ← Seg.length_eq_dist, ← Seg.length_eq_dist]
    apply Pythagoras_of_perp_foot _ _ h₂
  have trieq₂ : (dist (Inxpts h₁).front (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint) ^ 2 = (dist ω.center (Inxpts h₁).front) ^ 2 - (dist ω.center (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint) ^ 2 := by
    rw [← eq₂, eq_sub_iff_add_eq, add_comm, ← Seg.length_eq_dist, ← Seg.length_eq_dist, ← Seg.length_eq_dist]
    apply Pythagoras_of_perp_foot _ _ (inx_pts_lieson_dlin h₁).1
  have hgt : dist p (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint > dist (Inxpts h₁).front (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint := by
    calc
      _ = |dist p (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint| := by rw [abs_of_nonneg dist_nonneg]
      _ > |dist (Inxpts h₁).front (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint| := by
        apply sq_lt_sq.mp
        rw [trieq₁, trieq₂]
        simp
        apply sq_lt_sq.mpr
        rw [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg, (inx_pts_lieson_circle h₁).1]
        exact h₃
      _ = dist (Inxpts h₁).front (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint := by rw [abs_of_nonneg dist_nonneg]
  exact (not_lies_on_seg_nd_iff_lies_on_ray h₂').mp <| ((SEG_nd (DirLC.Inxpts h₁).front (DirLC.Inxpts h₁).back).dist_midpt_gt_iff_not_lies_on_of_lies_on_toLine h₂').mp hgt

theorem liesint_back_lieson_ray_front_reverse {ω : Circle P} {p : P} {l : DirLine P} (h₁ : DirLine.IsIntersected l ω) (h₂ : p LiesOn l) (h₃ : p LiesInt ω) : (Inxpts h₁).back LiesOn (RAY p (Inxpts h₁).front (liesint_ne_inxpts h₁ h₂ h₃).1.symm).reverse := by
  haveI : PtNe p (Inxpts h₁).front := ⟨(liesint_ne_inxpts h₁ h₂ h₃).1⟩
  have hs : dist_pt_line ω.center l.toLine < ω.radius := by
    calc
      _ ≤ dist ω.center p := dist_pt_line_shortest _ _ h₂
      _ < ω.radius := h₃
  haveI : PtNe (Inxpts h₁).front (Inxpts h₁).back := ⟨by
    contrapose! hs
    rw [(inx_pts_same_iff_tangent h₁).mp hs.symm]⟩
  have eq₁ : LIN (Inxpts h₁).front (Inxpts h₁).back = l := Line.eq_line_of_pt_pt_of_ne (inx_pts_lieson_dlin h₁).1 (inx_pts_lieson_dlin h₁).2
  have h₂' : p LiesOn (LIN (Inxpts h₁).front (Inxpts h₁).back) := by
    rw [eq₁]
    exact h₂
  have eq₂ : perp_foot ω.center l = (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint := by
    rw [← pts_lieson_circle_perpfoot_eq_midpoint (inx_pts_lieson_circle h₁).1 (inx_pts_lieson_circle h₁).2, eq₁]
  have trieq₁ : (dist p (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint) ^ 2 = (dist ω.center p) ^ 2 - (dist ω.center (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint) ^ 2 := by
    rw [← eq₂, eq_sub_iff_add_eq, add_comm, ← Seg.length_eq_dist, ← Seg.length_eq_dist, ← Seg.length_eq_dist]
    apply Pythagoras_of_perp_foot _ _ h₂
  have trieq₂ : (dist (Inxpts h₁).front (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint) ^ 2 = (dist ω.center (Inxpts h₁).front) ^ 2 - (dist ω.center (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint) ^ 2 := by
    rw [← eq₂, eq_sub_iff_add_eq, add_comm, ← Seg.length_eq_dist, ← Seg.length_eq_dist, ← Seg.length_eq_dist]
    apply Pythagoras_of_perp_foot _ _ (inx_pts_lieson_dlin h₁).1
  have hgt : dist p (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint < dist (Inxpts h₁).front (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint := by
    calc
      _ = |dist p (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint| := by rw [abs_of_nonneg dist_nonneg]
      _ < |dist (Inxpts h₁).front (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint| := by
        apply sq_lt_sq.mp
        rw [trieq₁, trieq₂]
        simp
        apply sq_lt_sq.mpr
        rw [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg, (inx_pts_lieson_circle h₁).1]
        exact h₃
      _ = dist (Inxpts h₁).front (SEG (Inxpts h₁).front (Inxpts h₁).back).midpoint := by rw [abs_of_nonneg dist_nonneg]
  apply (lies_int_seg_nd_iff_lies_on_ray_reverse h₂').mp
  exact ((SEG_nd (Inxpts h₁).front (Inxpts h₁).back).dist_midpt_lt_iff_lies_int_of_lies_on_toLine h₂').mp hgt

end Circle

end position

section power

namespace Circle

theorem circle_power_thm {ω : Circle P} {p : P} {l : DirLine P} (h₁ : DirLine.IsIntersected l ω) (h₂ : p LiesOn l) : ⟪VEC p (Inxpts h₁).front, VEC p (Inxpts h₁).back⟫_ℝ = power ω p := by
  rcases intersect_iff_tangent_or_secant.mp h₁ with h | h
  · have heq : (Inxpts h₁).back = (Inxpts h₁).front := (inx_pts_same_iff_tangent h₁).mpr h
    rw [heq, Vec.real_inner_apply _ _, ← Vec.norm_sq]
    calc
      _ = (dist p (Tangentpt h)) ^ 2 := by
        rw [dist_comm, NormedAddTorsor.dist_eq_norm']
        rfl
      _ = power ω p := tangent_length_sq_eq_power _ h₂
  haveI : PtNe (Inxpts h₁).back (Inxpts h₁).front := ⟨by
    have h : dist_pt_line ω.center l.toLine < ω.radius := h
    contrapose! h
    have : dist_pt_line ω.center l.toLine = ω.radius := (inx_pts_same_iff_tangent h₁).mp h
    rw [this]
    ⟩
  have heq : - VEC (perp_foot ω.center l) (Inxpts h₁).front = VEC (perp_foot ω.center l) (Inxpts h₁).back := by
    calc
      _ = VEC (Inxpts h₁).front (perp_foot ω.center l) := by rw [neg_vec]
      _ = VEC (Inxpts h₁).front (perp_foot ω.center (LIN (Inxpts h₁).front (Inxpts h₁).back)) := by
        congr; symm
        apply Line.eq_line_of_pt_pt_of_ne (inx_pts_lieson_dlin h₁).1 (inx_pts_lieson_dlin h₁).2
      _ = VEC (perp_foot ω.center (LIN (Inxpts h₁).front (Inxpts h₁).back)) (Inxpts h₁).back := by
        apply pts_lieson_circle_vec_eq (inx_pts_lieson_circle h₁).1 (inx_pts_lieson_circle h₁).2
      _ = VEC (perp_foot ω.center l) (Inxpts h₁).back := by
        congr
        apply Line.eq_line_of_pt_pt_of_ne (inx_pts_lieson_dlin h₁).1 (inx_pts_lieson_dlin h₁).2
  have eq₁ : (dist p (perp_foot ω.center l)) ^ 2 = (dist ω.center p) ^ 2 - (dist ω.center (perp_foot ω.center l)) ^ 2 := by
    rw [eq_sub_iff_add_eq, add_comm, ← Seg.length_eq_dist, ← Seg.length_eq_dist, ← Seg.length_eq_dist]
    apply Pythagoras_of_perp_foot _ _ h₂
  have eq₂ : (dist (Inxpts h₁).front (perp_foot ω.center l)) ^ 2 = (dist ω.center (Inxpts h₁).front) ^ 2 - (dist ω.center (perp_foot ω.center l)) ^ 2 := by
    rw [eq_sub_iff_add_eq, add_comm, ← Seg.length_eq_dist, ← Seg.length_eq_dist, ← Seg.length_eq_dist]
    apply Pythagoras_of_perp_foot _ _ (inx_pts_lieson_dlin h₁).1
  calc
    _ = ⟪VEC p (perp_foot ω.center l) + VEC (perp_foot ω.center l) (Inxpts h₁).front, VEC p (perp_foot ω.center l) + VEC (perp_foot ω.center l) (Inxpts h₁).back⟫_ℝ := by rw [vec_add_vec, vec_add_vec]
    _ = ⟪VEC p (perp_foot ω.center l) + VEC (perp_foot ω.center l) (Inxpts h₁).front, VEC p (perp_foot ω.center l) - VEC (perp_foot ω.center l) (Inxpts h₁).front⟫_ℝ := by rw [← heq, sub_eq_add_neg]
    _ = ‖VEC p (perp_foot ω.center l)‖ ^ 2 - ‖VEC (perp_foot ω.center l) (Inxpts h₁).front‖ ^ 2 := by
      rw [inner_add_left, inner_sub_right, inner_sub_right, Vec.norm_sq, Vec.norm_sq, ← Vec.real_inner_apply _ _, ← Vec.real_inner_apply _ _, add_comm, real_inner_comm]
      ring
    _ = (dist p (perp_foot ω.center l)) ^ 2 - (dist (Inxpts h₁).front (perp_foot ω.center l)) ^ 2 := by
      rw [dist_comm, NormedAddTorsor.dist_eq_norm', NormedAddTorsor.dist_eq_norm']
      rfl
    _ = ((dist ω.center p) ^ 2 - (dist ω.center (perp_foot ω.center l)) ^ 2) - ((dist ω.center (Inxpts h₁).front) ^ 2 - (dist ω.center (perp_foot ω.center l)) ^ 2) := by rw [eq₁, eq₂]
    _ = (dist ω.center p) ^ 2 - (dist ω.center (Inxpts h₁).front) ^ 2 := by ring
    _ = (dist ω.center p) ^ 2 - ω.radius ^ 2 := by rw [(inx_pts_lieson_circle h₁).1]
    _ = power ω p := rfl

theorem chord_power_thm {ω : Circle P} {p : P} {l : DirLine P} (h₁ : DirLine.IsIntersected l ω) (h₂ : p LiesOn l) (h₃ : p LiesInt ω) : (dist p (Inxpts h₁).front) * (dist p (Inxpts h₁).back) = - power ω p := by
  haveI hne : PtNe p (Inxpts h₁).front := ⟨(liesint_ne_inxpts h₁ h₂ h₃).1⟩
  have hl : (Inxpts h₁).back LiesOn (RAY p (Inxpts h₁).front).reverse := liesint_back_lieson_ray_front_reverse h₁ h₂ h₃
  rcases pt_lies_on_ray_rev_iff_vec_opposite_dir.mp hl with ⟨t, tnonpos, ht⟩
  have heq : dist p (Inxpts h₁).back = -t := by
    calc
      _ = ‖VEC p (Inxpts h₁).back‖ := by rw [dist_comm, NormedAddTorsor.dist_eq_norm']; rfl
      _ = ‖t • (RAY p (Inxpts h₁).front).toDir.unitVec‖ := by rw [← ht]; rfl
      _ = -t := by rw [norm_smul, Dir.norm_unitVec, mul_one, Real.norm_of_nonpos tnonpos]
  have ht' : VEC p (Inxpts h₁).back = (t * (dist p (Inxpts h₁).front)⁻¹) • (VEC p (Inxpts h₁).front) := by
    calc
      _ = t • (RAY p (Inxpts h₁).front).toDir.unitVec := by rw [← ht]; rfl
      _ = t • ((dist p (Inxpts h₁).front)⁻¹ • (VEC p (Inxpts h₁).front)) := by rw [dist_comm, NormedAddTorsor.dist_eq_norm']; rfl
      _ = (t * (dist p (Inxpts h₁).front)⁻¹) • (VEC p (Inxpts h₁).front) := by rw [smul_smul]
  symm
  calc
    _ = -⟪VEC p (Inxpts h₁).front, VEC p (Inxpts h₁).back⟫_ℝ := by rw [circle_power_thm h₁ h₂]
    _ = -⟪VEC p (Inxpts h₁).front, (t * (dist p (Inxpts h₁).front)⁻¹) • (VEC p (Inxpts h₁).front)⟫_ℝ := by rw [ht']
    _ = -(t * (dist p (Inxpts h₁).front)⁻¹) * ‖VEC p (Inxpts h₁).front‖ ^ 2 := by
      rw [real_inner_smul_right, Vec.real_inner_apply _ _, ← Vec.norm_sq]
      simp
    _ = (dist p (Inxpts h₁).front) * (dist p (Inxpts h₁).back) := by
      unfold Vec.mkPtPt
      rw [← NormedAddTorsor.dist_eq_norm', dist_comm, heq, neg_mul, mul_assoc, mul_comm, pow_two, inv_mul_cancel_left₀]
      simp
      apply dist_ne_zero.mpr hne.out.symm

theorem secant_power_thm {ω : Circle P} {p : P} {l : DirLine P} (h₁ : DirLine.IsIntersected l ω) (h₂ : p LiesOn l) (h₃ : p LiesOut ω) : (dist p (Inxpts h₁).front) * (dist p (Inxpts h₁).back) = power ω p := by
  haveI hne : PtNe p (Inxpts h₁).front := ⟨(liesout_ne_inxpts h₁ h₂ h₃).1⟩
  have hl : (Inxpts h₁).back LiesOn (RAY p (Inxpts h₁).front) := liesout_back_lieson_ray_front h₁ h₂ h₃
  rcases Ray.lies_on_iff.mp hl with ⟨t, tnonneg, ht⟩
  have heq : dist p (Inxpts h₁).back = t := by
    calc
      _ = ‖VEC p (Inxpts h₁).back‖ := by rw [dist_comm, NormedAddTorsor.dist_eq_norm']; rfl
      _ = ‖t • (RAY p (Inxpts h₁).front).toDir.unitVec‖ := by rw [← ht]; rfl
      _ = t := by rw [norm_smul, Dir.norm_unitVec, mul_one, Real.norm_of_nonneg tnonneg]
  have ht' : VEC p (Inxpts h₁).back = (t * (dist p (Inxpts h₁).front)⁻¹) • (VEC p (Inxpts h₁).front) := by
    calc
      _ = t • (RAY p (Inxpts h₁).front).toDir.unitVec := by rw [← ht]; rfl
      _ = t • ((dist p (Inxpts h₁).front)⁻¹ • (VEC p (Inxpts h₁).front)) := by rw [dist_comm, NormedAddTorsor.dist_eq_norm']; rfl
      _ = (t * (dist p (Inxpts h₁).front)⁻¹) • (VEC p (Inxpts h₁).front) := by rw [smul_smul]
  symm
  calc
    _ = ⟪VEC p (Inxpts h₁).front, VEC p (Inxpts h₁).back⟫_ℝ := by rw [circle_power_thm h₁ h₂]
    _ = ⟪VEC p (Inxpts h₁).front, (t * (dist p (Inxpts h₁).front)⁻¹) • (VEC p (Inxpts h₁).front)⟫_ℝ := by rw [ht']
    _ = (t * (dist p (Inxpts h₁).front)⁻¹) * ‖VEC p (Inxpts h₁).front‖ ^ 2 := by rw [real_inner_smul_right, Vec.real_inner_apply _ _, ← Vec.norm_sq]
    _ = (dist p (Inxpts h₁).front) * (dist p (Inxpts h₁).back) := by
      unfold Vec.mkPtPt
      rw [← NormedAddTorsor.dist_eq_norm', dist_comm, heq, mul_assoc, mul_comm, pow_two, inv_mul_cancel_left₀]
      apply dist_ne_zero.mpr hne.out.symm

end Circle

end power

section radical_axis

namespace Circle

end Circle

end radical_axis

end EuclidGeom
