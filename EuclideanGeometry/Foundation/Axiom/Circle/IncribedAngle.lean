import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex2
import EuclideanGeometry.Foundation.Axiom.Position.Orientation_trash
import EuclideanGeometry.Foundation.Axiom.Triangle.IsocelesTriangle_trash
import EuclideanGeometry.Foundation.Axiom.Basic.Angle_trash

noncomputable section
namespace EuclidGeom

open AngValue

@[ext]
structure Arc (P : Type _) [EuclideanPlane P] where
  source : P
  target : P
  circle : Circle P
  ison : (source LiesOn circle) ∧ (target LiesOn circle)
  endpts_ne : PtNe target source

variable {P : Type _} [EuclideanPlane P]

namespace Arc

attribute [instance] Arc.endpts_ne

protected def mk_pt_pt_circle (A B : P) {ω : Circle P} [h : PtNe B A] (ha : A LiesOn ω) (hb : B LiesOn ω) : Arc P where
  source := A
  target := B
  circle := ω
  ison := ⟨ha, hb⟩
  endpts_ne := h

end Arc

scoped notation "ARC" => Arc.mk_pt_pt_circle


section position

namespace Arc

protected def IsOn (p : P) (β : Arc P) : Prop := (p LiesOn β.circle) ∧ (¬ p LiesOnLeft (DLIN β.source β.target))

def Isnot_arc_endpts (p : P) (β : Arc P) : Prop := (p ≠ β.source) ∧ (p ≠ β.target)

instance (p : P) (β : Arc P) (h : Isnot_arc_endpts p β) : PtNe β.source p := ⟨h.1.symm⟩

instance (p : P) (β : Arc P) (h : Isnot_arc_endpts p β) : PtNe β.target p := ⟨h.2.symm⟩

protected def IsInt (p : P) (β : Arc P) : Prop := (Arc.IsOn p β) ∧ (Isnot_arc_endpts p β)

protected def carrier (β : Arc P) : Set P := { p : P | Arc.IsOn p β }

protected def interior (β : Arc P) : Set P := { p : P | Arc.IsInt p β }

instance : Fig (Arc P) P where
  carrier := Arc.carrier

instance : Interior (Arc P) P where
  interior := Arc.interior

theorem center_isnot_arc_endpts (β : Arc P) : Isnot_arc_endpts β.circle.center β := by
  constructor
  · intro h
    have : β.source LiesOn β.circle := β.ison.1
    rw [← h] at this
    unfold lies_on Fig.carrier Circle.instFigCircle Circle.carrier Circle.IsOn at this
    simp at this
    have : β.circle.radius > 0 := β.circle.rad_pos
    linarith
  intro h
  have : β.target LiesOn β.circle := β.ison.2
  rw [← h] at this
  unfold lies_on Fig.carrier Circle.instFigCircle Circle.carrier Circle.IsOn at this
  simp at this
  have : β.circle.radius > 0 := β.circle.rad_pos
  linarith

instance (β : Arc P) : PtNe β.source β.circle.center := ⟨ (center_isnot_arc_endpts β).1.symm ⟩
instance (β : Arc P) : PtNe β.target β.circle.center := ⟨ (center_isnot_arc_endpts β).2.symm ⟩

def complement (β : Arc P) : Arc P where
  source := β.target
  target := β.source
  circle := β.circle
  ison := and_comm.mp β.ison
  endpts_ne := β.endpts_ne.symm

lemma liesint_arc_not_lieson_dlin {β : Arc P} {p : P} (h : p LiesInt β) : ¬ (p LiesOn (DLIN β.source β.target)) := by
  intro hl
  have hl : p LiesOn (LIN β.source β.target) := hl
  have hco : colinear β.source β.target p := Line.pt_pt_linear hl
  have hco' : ¬ (colinear β.source β.target p) := Circle.three_pts_lieson_circle_not_colinear (hne₂ := ⟨h.2.2⟩) (hne₃ := ⟨ h.2.1.symm ⟩ ) β.ison.1 β.ison.2 h.1.1
  tauto

theorem liesint_arc_liesonright_dlin {β : Arc P} {p : P} (h : p LiesInt β) : p LiesOnRight (DLIN β.source β.target) := by
  have hnl : ¬ (p LiesOn (DLIN β.source β.target)) := liesint_arc_not_lieson_dlin h
  have hnll : ¬ (p LiesOnLeft (DLIN β.source β.target)) := h.1.2
  rcases DirLine.lieson_or_liesonleft_or_liesonright p (DLIN β.source β.target) with hh | (hh | hh)
  · exfalso; tauto
  · exfalso; tauto
  exact hh

theorem liesint_complementary_arc_liesonleft_dlin {β : Arc P} {p : P} (h : p LiesInt β.complement) : p LiesOnLeft (DLIN β.source β.target) := by
  have hh : p LiesOnRight (DLIN β.target β.source) := by apply liesint_arc_liesonright_dlin h
  apply liesonleft_iff_liesonright_reverse.mpr
  rw [← DirLine.pt_pt_rev_eq_rev]
  exact hh

end Arc

end position


section angle

namespace Arc

protected def angle_mk_pt_arc (p : P) (β : Arc P) (h : Isnot_arc_endpts p β) : Angle P := ANG β.source p β.target h.1.symm h.2.symm

protected def cangle (β : Arc P) : Angle P := Arc.angle_mk_pt_arc β.circle.center β (center_isnot_arc_endpts β)

protected def IsMajor (β : Arc P) : Prop := β.cangle.value.toReal < 0

protected def IsMinor (β : Arc P) : Prop := β.cangle.value.toReal > 0

protected def IsAntipode (A B : P) {ω : Circle P} [_h : PtNe B A] (h₁ : A LiesOn ω) (h₂ : B LiesOn ω) : Prop := (ARC A B h₁ h₂).cangle.value = π

theorem cangle_of_complementary_arc_are_opposite (β : Arc P) : β.cangle.value = - β.complement.cangle.value := by
  show (∠ β.source β.circle.center β.target = -∠ β.target β.circle.center β.source)
  apply neg_value_of_rev_ang

theorem antipode_iff_colinear (A B : P) {ω : Circle P} [h : PtNe B A] (h₁ : A LiesOn ω) (h₂ : B LiesOn ω) : Arc.IsAntipode A B h₁ h₂ ↔ colinear ω.center A B := by
  constructor
  · intro hh
    unfold Arc.IsAntipode Arc.cangle Arc.mk_pt_pt_circle Arc.angle_mk_pt_arc at hh
    simp at hh
    apply colinear_of_angle_eq_pi hh
  intro hh
  haveI : PtNe A ω.center := Circle.pt_lieson_ne_center h₁
  haveI : PtNe B ω.center := Circle.pt_lieson_ne_center h₂
  show ∠ A ω.center B = π
  have hl : B LiesOn LIN ω.center A := Line.pt_pt_maximal hh
  have heq₁ : VEC A ω.center = VEC ω.center B := by
    apply distinct_pts_same_dist_vec_eq hl
    rw [h₁, h₂]
  have heq₂ : VEC A B = (2 : ℝ) • (VEC A ω.center) := by
    calc
      _ = VEC A ω.center + VEC ω.center B := by rw [vec_add_vec]
      _ = (2 : ℝ) • (VEC A ω.center) := by rw [← heq₁, two_smul]
  have hli : ω.center LiesInt SEG_nd A B := by
    apply SegND.lies_int_iff.mpr
    use 2⁻¹
    constructor
    · norm_num
    constructor
    · norm_num
    show VEC A ω.center = 2⁻¹ • (VEC A B)
    rw [heq₂]
    simp
  apply liesint_segnd_value_eq_pi _ hli

theorem mk_pt_pt_diam_isantipode {A B : P} [h : PtNe A B] : Arc.IsAntipode A B (Circle.mk_pt_pt_diam_fst_lieson) (Circle.mk_pt_pt_diam_snd_lieson) := by
  have hc : colinear (SEG A B).midpoint A B := by
    apply perm_colinear_trd_fst_snd
    apply Line.pt_pt_linear
    show (SEG A B).midpoint LiesOn (SEG_nd A B).toLine
    apply SegND.lies_on_toLine_of_lie_on
    apply Seg.midpt_lies_on
  exact (antipode_iff_colinear _ _ (Circle.mk_pt_pt_diam_fst_lieson) (Circle.mk_pt_pt_diam_snd_lieson)).mpr hc

end Arc

end angle


theorem inscribed_angle_is_positive {p : P} {β : Arc P} (h : p LiesInt β.complement) : (Arc.angle_mk_pt_arc p β h.2.symm).value.IsPos := by
  unfold Arc.angle_mk_pt_arc
  apply liesonleft_angle_ispos (Arc.liesint_complementary_arc_liesonleft_dlin h)

theorem inscribed_angle_of_complementary_arc_is_negative {p : P} {β : Arc P} (h : p LiesInt β) : (Arc.angle_mk_pt_arc p β h.2).value.IsNeg := by
  unfold Arc.angle_mk_pt_arc
  apply liesonright_angle_isneg (Arc.liesint_arc_liesonright_dlin h)

theorem cangle_eq_two_times_inscribed_angle {p : P} {β : Arc P} (h₁ : p LiesOn β.circle) (h₂ : Arc.Isnot_arc_endpts p β) : β.cangle.value = 2 • (Arc.angle_mk_pt_arc p β h₂).value := by
  haveI ne : p ≠ β.circle.center := (Circle.pt_lieson_ne_center h₁).out
  have hit₁ : (▵ β.circle.center β.target p).IsIsoceles := by
    unfold Triangle.IsIsoceles
    show (SEG p β.circle.center).length = (SEG β.circle.center β.target).length
    rw [Seg.length_eq_dist, Seg.length_eq_dist, dist_comm, h₁, β.ison.2]
  have hit₂ : (▵ β.circle.center p β.source).IsIsoceles := by
    unfold Triangle.IsIsoceles
    show (SEG β.source β.circle.center).length = (SEG β.circle.center p).length
    rw [Seg.length_eq_dist, Seg.length_eq_dist, dist_comm, h₁, β.ison.1]
  have eq₁ : ∠ p β.target β.circle.center h₂.2 (Arc.center_isnot_arc_endpts β).2 = ∠ β.circle.center p β.target ne.symm h₂.2.symm := by apply is_isoceles_tri_ang_eq_ang_of_tri hit₁
  have eq₂ : ∠ β.source p β.circle.center h₂.1.symm ne.symm = ∠ β.circle.center β.source p (Arc.center_isnot_arc_endpts β).1 h₂.1 := by apply is_isoceles_tri_ang_eq_ang_of_tri hit₂
  have π₁ : ∠ β.target β.circle.center p (Arc.center_isnot_arc_endpts β).2.symm ne + ∠ p β.target β.circle.center h₂.2 (Arc.center_isnot_arc_endpts β).2 + ∠ β.circle.center p β.target ne.symm h₂.2.symm = π := by apply angle_sum_eq_pi_of_tri (▵ β.circle.center β.target p)
  have π₂ : ∠ p β.circle.center β.source ne (Arc.center_isnot_arc_endpts β).1.symm + ∠ β.source p β.circle.center h₂.1.symm ne.symm + ∠ β.circle.center β.source p (Arc.center_isnot_arc_endpts β).1 h₂.1 = π := by apply angle_sum_eq_pi_of_tri (▵ β.circle.center p β.source)
  have hsum₁ : ∠ β.target β.circle.center p (Arc.center_isnot_arc_endpts β).2.symm ne + ∠ p β.circle.center β.source ne (Arc.center_isnot_arc_endpts β).1.symm = ∠ β.target β.circle.center β.source (Arc.center_isnot_arc_endpts β).2.symm (Arc.center_isnot_arc_endpts β).1.symm := by
    have : (ANG β.target β.circle.center p (Arc.center_isnot_arc_endpts β).2.symm ne).end_ray = (ANG p β.circle.center β.source ne (Arc.center_isnot_arc_endpts β).1.symm).start_ray := rfl
    have hhs : (Angle.sum_adj this).value = ∠ β.target β.circle.center β.source (Arc.center_isnot_arc_endpts β).2.symm (Arc.center_isnot_arc_endpts β).1.symm := rfl
    rw [← hhs, Angle.ang_eq_ang_add_ang_mod_pi_of_adj_ang]
    rfl
  have hsum₂ : ∠ β.source p β.circle.center h₂.1.symm ne.symm + ∠ β.circle.center p β.target ne.symm h₂.2.symm = ∠ β.source p β.target h₂.1.symm h₂.2.symm := by
    have : (ANG β.source p β.circle.center h₂.1.symm ne.symm).end_ray = (ANG β.circle.center p β.target ne.symm h₂.2.symm).start_ray := rfl
    have hhs : (Angle.sum_adj this).value = ∠ β.source p β.target h₂.1.symm h₂.2.symm := rfl
    rw [← hhs, Angle.ang_eq_ang_add_ang_mod_pi_of_adj_ang]
    rfl
  have eq₃ : ∠ β.target β.circle.center β.source (Arc.center_isnot_arc_endpts β).2.symm (Arc.center_isnot_arc_endpts β).1.symm + 2 • (∠ β.source p β.target h₂.1.symm h₂.2.symm) = 0 := by
    calc
      _ = ∠ β.target β.circle.center p (Arc.center_isnot_arc_endpts β).2.symm ne + ∠ p β.circle.center β.source ne (Arc.center_isnot_arc_endpts β).1.symm + 2 • (∠ β.source p β.circle.center h₂.1.symm ne.symm + ∠ β.circle.center p β.target ne.symm h₂.2.symm) := by rw [hsum₁, hsum₂]
      _ = ∠ β.target β.circle.center p (Arc.center_isnot_arc_endpts β).2.symm ne + ∠ p β.circle.center β.source ne (Arc.center_isnot_arc_endpts β).1.symm + (∠ p β.target β.circle.center h₂.2 (Arc.center_isnot_arc_endpts β).2 + ∠ β.circle.center p β.target ne.symm h₂.2.symm) + (∠ β.source p β.circle.center h₂.1.symm ne.symm + ∠ β.circle.center β.source p (Arc.center_isnot_arc_endpts β).1 h₂.1) := by
        rw [← eq₂, eq₁, two_smul]
        abel
      _ = (∠ β.target β.circle.center p (Arc.center_isnot_arc_endpts β).2.symm ne + ∠ p β.target β.circle.center h₂.2 (Arc.center_isnot_arc_endpts β).2 + ∠ β.circle.center p β.target ne.symm h₂.2.symm) + (∠ p β.circle.center β.source ne (Arc.center_isnot_arc_endpts β).1.symm + ∠ β.source p β.circle.center h₂.1.symm ne.symm + ∠ β.circle.center β.source p (Arc.center_isnot_arc_endpts β).1 h₂.1) := by
        rw [add_assoc, add_add_add_comm]
        abel
      _ = 0 := by
        rw [π₁, π₂, ← coe_two_pi, two_mul]
        simp
  calc
    _ = - ∠ β.target β.circle.center β.source (Arc.center_isnot_arc_endpts β).2.symm (Arc.center_isnot_arc_endpts β).1.symm := by rw [← neg_value_of_rev_ang]; rfl
    _ = 2 • (∠ β.source p β.target h₂.1.symm h₂.2.symm) := by rw [← zero_sub, ← eq₃, add_sub_cancel']
    _ = 2 • (Arc.angle_mk_pt_arc p β h₂).value := rfl

theorem inscribed_angle_of_diameter_eq_mod_pi {p : P} {β : Arc P} (h₁ : p LiesOn β.circle) (h₂ : Arc.IsAntipode β.source β.target β.ison.1 β.ison.2) (h₃ : Arc.Isnot_arc_endpts p β) : (Arc.angle_mk_pt_arc p β h₃).dvalue = ∡[π / 2] := by
  have : β.cangle.value = π := h₂
  have : 2 • (Arc.angle_mk_pt_arc p β h₃).value = π := by
    rw [← this, ← cangle_eq_two_times_inscribed_angle]
    exact h₁
  rcases two_nsmul_eq_pi_iff.mp this with h | h
  · unfold Angle.dvalue
    rw [h]
  unfold Angle.dvalue
  rw [h, neg_div]
  simp

theorem inscribed_angle_of_diameter_eq_mod_pi_pt_pt_pt {A B C : P} {ω : Circle P} [hne₁ : PtNe A B] [hne₂ : PtNe B C] [hne₃ : PtNe C A] (h₁ : A LiesOn ω) (h₂ : B LiesOn ω) (h₃ : C LiesOn ω) (h : Arc.IsAntipode A B h₁ h₂) : ∠ A C B = ∡[π / 2] := by
  let β : Arc P := ARC A B h₁ h₂
  have hh₁ : C LiesOn β.circle := h₃
  have hh₂ : Arc.IsAntipode β.source β.target β.ison.1 β.ison.2 := h
  have hh₃ : Arc.Isnot_arc_endpts C β := ⟨hne₃.out, hne₂.out.symm⟩
  apply inscribed_angle_of_diameter_eq_mod_pi hh₁ hh₂ hh₃

theorem inscribed_angle_on_same_arc_is_invariant_mod_pi {A B : P} {β : Arc P} (h₁ : A LiesOn β.circle) (h₂ : B LiesOn β.circle) (hne₁ : Arc.Isnot_arc_endpts A β) (hne₂ : Arc.Isnot_arc_endpts B β) : (Arc.angle_mk_pt_arc A β hne₁).dvalue = (Arc.angle_mk_pt_arc B β hne₂).dvalue := by
  have eq : 2 • (Arc.angle_mk_pt_arc A β hne₁).value = 2 • (Arc.angle_mk_pt_arc B β hne₂).value := by rw [← cangle_eq_two_times_inscribed_angle h₁ hne₁, ← cangle_eq_two_times_inscribed_angle h₂ hne₂]
  exact coe_eq_coe_iff_two_nsmul_eq.mpr eq


namespace Arc

protected def iangle (β : Arc P) : AngDValue := sorry

theorem inscribed_angle_dvalue_eq_iangle {p : P} {β : Arc P} (h₁ : p LiesOn β.circle) (h₂ : Isnot_arc_endpts p β) : (Arc.angle_mk_pt_arc p β h₂).dvalue = β.iangle := by
  sorry

theorem angle_of_osculation : sorry := sorry

end Arc

end EuclidGeom
