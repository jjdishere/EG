import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex2
import EuclideanGeometry.Foundation.Axiom.Position.Orientation_trash
import EuclideanGeometry.Foundation.Axiom.Triangle.IsocelesTriangle_trash
import EuclideanGeometry.Foundation.Axiom.Basic.Angle_trash

noncomputable section
namespace EuclidGeom

@[ext]
structure Arc (P : Type _) [EuclideanPlane P] where
  source : P
  target : P
  circle : Circle P
  ison : (source LiesOn circle) ∧ (target LiesOn circle)
  endpts_ne : target ≠ source

variable {P : Type _} [EuclideanPlane P]

namespace Arc

protected def mk_pt_pt_circle (A B : P) {ω : Circle P} (h : B ≠ A) (ha : A LiesOn ω) (hb : B LiesOn ω) : Arc P where
  source := A
  target := B
  circle := ω
  ison := ⟨ha, hb⟩
  endpts_ne := h

end Arc

scoped notation "ARC" => Arc.mk_pt_pt_circle


section position

namespace Arc

protected def IsOn (p : P) (β : Arc P) : Prop := (p LiesOn β.circle) ∧ (¬ p LiesOnLeft (DLIN β.source β.target β.endpts_ne))

def Isnot_arc_endpts (p : P) (β : Arc P) : Prop := (p ≠ β.source) ∧ (p ≠ β.target)

protected def IsInt (p : P) (β : Arc P) : Prop := (Arc.IsOn p β) ∧ (Isnot_arc_endpts p β)

protected def carrier (β : Arc P) : Set P := { p : P | Arc.IsOn p β }

protected def interior (β : Arc P) : Set P := { p : P | Arc.IsInt p β }

instance : Fig (Arc P) P where
  carrier := Arc.carrier

instance : Interior (Arc P) P where
  interior := Arc.interior

theorem arc_center_isnot_arc_endpts (β : Arc P) : Isnot_arc_endpts β.circle.center β := by
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

def complement (β : Arc P) : Arc P where
  source := β.target
  target := β.source
  circle := β.circle
  ison := and_comm.mp β.ison
  endpts_ne := β.endpts_ne.symm

lemma liesint_arc_not_lieson_dlin {β : Arc P} {p : P} (h : p LiesInt β) : ¬ (p LiesOn (DLIN β.source β.target β.endpts_ne)) := by
  intro hl
  have hl : p LiesOn (LIN β.source β.target β.endpts_ne) := hl
  have hco : colinear β.source β.target p := Line.pt_pt_linear β.endpts_ne hl
  have hco' : ¬ (colinear β.source β.target p) := Circle.three_pts_lieson_circle_not_colinear β.endpts_ne h.2.2 h.2.1.symm β.ison.1 β.ison.2 h.1.1
  tauto

theorem liesint_arc_liesonright_dlin {β : Arc P} {p : P} (h : p LiesInt β) : p LiesOnRight (DLIN β.source β.target β.endpts_ne) := by
  have hnl : ¬ (p LiesOn (DLIN β.source β.target β.endpts_ne)) := liesint_arc_not_lieson_dlin h
  have hnll : ¬ (p LiesOnLeft (DLIN β.source β.target β.endpts_ne)) := h.1.2
  rcases DirLine.lieson_or_liesonleft_or_liesonright p (DLIN β.source β.target β.endpts_ne) with hh | (hh | hh)
  · exfalso; tauto
  · exfalso; tauto
  exact hh

theorem liesint_complementary_arc_liesonleft_dlin {β : Arc P} {p : P} (h : p LiesInt β.complement) : p LiesOnLeft (DLIN β.source β.target β.endpts_ne) := by
  have hh : p LiesOnRight (DLIN β.target β.source β.endpts_ne.symm) := by apply liesint_arc_liesonright_dlin h
  apply liesonleft_iff_liesonright_reverse.mpr
  rw [← DirLine.pt_pt_rev_eq_rev β.endpts_ne]
  exact hh

end Arc

end position


section angle

namespace Arc

protected def angle_mk_pt_arc (p : P) (β : Arc P) (h : Isnot_arc_endpts p β) : Angle P := ANG β.source p β.target h.1.symm h.2.symm

protected def cangle (β : Arc P) : Angle P := Arc.angle_mk_pt_arc β.circle.center β (arc_center_isnot_arc_endpts β)

protected def IsMajor (β : Arc P) : Prop := β.cangle.value.toReal < 0

protected def IsMinor (β : Arc P) : Prop := β.cangle.value.toReal > 0

protected def IsAntipode (A B : P) {ω : Circle P} (h : B ≠ A) (h₁ : A LiesOn ω) (h₂ : B LiesOn ω) : Prop := (ARC A B h h₁ h₂).cangle.value = π

theorem cangle_of_complementary_arc_are_opposite (β : Arc P) : β.cangle.value = - β.complement.cangle.value := by
  show ∠ β.source β.circle.center β.target (arc_center_isnot_arc_endpts β).1.symm (arc_center_isnot_arc_endpts β).2.symm = -∠ β.target β.circle.center β.source (arc_center_isnot_arc_endpts β).2.symm (arc_center_isnot_arc_endpts β).1.symm
  apply neg_value_of_rev_ang

theorem antipode_iff_colinear (A B : P) {ω : Circle P} (h : B ≠ A) (h₁ : A LiesOn ω) (h₂ : B LiesOn ω) : Arc.IsAntipode A B h h₁ h₂ ↔ colinear ω.center A B := by
  constructor
  · intro hh
    unfold Arc.IsAntipode Arc.cangle Arc.mk_pt_pt_circle Arc.angle_mk_pt_arc at hh
    simp at hh
    apply colinear_of_angle_eq_pi hh
  intro hh
  sorry

end Arc

end angle


namespace Arc

theorem inscribed_angle_is_positive {p : P} {β : Arc P} (h : p LiesInt β.complement) : (Arc.angle_mk_pt_arc p β h.2.symm).value.IsPos := by
  unfold Arc.angle_mk_pt_arc
  apply liesonleft_angle_ispos β.endpts_ne (liesint_complementary_arc_liesonleft_dlin h)

theorem inscribed_angle_of_complementary_arc_is_negative {p : P} {β : Arc P} (h : p LiesInt β) : (Arc.angle_mk_pt_arc p β h.2).value.IsNeg := by
  unfold Arc.angle_mk_pt_arc
  apply liesonright_angle_isneg β.endpts_ne (liesint_arc_liesonright_dlin h)

theorem cangle_eq_two_times_inscribed_angle {p : P} {β : Arc P} (h₁ : p LiesOn β.circle) (h₂ : Isnot_arc_endpts p β) : β.cangle.value = 2 • (Arc.angle_mk_pt_arc p β h₂).value := by
  have ne : p ≠ β.circle.center := Circle.pt_lieson_ne_center h₁
  have hit₁ : (▵ β.circle.center β.target p).IsIsoceles := by
    unfold Triangle.IsIsoceles
    show (SEG p β.circle.center).length = (SEG β.circle.center β.target).length
    rw [Seg.length_eq_dist, Seg.length_eq_dist, dist_comm, h₁, β.ison.2]
  have hit₂ : (▵ β.circle.center p β.source).IsIsoceles := by
    unfold Triangle.IsIsoceles
    show (SEG β.source β.circle.center).length = (SEG β.circle.center p).length
    rw [Seg.length_eq_dist, Seg.length_eq_dist, dist_comm, h₁, β.ison.1]
  have eq₁ : ∠ p β.target β.circle.center h₂.2 (arc_center_isnot_arc_endpts β).2 = ∠ β.circle.center p β.target ne.symm h₂.2.symm := by apply is_isoceles_tri_ang_eq_ang_of_tri hit₁
  have eq₂ : ∠ β.source p β.circle.center h₂.1.symm ne.symm = ∠ β.circle.center β.source p (arc_center_isnot_arc_endpts β).1 h₂.1 := by apply is_isoceles_tri_ang_eq_ang_of_tri hit₂
  have π₁ : ∠ β.target β.circle.center p (arc_center_isnot_arc_endpts β).2.symm ne + ∠ p β.target β.circle.center h₂.2 (arc_center_isnot_arc_endpts β).2 + ∠ β.circle.center p β.target ne.symm h₂.2.symm = π := by apply angle_sum_eq_pi_of_tri (▵ β.circle.center β.target p)
  have π₂ : ∠ p β.circle.center β.source ne (arc_center_isnot_arc_endpts β).1.symm + ∠ β.source p β.circle.center h₂.1.symm ne.symm + ∠ β.circle.center β.source p (arc_center_isnot_arc_endpts β).1 h₂.1 = π := by apply angle_sum_eq_pi_of_tri (▵ β.circle.center p β.source)
  have hsum₁ : ∠ β.target β.circle.center p (arc_center_isnot_arc_endpts β).2.symm ne + ∠ p β.circle.center β.source ne (arc_center_isnot_arc_endpts β).1.symm = ∠ β.target β.circle.center β.source (arc_center_isnot_arc_endpts β).2.symm (arc_center_isnot_arc_endpts β).1.symm := by
    have : (ANG β.target β.circle.center p (arc_center_isnot_arc_endpts β).2.symm ne).end_ray = (ANG p β.circle.center β.source ne (arc_center_isnot_arc_endpts β).1.symm).start_ray := rfl
    have hhs : (Angle.sum_adj this).value = ∠ β.target β.circle.center β.source (arc_center_isnot_arc_endpts β).2.symm (arc_center_isnot_arc_endpts β).1.symm := rfl
    rw [← hhs, Angle.ang_eq_ang_add_ang_mod_pi_of_adj_ang]
    rfl
  have hsum₂ : ∠ β.source p β.circle.center h₂.1.symm ne.symm + ∠ β.circle.center p β.target ne.symm h₂.2.symm = ∠ β.source p β.target h₂.1.symm h₂.2.symm := by
    have : (ANG β.source p β.circle.center h₂.1.symm ne.symm).end_ray = (ANG β.circle.center p β.target ne.symm h₂.2.symm).start_ray := rfl
    have hhs : (Angle.sum_adj this).value = ∠ β.source p β.target h₂.1.symm h₂.2.symm := rfl
    rw [← hhs, Angle.ang_eq_ang_add_ang_mod_pi_of_adj_ang]
    rfl
  have eq₃ : ∠ β.target β.circle.center β.source (arc_center_isnot_arc_endpts β).2.symm (arc_center_isnot_arc_endpts β).1.symm + 2 • (∠ β.source p β.target h₂.1.symm h₂.2.symm) = 0 := by
    calc
      _ = ∠ β.target β.circle.center p (arc_center_isnot_arc_endpts β).2.symm ne + ∠ p β.circle.center β.source ne (arc_center_isnot_arc_endpts β).1.symm + 2 • (∠ β.source p β.circle.center h₂.1.symm ne.symm + ∠ β.circle.center p β.target ne.symm h₂.2.symm) := by rw [hsum₁, hsum₂]
      _ = ∠ β.target β.circle.center p (arc_center_isnot_arc_endpts β).2.symm ne + ∠ p β.circle.center β.source ne (arc_center_isnot_arc_endpts β).1.symm + (∠ p β.target β.circle.center h₂.2 (arc_center_isnot_arc_endpts β).2 + ∠ β.circle.center p β.target ne.symm h₂.2.symm) + (∠ β.source p β.circle.center h₂.1.symm ne.symm + ∠ β.circle.center β.source p (arc_center_isnot_arc_endpts β).1 h₂.1) := by
        rw [← eq₂, eq₁, two_smul]
        abel
      _ = (∠ β.target β.circle.center p (arc_center_isnot_arc_endpts β).2.symm ne + ∠ p β.target β.circle.center h₂.2 (arc_center_isnot_arc_endpts β).2 + ∠ β.circle.center p β.target ne.symm h₂.2.symm) + (∠ p β.circle.center β.source ne (arc_center_isnot_arc_endpts β).1.symm + ∠ β.source p β.circle.center h₂.1.symm ne.symm + ∠ β.circle.center β.source p (arc_center_isnot_arc_endpts β).1 h₂.1) := by
        rw [add_assoc, add_add_add_comm]
        abel
      _ = 0 := by
        rw [π₁, π₂, ← AngValue.coe_two_pi, two_mul]
        simp
  calc
    _ = - ∠ β.target β.circle.center β.source (arc_center_isnot_arc_endpts β).2.symm (arc_center_isnot_arc_endpts β).1.symm := by rw [← neg_value_of_rev_ang]; rfl
    _ = 2 • (∠ β.source p β.target h₂.1.symm h₂.2.symm) := by rw [← zero_sub, ← eq₃, add_sub_cancel']
    _ = 2 • (Arc.angle_mk_pt_arc p β h₂).value := rfl

theorem inscribed_angle_of_diameter_eq_mod_pi {p : P} {β : Arc P} (h₁ : p LiesOn β.circle) (h₂ : Arc.IsAntipode β.source β.target β.endpts_ne β.ison.1 β.ison.2) (h₃ : Isnot_arc_endpts p β) : (Arc.angle_mk_pt_arc p β h₃).dvalue = ((π / 2 : ℝ) : AngDValue) := by
  have : β.cangle.value = π := h₂
  have : 2 • (Arc.angle_mk_pt_arc p β h₃).value = π := by
    rw [← this, ← cangle_eq_two_times_inscribed_angle]
    exact h₁
  rcases AngValue.two_nsmul_eq_pi_iff.mp this with h | h
  · unfold Angle.dvalue
    rw [h]
  unfold Angle.dvalue
  rw [h, neg_div]
  simp

theorem inscribed_angle_on_same_arc_is_invariant_mod_pi {A B : P} {β : Arc P} (h₁ : A LiesOn β.circle) (h₂ : B LiesOn β.circle) (hne₁ : Isnot_arc_endpts A β) (hne₂ : Isnot_arc_endpts B β) : (Arc.angle_mk_pt_arc A β hne₁).dvalue = (Arc.angle_mk_pt_arc B β hne₂).dvalue := by
  have eq : 2 • (Arc.angle_mk_pt_arc A β hne₁).value = 2 • (Arc.angle_mk_pt_arc B β hne₂).value := by rw [← cangle_eq_two_times_inscribed_angle h₁ hne₁, ← cangle_eq_two_times_inscribed_angle h₂ hne₂]
  apply (two_smul_value_eq_iff_dvalue_eq _ _).mp eq


protected def iangle (β : Arc P) : AngDValue := sorry

theorem inscribed_angle_dvalue_eq_iangle {p : P} {β : Arc P} (h₁ : p LiesOn β.circle) (h₂ : Isnot_arc_endpts p β) : (Arc.angle_mk_pt_arc p β h₂).dvalue = β.iangle := by
  sorry

theorem angle_of_osculation : sorry := sorry

end Arc

end EuclidGeom
