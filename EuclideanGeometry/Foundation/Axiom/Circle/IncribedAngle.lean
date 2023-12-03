import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Position.Orientation_trash

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

def mk_pt_pt_circle (A B : P) {ω : Circle P} (h : B ≠ A) (ha : A LiesOn ω) (hb : B LiesOn ω) : Arc P where
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

instance : Fig Arc where
  carrier := Arc.carrier

instance : Interior Arc where
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

theorem liesint_complementary_arc_isnot_arc_endpts {β : Arc P} {p : P} (h : p LiesInt β.complement) : Isnot_arc_endpts p β := and_comm.mp h.2

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

def angle_mk_pt_arc (p : P) (β : Arc P) (h : Isnot_arc_endpts p β) : Angle P := ANG β.source p β.target h.1.symm h.2.symm

def cangle (β : Arc P) : Angle P := angle_mk_pt_arc β.circle.center β (arc_center_isnot_arc_endpts β)

protected def IsMajor (β : Arc P) : Prop := β.cangle.value.toReal < 0

protected def IsMinor (β : Arc P) : Prop := β.cangle.value.toReal > 0

protected def IsAntipode (A B : P) {ω : Circle P} (h : B ≠ A) (h₁ : A LiesOn ω) (h₂ : B LiesOn ω) : Prop := (ARC A B h h₁ h₂).cangle.value = π

theorem cangle_of_complementary_arc_are_opposite (β : Arc P) : β.cangle.value = - β.complement.cangle.value := by
  show ∠ β.source β.circle.center β.target (arc_center_isnot_arc_endpts β).1.symm (arc_center_isnot_arc_endpts β).2.symm = -∠ β.target β.circle.center β.source (arc_center_isnot_arc_endpts β).2.symm (arc_center_isnot_arc_endpts β).1.symm
  apply neg_value_of_rev_ang

end Arc

end angle


namespace Arc

theorem inscribed_angle_is_positive {p : P} {β : Arc P} (h : p LiesInt β.complement) : (angle_mk_pt_arc p β (liesint_complementary_arc_isnot_arc_endpts h)).value.IsPos := by
  unfold angle_mk_pt_arc
  apply liesonleft_angle_ispos β.endpts_ne (liesint_complementary_arc_liesonleft_dlin h)

theorem inscribed_angle_of_complementary_arc_is_negative {p : P} {β : Arc P} (h : p LiesInt β) : (angle_mk_pt_arc p β h.2).value.IsNeg := by
  unfold angle_mk_pt_arc
  apply liesonright_angle_isneg β.endpts_ne (liesint_arc_liesonright_dlin h)

theorem cangle_eq_two_times_inscribed_angle {p : P} {β : Arc P} (h₁ : p LiesOn β.circle) (h₂ : Isnot_arc_endpts p β) : β.cangle.value = 2 • (angle_mk_pt_arc p β h₂).value := sorry

theorem inscribed_angle_of_diameter_eq {p : P} {β : Arc P} (h₁ : p LiesInt β.complement) (h₂ : Arc.IsAntipode β.source β.target β.endpts_ne β.ison.1 β.ison.2) : (angle_mk_pt_arc p β h₁.2.symm).value = ((π / 2 : ℝ) : AngValue) := sorry

/-
The followings need a modification when the angle modulo π is constructed.
-/
theorem inscribed_angle_on_same_arc_is_invariant {A B : P} {β : Arc P} (h₁ : A LiesInt β) (h₂ : B LiesInt β) : (angle_mk_pt_arc A β h₁.2).value = (angle_mk_pt_arc B β h₂.2).value := sorry

theorem inscribed_angle_on_same_complementary_arc_is_invariant {A B : P} {β : Arc P} (h₁ : A LiesInt β.complement) (h₂ : B LiesInt β.complement) : (angle_mk_pt_arc A β (liesint_complementary_arc_isnot_arc_endpts h₁)).value = (angle_mk_pt_arc B β (liesint_complementary_arc_isnot_arc_endpts h₂)).value := sorry

theorem inscribed_angle_on_complementary_arc_difference_eq_pi {A B : P} {β : Arc P} (h₁ : A LiesInt β) (h₂ : B LiesInt β.complement) : (angle_mk_pt_arc A β h₁.2).value - (angle_mk_pt_arc B β (liesint_complementary_arc_isnot_arc_endpts h₂)).value = π := sorry

theorem angle_of_osculation : sorry := sorry

end Arc

end EuclidGeom
