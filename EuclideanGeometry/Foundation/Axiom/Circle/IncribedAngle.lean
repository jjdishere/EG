import EuclideanGeometry.Foundation.Axiom.Circle.Basic

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

protected def IsOn (p : P) (β : Arc P) : Prop := (p LiesOn β.circle) ∧ (¬ p LiesOnLeft (RAY β.source β.target β.endpts_ne))

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

theorem isint_complementary_arc_isnot_arc_endpts {β : Arc P} {p : P} (h : p LiesInt β.complement) : Isnot_arc_endpts p β := and_comm.mp h.2

end Arc

end position


section angle

namespace Arc

def angle_mk_pt_arc (p : P) (β : Arc P) (h : Isnot_arc_endpts p β) : Angle P := ANG β.source p β.target h.1.symm h.2.symm

def cangle (β : Arc P) : Angle P := angle_mk_pt_arc β.circle.center β (arc_center_isnot_arc_endpts β)

protected def IsMajor (β : Arc P) : Prop := β.cangle.value.toReal < 0

protected def IsMinor (β : Arc P) : Prop := β.cangle.value.toReal > 0

protected def IsAntipode (A B : P) {ω : Circle P} (h : B ≠ A) (h₁ : A LiesOn ω) (h₂ : B LiesOn ω) : Prop := (ARC A B h h₁ h₂).cangle.value = π

theorem cangle_of_complementary_arc_are_opposite (β : Arc P) : β.cangle.value = - β.complement.cangle.value := sorry

end Arc

end angle


namespace Arc

theorem inscribed_angle_is_positive {p : P} {β : Arc P} (h : p LiesInt β.complement) : (angle_mk_pt_arc p β (isint_complementary_arc_isnot_arc_endpts h)).value.IsPos := sorry

theorem inscribed_angle_of_complementary_arc_is_negative {p : P} {β : Arc P} (h : p LiesInt β) : (angle_mk_pt_arc p β h.2).value.IsNeg := sorry

theorem cangle_eq_two_times_inscribed_angle {p : P} {β : Arc P} (h₁ : p LiesOn β.circle) (h₂ : Isnot_arc_endpts p β) : β.cangle.value = 2 • (angle_mk_pt_arc p β h₂).value := sorry

/-
The followings need a modification when the angle modulo π is constructed.
-/
theorem inscribed_angle_on_same_arc_is_invariant {A B : P} {β : Arc P} (h₁ : A LiesInt β) (h₂ : B LiesInt β) : (angle_mk_pt_arc A β h₁.2).value = (angle_mk_pt_arc B β h₂.2).value := sorry

theorem inscribed_angle_on_same_complementary_arc_is_invariant {A B : P} {β : Arc P} (h₁ : A LiesInt β.complement) (h₂ : B LiesInt β.complement) : (angle_mk_pt_arc A β (isint_complementary_arc_isnot_arc_endpts h₁)).value = (angle_mk_pt_arc B β (isint_complementary_arc_isnot_arc_endpts h₂)).value := sorry

theorem inscribed_angle_on_complementary_arc_difference_eq_pi {A B : P} {β : Arc P} (h₁ : A LiesInt β) (h₂ : B LiesInt β.complement) : (angle_mk_pt_arc A β h₁.2).value - (angle_mk_pt_arc B β (isint_complementary_arc_isnot_arc_endpts h₂)).value = π := sorry

theorem angle_of_osculation : sorry := sorry

end Arc

end EuclidGeom
