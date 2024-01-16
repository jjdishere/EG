import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex2
import EuclideanGeometry.Foundation.Axiom.Triangle.IsocelesTriangle_trash
import EuclideanGeometry.Foundation.Axiom.Basic.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_ex

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] (ω : Circle P)

open AngValue Angle Circle

section angle -- need a change

def Circle.angle_mk_pt_arc (p : P) (β : Arc P ω) (h : Arc.Isnot_arc_endpts ω p β) : Angle P := ANG β.source p β.target h.1.symm h.2.symm

namespace Arc

protected def cangle (β : Arc P ω) : Angle P := angle_mk_pt_arc ω ω.center β (center_isnot_arc_endpts ω β)

protected def IsMajor (β : Arc P ω) : Prop := (β.cangle ω).value.toReal < 0

protected def IsMinor (β : Arc P ω) : Prop := (β.cangle ω).value.toReal > 0

end Arc

end angle

-- protected def IsAntipode (A B : P) {ω : Circle P} [_h : PtNe B A] (h₁ : A LiesOn ω) (h₂ : B LiesOn ω) : Prop := (ARC A B h₁ h₂).cangle.value = π

namespace Circle

theorem cangle_of_complementary_arc_are_opposite (β : Arc P ω) : (β.cangle ω).value = - (Arc.cangle ω β.complement).value := by
  show (∠ β.source ω.center β.target = -∠ β.target ω.center β.source)
  apply neg_value_of_rev_ang

theorem inscribed_angle_is_positive {p : P} {β : Arc P ω} (h : p LiesInt β.complement) : (angle_mk_pt_arc ω p β h.2.symm).value.IsPos := by
  unfold angle_mk_pt_arc
  apply TriangleND.liesonleft_angle_ispos
  exact (Arc.pt_liesint_complementary_liesonleft_dlin ω h)

theorem inscribed_angle_of_complementary_arc_is_negative {p : P} {β : Arc P ω} (h : p LiesInt β) : (angle_mk_pt_arc ω p β h.2).value.IsNeg := by
  unfold angle_mk_pt_arc
  apply TriangleND.liesonright_angle_isneg
  exact (Arc.pt_liesint_liesonright_dlin ω h)

theorem cangle_eq_two_times_inscribed_angle {p : P} {β : Arc P ω} (h₁ : p LiesOn ω) (h₂ : Arc.Isnot_arc_endpts ω p β) : (β.cangle ω).value = 2 • (angle_mk_pt_arc ω p β h₂).value := by
  haveI : PtNe p β.source := ⟨h₂.1⟩
  haveI : PtNe p β.target := ⟨h₂.2⟩
  haveI : PtNe p ω.center := Circle.pt_lieson_ne_center h₁
  have hit₁ : (▵ ω.center β.target p).IsIsoceles := by
    unfold Triangle.IsIsoceles
    show (SEG p ω.center).length = (SEG ω.center β.target).length
    rw [Seg.length_eq_dist, Seg.length_eq_dist, dist_comm, h₁, β.ison.2]
  have hit₂ : (▵ ω.center p β.source).IsIsoceles := by
    unfold Triangle.IsIsoceles
    show (SEG β.source ω.center).length = (SEG ω.center p).length
    rw [Seg.length_eq_dist, Seg.length_eq_dist, dist_comm, h₁, β.ison.1]
  have eq₁ : ∠ p β.target ω.center = ∠ ω.center p β.target := by apply is_isoceles_tri_ang_eq_ang_of_tri hit₁
  have eq₂ : ∠ β.source p ω.center = ∠ ω.center β.source p := by apply is_isoceles_tri_ang_eq_ang_of_tri hit₂
  have π₁ : ∠ β.target ω.center p + ∠ p β.target ω.center + ∠ ω.center p β.target = π := by apply angle_sum_eq_pi_of_tri (▵ ω.center β.target p)
  have π₂ : ∠ p ω.center β.source + ∠ β.source p ω.center + ∠ ω.center β.source p = π := by apply angle_sum_eq_pi_of_tri (▵ ω.center p β.source)
  have hsum₁ : ∠ β.target ω.center p + ∠ p ω.center β.source = ∠ β.target ω.center β.source := by
    have : (ANG β.target ω.center p).end_ray = (ANG p ω.center β.source).start_ray := rfl
    have hhs : (Angle.sum_adj this).value = ∠ β.target ω.center β.source := rfl
    rw [← hhs, Angle.ang_eq_ang_add_ang_mod_pi_of_adj_ang]
  have hsum₂ : ∠ β.source p ω.center + ∠ ω.center p β.target = ∠ β.source p β.target := by
    have : (ANG β.source p ω.center).end_ray = (ANG ω.center p β.target).start_ray := rfl
    have hhs : (Angle.sum_adj this).value = ∠ β.source p β.target := rfl
    rw [← hhs, Angle.ang_eq_ang_add_ang_mod_pi_of_adj_ang]
  have eq₃ : ∠ β.target ω.center β.source + 2 • (∠ β.source p β.target) = 0 := by
    calc
      _ = ∠ β.target ω.center p + ∠ p ω.center β.source + 2 • (∠ β.source p ω.center + ∠ ω.center p β.target) := by rw [hsum₁, hsum₂]
      _ = ∠ β.target ω.center p + ∠ p ω.center β.source + (∠ p β.target ω.center + ∠ ω.center p β.target) + (∠ β.source p ω.center + ∠ ω.center β.source p) := by
        rw [← eq₂, eq₁, two_smul]
        abel
      _ = (∠ β.target ω.center p + ∠ p β.target ω.center + ∠ ω.center p β.target) + (∠ p ω.center β.source + ∠ β.source p ω.center + ∠ ω.center β.source p) := by
        rw [add_assoc, add_add_add_comm]
        abel
      _ = 0 := by
        rw [π₁, π₂, ← coe_two_pi, two_mul]
        simp
  calc
    _ = - ∠ β.target ω.center β.source := by rw [← neg_value_of_rev_ang]; rfl
    _ = 2 • (∠ β.source p β.target) := by rw [← zero_sub, ← eq₃, add_sub_cancel']
    _ = 2 • (angle_mk_pt_arc ω p β h₂).value := rfl

/-
theorem inscribed_angle_of_diameter_eq_mod_pi {p : P} {β : Arc P ω} (h₁ : p LiesOn ω) (h₂ : Arc.IsAntipode β.source β.target β.ison.1 β.ison.2) (h₃ : Arc.Isnot_arc_endpts p β) : (angle_mk_pt_Arc P ω β h₃).dvalue = ∡[π / 2] := by
  have : β.cangle.value = π := h₂
  have : 2 • (angle_mk_pt_Arc P ω β h₃).value = π := by
    rw [← this, ← cangle_eq_two_times_inscribed_angle]
    exact h₁
  rcases two_nsmul_eq_pi_iff.mp this with h | h
  · unfold Angle.dvalue
    rw [h]
  unfold Angle.dvalue
  rw [h, neg_div]
  simp

theorem inscribed_angle_of_diameter_eq_mod_pi_pt_pt_pt {A B C : P} {ω : Circle P} [hne₁ : PtNe A B] [hne₂ : PtNe B C] [hne₃ : PtNe C A] (h₁ : A LiesOn ω) (h₂ : B LiesOn ω) (h₃ : C LiesOn ω) (h : Arc.IsAntipode A B h₁ h₂) : ∠ A C B = ∡[π / 2] := by
  let β : Arc P ω := ARC A B h₁ h₂
  have hh₁ : C LiesOn ω := h₃
  have hh₂ : Arc.IsAntipode β.source β.target β.ison.1 β.ison.2 := h
  have hh₃ : Arc.Isnot_arc_endpts C β := ⟨hne₃.out, hne₂.out.symm⟩
  apply inscribed_angle_of_diameter_eq_mod_pi hh₁ hh₂ hh₃
-/

theorem inscribed_angle_on_same_arc_is_invariant_mod_pi {A B : P} {β : Arc P ω} (h₁ : A LiesOn ω) (h₂ : B LiesOn ω) (hne₁ : Arc.Isnot_arc_endpts ω A β) (hne₂ : Arc.Isnot_arc_endpts ω B β) : (angle_mk_pt_arc ω A β hne₁).dvalue = (angle_mk_pt_arc ω B β hne₂).dvalue := by
  have eq : 2 • (angle_mk_pt_arc ω A β hne₁).value = 2 • (angle_mk_pt_arc ω B β hne₂).value := by rw [← cangle_eq_two_times_inscribed_angle ω h₁ hne₁, ← cangle_eq_two_times_inscribed_angle ω h₂ hne₂]
  exact coe_eq_coe_iff_two_nsmul_eq.mpr eq

end Circle


namespace Arc

protected def iangle (β : Arc P ω) : AngDValue := sorry

theorem inscribed_angle_dvalue_eq_iangle {p : P} {β : Arc P ω} (h₁ : p LiesOn ω) (h₂ : Isnot_arc_endpts ω p β) : (angle_mk_pt_arc ω p β h₂).dvalue = β.iangle := by
  sorry

theorem angle_of_osculation : sorry := sorry

end Arc

end EuclidGeom
