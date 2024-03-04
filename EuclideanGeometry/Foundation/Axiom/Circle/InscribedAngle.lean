import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Triangle.IsocelesTriangle_trash

noncomputable section
namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

open AngValue Angle

section cangle

attribute [instance] Arc.endpts_ne Chord.IsND Arc.source_ne_center Arc.target_ne_center Chord.source_ne_center Chord.target_ne_center

def Arc.cangle {ω : Circle P} (β : Arc P ω) : Angle P := ANG β.source ω.center β.target

def Arc.IsMajor {ω : Circle P} (β : Arc P ω) : Prop := β.cangle.value.toReal < 0

def Arc.IsMinor {ω : Circle P} (β : Arc P ω) : Prop := β.cangle.value.toReal > 0

def Chord.cangle {ω : Circle P} (s : Chord P ω) : Angle P := ANG s.1.source ω.center s.1.target

theorem Circle.cangle_of_arc_eq_cangle_of_toChord {ω : Circle P} (β : Arc P ω) : β.cangle = β.toChord.cangle := rfl

theorem Circle.cangle_of_chord_eq_cangle_of_toArc {ω : Circle P} (s : Chord P ω) : s.cangle = s.toArc.cangle := rfl

theorem Chord.cangle_eq_pi_iff_is_diameter {ω : Circle P} (s : Chord P ω) : s.cangle.value = π ↔ Chord.IsDiameter s := by
  constructor
  · intro heq
    have : Collinear ω.center s.1.source s.1.target := collinear_of_angle_eq_pi heq
    apply diameter_iff_antipide.mpr
    apply (Circle.antipode_iff_collinear s.1.source s.1.target  _ _).mpr (Collinear.perm₂₁₃ this)
  intro hd
  have : ω.center LiesInt s.1 := by
    constructor
    · exact hd
    exact (center_ne_endpts s).1
    exact (center_ne_endpts s).2
  apply value_eq_pi_of_lies_int_seg_nd this

theorem Arc.complement_cangle_reverse {ω : Circle P} (β : Arc P ω) : β.complement.cangle = β.cangle.reverse := rfl

theorem Chord.reverse_cangle_reverse {ω : Circle P} (s : Chord P ω) : s.reverse.cangle = s.cangle.reverse := rfl

theorem Circle.cangle_of_complementary_arc_eq_neg {ω : Circle P} (β : Arc P ω) : β.complement.cangle.value = -β.cangle.value := by
  rw [Arc.complement_cangle_reverse, rev_value_eq_neg_value]

theorem Circle.cangle_of_reverse_chord_eq_neg {ω : Circle P} (s : Chord P ω) : s.reverse.cangle.value = -s.cangle.value := by
  rw [Chord.reverse_cangle_reverse, rev_value_eq_neg_value]

theorem Chord.cangle_eq_iff_length_eq {ω : Circle P} (s₁ s₂ : Chord P ω) : s₁.cangle.value = s₂.cangle.value ↔ s₁.length = s₂.length := sorry

end cangle


section iangle

attribute [instance] Arc.pt_ne_source Arc.pt_ne_target  -- why can't work

def Arc.IsIangle {ω : Circle P} (β : Arc P ω) (ang : Angle P) : Prop := (ang.source LiesOn ω) ∧ (β.ne_endpts ang.source) ∧ (β.source LiesOn ang.start_ray) ∧ (β.target LiesOn ang.end_ray)

def Chord.IsIangle {ω : Circle P} (s : Chord P ω) (ang : Angle P) : Prop := (ang.source LiesOn ω) ∧ (s.ne_endpts ang.source) ∧ (s.1.source LiesOn ang.start_ray) ∧ (s.1.target LiesOn ang.end_ray)

theorem Arc.iangle_eq {ω : Circle P} {β : Arc P ω} {ang : Angle P} (h : β.IsIangle ang) : ANG β.source ang.source β.target h.2.1.1.symm h.2.1.2.symm = ang := eq_of_lies_int_ray ⟨h.2.2.1, h.2.1.1.symm⟩ ⟨h.2.2.2, h.2.1.2.symm⟩

theorem Chord.iangle_eq {ω : Circle P} {s : Chord P ω} {ang : Angle P} (h : s.IsIangle ang) : ANG s.1.source ang.source s.1.target h.2.1.1.symm h.2.1.2.symm = ang := eq_of_lies_int_ray ⟨h.2.2.1, h.2.1.1.symm⟩ ⟨h.2.2.2, h.2.1.2.symm⟩

theorem Arc.angle_mk_pt_is_iangle {ω : Circle P} {C : P} {β : Arc P ω} (h₁ : C LiesOn ω) (h₂ : β.ne_endpts C) : β.IsIangle (ANG β.source C β.target h₂.1.symm h₂.2.symm) := by
  haveI : PtNe C β.source := ⟨h₂.1⟩
  haveI : PtNe C β.target := ⟨h₂.2⟩
  constructor
  · exact h₁
  constructor
  · exact h₂
  constructor
  · show β.source LiesOn (RAY C β.source)
    apply Ray.snd_pt_lies_on_mk_pt_pt
  show β.target LiesOn (RAY C β.target)
  apply Ray.snd_pt_lies_on_mk_pt_pt

theorem Chord.angle_mk_pt_is_iangle {ω : Circle P} {C : P} {s : Chord P ω} (h₁ : C LiesOn ω) (h₂ : s.ne_endpts C) : s.IsIangle (ANG s.1.source C s.1.target h₂.1.symm h₂.2.symm) := by
  haveI : PtNe C s.1.source := ⟨h₂.1⟩
  haveI : PtNe C s.1.target := ⟨h₂.2⟩
  constructor
  · exact h₁
  constructor
  · exact h₂
  constructor
  · show s.1.source LiesOn (RAY C s.1.source)
    apply Ray.snd_pt_lies_on_mk_pt_pt
  show s.1.target LiesOn (RAY C s.1.target)
  apply Ray.snd_pt_lies_on_mk_pt_pt

theorem Circle.iangle_of_arc_is_iangle_of_toChord {ω : Circle P} {β : Arc P ω} {ang : Angle P} (h : β.IsIangle ang) : β.toChord.IsIangle ang := h

theorem Circle.iangle_of_chord_is_iangle_of_toArc {ω : Circle P} {s : Chord P ω} {ang : Angle P} (h : s.IsIangle ang) : s.toArc.IsIangle ang := h

theorem Arc.cangle_eq_two_times_inscribed_angle {ω : Circle P} {β : Arc P ω} {ang : Angle P} (h : β.IsIangle ang) : β.cangle.value = 2 • ang.value := by
  let p : P := ang.source
  haveI : PtNe p β.source := ⟨h.2.1.1⟩
  haveI : PtNe p β.target := ⟨h.2.1.2⟩
  haveI : PtNe p ω.center := Circle.pt_lieson_ne_center h.1
  have hit₁ : (▵ ω.center β.target p).IsIsoceles := by
    show (SEG p ω.center).length = (SEG ω.center β.target).length
    rw [Seg.length_eq_dist, Seg.length_eq_dist, dist_comm, h.1, β.ison.2]
  have hit₂ : (▵ ω.center p β.source).IsIsoceles := by
    show (SEG β.source ω.center).length = (SEG ω.center p).length
    rw [Seg.length_eq_dist, Seg.length_eq_dist, dist_comm, h.1, β.ison.1]
  have eq₁ : ∠ p β.target ω.center = ∠ ω.center p β.target :=
    is_isoceles_tri_ang_eq_ang_of_tri hit₁ _
  have eq₂ : ∠ β.source p ω.center = ∠ ω.center β.source p :=
    is_isoceles_tri_ang_eq_ang_of_tri hit₂ _
  have π₁ : ∠ β.target ω.center p + ∠ p β.target ω.center + ∠ ω.center p β.target = π :=
    angle_sum_eq_pi_of_tri (▵ ω.center β.target p) _ _ _
  have π₂ : ∠ p ω.center β.source + ∠ β.source p ω.center + ∠ ω.center β.source p = π :=
    angle_sum_eq_pi_of_tri (▵ ω.center p β.source) _ _ _
  have eq₃ : ∠ β.target ω.center β.source + 2 • (∠ β.source p β.target) = 0 := by
    calc
      _ = ∠ β.target ω.center p + ∠ p ω.center β.source + 2 • (∠ β.source p ω.center + ∠ ω.center p β.target) := by
        rw [value_add_eq_add_value ω.center β.target β.source p]
        rw [value_add_eq_add_value p β.source β.target ω.center]
      _ = ∠ β.target ω.center p + ∠ p ω.center β.source + (∠ p β.target ω.center + ∠ ω.center p β.target) + (∠ β.source p ω.center + ∠ ω.center β.source p) := by
        rw [← eq₂, eq₁, two_smul]
        abel
      _ = (∠ β.target ω.center p + ∠ p β.target ω.center + ∠ ω.center p β.target) + (∠ p ω.center β.source + ∠ β.source p ω.center + ∠ ω.center β.source p) := by
        rw [add_assoc, add_add_add_comm]
        abel
      _ = 0 := by
        rw [π₁, π₂, ← coe_two_pi, two_mul, coe_pi_add_coe_pi, coe_add, coe_pi_add_coe_pi]
  calc
    _ = - ∠ β.target ω.center β.source := by rw [← neg_value_of_rev_ang]; rfl
    _ = 2 • (∠ β.source p β.target) := by rw [← zero_sub, ← eq₃, add_sub_cancel']
    _ = 2 • ang.value := by rw [← Arc.iangle_eq h]

theorem Chord.cangle_eq_two_times_inscribed_angle {ω : Circle P} {s : Chord P ω} {ang : Angle P} (h : s.IsIangle ang) : s.cangle.value = 2 • ang.value := by
  have : s.toArc.IsIangle ang := h
  rw [← Arc.cangle_eq_two_times_inscribed_angle this]
  rfl

theorem Circle.iangle_of_diameter_eq_mod_pi {ω : Circle P} {s : Chord P ω} {ang : Angle P} (h : s.IsIangle ang) (hd : s.IsDiameter) : ang.dvalue = ∡[π / 2] := by
  have : s.cangle.value = π := (Chord.cangle_eq_pi_iff_is_diameter s).mpr hd
  have : 2 • ang.value = π := by rw [← this, Chord.cangle_eq_two_times_inscribed_angle h]
  rcases two_nsmul_eq_pi_iff.mp this with h | h
  · rw [← h]
  unfold dvalue
  rw [h, neg_div]
  simp only [coe_neg, AngDValue.coe_neg, AngDValue.neg_coe_pi_div_two]

theorem Arc.iangle_invariant_mod_pi {ω : Circle P} {β : Arc P ω} {ang₁ ang₂ : Angle P} (h₁ : β.IsIangle ang₁) (h₂ : β.IsIangle ang₂) : ang₁.dvalue = ang₂.dvalue := by
  have : 2 • ang₁.value = 2 • ang₂.value := by
    rw [← cangle_eq_two_times_inscribed_angle h₁, ← cangle_eq_two_times_inscribed_angle h₂]
  apply coe_eq_coe_iff_two_nsmul_eq.mpr this

theorem Chord.iangle_invariant_mod_pi {ω : Circle P} {s : Chord P ω} {ang₁ ang₂ : Angle P} (h₁ : s.IsIangle ang₁) (h₂ : s.IsIangle ang₂) : ang₁.dvalue = ang₂.dvalue := by
  have : 2 • ang₁.value = 2 • ang₂.value := by
    rw [← cangle_eq_two_times_inscribed_angle h₁, ← cangle_eq_two_times_inscribed_angle h₂]
  apply coe_eq_coe_iff_two_nsmul_eq.mpr this

theorem Circle.dvalue_eq_of_lies_on {ω : Circle P} {A B C D : P} [_hca : PtNe C A] [_hda : PtNe D A] [_hcb : PtNe C B] [_hdb : PtNe D B] (ha : A LiesOn ω) (hb : B LiesOn ω) (hc : C LiesOn ω) (hd : D LiesOn ω) : ∡ A C B = ∡ A D B := by
  by_cases h : B = A
  · simp only [h, pt_pt_pt_dvalue_eq_zero_of_same_pt]
  · haveI : PtNe B A := ⟨h⟩
    haveI : PtNe (ARC ha hb).source (ANG A C B).source := _hca.symm
    haveI : PtNe (ARC ha hb).target (ANG A C B).source := _hcb.symm
    haveI : PtNe (ARC ha hb).source (ANG A D B).source := _hda.symm
    haveI : PtNe (ARC ha hb).target (ANG A D B).source := _hdb.symm
    apply (ARC ha hb).iangle_invariant_mod_pi
    · exact ⟨hc, ⟨_hca.1, _hcb.1⟩, Ray.snd_pt_lies_on_mk_pt_pt, Ray.snd_pt_lies_on_mk_pt_pt⟩
    · exact ⟨hd, ⟨_hda.1, _hdb.1⟩, Ray.snd_pt_lies_on_mk_pt_pt, Ray.snd_pt_lies_on_mk_pt_pt⟩

end iangle


section iangdvalue

def Arc.iangdv {ω : Circle P} (β : Arc P ω) : AngDValue := β.cangle.value.half

def Chord.iangdv {ω : Circle P} (s : Chord P ω) : AngDValue := s.cangle.value.half

theorem Arc.iangle_dvalue_eq {ω : Circle P} {β : Arc P ω} {ang : Angle P} (h : β.IsIangle ang) : ang.dvalue = β.iangdv := by
  unfold iangdv
  rw [cangle_eq_two_times_inscribed_angle h]
  apply AngValue.coe_eq_coe_iff_two_nsmul_eq.mpr
  simp

theorem Chord.iangle_dvalue_eq {ω : Circle P} {s : Chord P ω} {ang : Angle P} (h : s.IsIangle ang) : ang.dvalue = s.iangdv := by
  unfold iangdv
  rw [cangle_eq_two_times_inscribed_angle h]
  apply AngValue.coe_eq_coe_iff_two_nsmul_eq.mpr
  simp

theorem Circle.same_chord_same_iangle_dvalue {ω : Circle P} {s₁ s₂ : Chord P ω} {ang₁ ang₂ : Angle P} (h₁ : s₁.IsIangle ang₁) (h₂ : s₂.IsIangle ang₂) (h : s₁.length = s₂.length) : ang₁.dvalue = ang₂.dvalue := by
  have : s₁.cangle.value = s₂.cangle.value := (Chord.cangle_eq_iff_length_eq s₁ s₂).mpr h
  rw [Chord.iangle_dvalue_eq h₁, Chord.iangle_dvalue_eq h₂]
  unfold Chord.iangdv
  rw [this]

end iangdvalue


/-
theorem inscribed_angle_is_positive {p : P} {β : Arc P ω} (h : p LiesInt β.complement) : (angle_mk_pt_arc ω p β h.2.symm).value.IsPos := by
  unfold angle_mk_pt_arc
  apply TriangleND.liesonleft_angle_ispos
  exact (Arc.pt_liesint_complementary_liesonleft_dlin ω h)

theorem inscribed_angle_of_complementary_arc_is_negative {p : P} {β : Arc P ω} (h : p LiesInt β) : (angle_mk_pt_arc ω p β h.2).value.IsNeg := by
  unfold angle_mk_pt_arc
  apply TriangleND.liesonright_angle_isneg
  exact (Arc.pt_liesint_liesonright_dlin ω h)
-/

end EuclidGeom
