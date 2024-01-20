import EuclideanGeometry.Foundation.Axiom.Triangle.Trigonometric
import EuclideanGeometry.Foundation.Axiom.Linear.Line_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash
import EuclideanGeometry.Foundation.Axiom.Basic.Plane_trash
import EuclideanGeometry.Foundation.Axiom.Position.Orientation_trash

noncomputable section
namespace EuclidGeom

/- Class of Circles-/
@[ext]
structure Circle (P : Type*) [EuclideanPlane P] where
  center : P
  radius : ℝ
  rad_pos : 0 < radius

variable {P : Type*} [EuclideanPlane P]

namespace Circle

def mk_pt_pt (O A : P) [h : PtNe O A] : Circle P where
  center := O
  radius := dist O A
  rad_pos := dist_pos.mpr h.out

def mk_pt_pt_pt (A B C: P) (h : ¬ Collinear A B C) : Circle P := sorry

end Circle

scoped notation "CIR" => Circle.mk_pt_pt

scoped notation "⨀" => Circle.mk_pt_pt

namespace Circle

def mk_pt_radius (O : P) {r : ℝ} (rpos : r > 0) : Circle P where
  center := O
  radius := r
  rad_pos := rpos

def mk_pt_pt_diam (A B : P) [_h :PtNe A B] : Circle P where
  center := (SEG A B).midpoint
  radius := dist (SEG A B).midpoint B
  rad_pos := dist_pos.mpr (SEG_nd A B).midpt_ne_target

end Circle

section coercion

-- this should not live here, this belongs to construction.
-- def TriangleND.toCir (tr_nd : TriangleND P) : Circle P := sorry

end coercion


section position

namespace Circle

/- `One seldom uses Inside a circle in reality.` Should we delete this? Int On Out is enough-/
protected def IsInside (p : P) (ω : Circle P) : Prop := dist ω.center p ≤  ω.radius

protected def IsOn (p : P) (ω : Circle P) : Prop := dist ω.center p = ω.radius

protected def IsInt (p : P) (ω : Circle P) : Prop := dist ω.center p < ω.radius

protected def IsOutside (p : P) (ω : Circle P) : Prop := ω.radius < dist ω.center p

protected def carrier (ω : Circle P) : Set P := { p : P | Circle.IsOn p ω }

protected def interior (ω : Circle P) : Set P := { p : P | Circle.IsInt p ω }
--`Interior is NOT a subset of carrier`

instance : Fig (Circle P) P where
  carrier := Circle.carrier

instance : Interior (Circle P) P where
  interior := Circle.interior

end Circle

/- `One seldom uses Inside a circle in reality.` Should we delete this? Int On Out is enough-/
scoped infix : 50 " LiesIn " => Circle.IsInside

scoped infix : 50 " LiesOut " => Circle.IsOutside

namespace Circle

instance pt_liesout_ne_center {p : P} {ω : Circle P} (h : p LiesOut ω) : PtNe p ω.center := ⟨by
  apply dist_pos.mp
  rw [dist_comm]
  have : dist ω.center p > ω.radius := h
  have : ω.radius > 0 := ω.rad_pos
  linarith
  ⟩

instance pt_lieson_ne_center {p : P} {ω : Circle P} (h : p LiesOn ω) : PtNe p ω.center := ⟨by
  apply dist_pos.mp
  rw [dist_comm, h]
  exact ω.rad_pos
  ⟩

-- this instance does not work due to ω cannot be infered from A B, this should made in tactic ptne in the future
instance pt_liesout_ne_pt_lieson {A B : P} {ω : Circle P} (h₁ : A LiesOut ω) (h₂ : B LiesOn ω) : PtNe A B := ⟨by
  have hgt : dist ω.center A > ω.radius := h₁
  have heq : dist ω.center B = ω.radius := h₂
  contrapose! hgt
  rw [hgt, heq]
  ⟩

instance pt_liesint_ne_pt_lieson {A B : P} {ω : Circle P} (h₁ : A LiesInt ω) (h₂ : B LiesOn ω) : PtNe A B := ⟨by
  have hgt : dist ω.center A < ω.radius := h₁
  have heq : dist ω.center B = ω.radius := h₂
  contrapose! hgt
  rw [hgt, heq]
  ⟩

instance pt_liesout_ne_pt_liesint {A B : P} {ω : Circle P} (h₁ : A LiesOut ω) (h₂ : B LiesInt ω) : PtNe A B := ⟨by
  have hgt : dist ω.center A > ω.radius := h₁
  have hlt : dist ω.center B < ω.radius := h₂
  contrapose! hgt
  rw [hgt]
  linarith
  ⟩

theorem liesint_iff_liesin_and_not_lieson (p : P) (ω : Circle P) : p LiesInt ω ↔ (p LiesIn ω) ∧ (¬ p LiesOn ω) := by
  show dist ω.center p < ω.radius ↔ (dist ω.center p ≤ ω.radius) ∧ (¬ dist ω.center p = ω.radius)
  push_neg
  exact lt_iff_le_and_ne

theorem liesin_iff_liesint_or_lieson (A : P) (ω : Circle P) : A LiesIn ω ↔ (A LiesInt ω) ∨ (A LiesOn ω) := by
  show dist ω.center A ≤ ω.radius ↔ (dist ω.center A < ω.radius) ∨ (dist ω.center A = ω.radius)
  exact le_iff_lt_or_eq

theorem mk_pt_pt_lieson {O A : P} [PtNe O A] : A LiesOn (CIR O A) := rfl

theorem mk_pt_pt_diam_fst_lieson {A B : P} [_h : PtNe A B] : A LiesOn (mk_pt_pt_diam A B) := by
  show dist (SEG A B).midpoint A = dist (SEG A B).midpoint B
  rw [dist_comm, ← Seg.length_eq_dist, ← Seg.length_eq_dist]
  exact (SEG A B).dist_target_eq_dist_source_of_midpt

theorem mk_pt_pt_diam_snd_lieson {A B : P} [_h : PtNe A B] : B LiesOn (mk_pt_pt_diam A B) := rfl

-- Define a concept of segment to be entirely contained in a circle, to mean that the two endpoints of a segment to lie inside a circle.

def seg_lies_inside_circle (l : Seg P) (ω : Circle P) : Prop := l.source LiesIn ω ∧ l.target LiesIn ω

end Circle

scoped infix : 50 " SegInCir " => Circle.seg_lies_inside_circle

namespace Circle

-- very hard question: if a segment lies inside a circle, then the interior point of a

theorem pt_lies_inside_circle_of_seg_inside_circle {l : Seg P} {ω : Circle P} (h : l SegInCir ω) {p : P} (lieson : p LiesInt l) : p LiesInt ω := sorry

end Circle

end position


section Collinear

namespace Circle

lemma pts_lieson_circle_vec_eq {A B : P} {ω : Circle P} [hne : PtNe B A] (hl₁ : A LiesOn ω) (hl₂ : B LiesOn ω) : VEC A (perp_foot ω.center (LIN A B)) = VEC (perp_foot ω.center (LIN A B)) B := by
  have htri₁ : (dist ω.center (perp_foot ω.center (LIN A B))) ^ 2 + (dist A (perp_foot ω.center (LIN A B))) ^ 2 = (dist ω.center A) ^ 2 := by
    rw [← Seg.length_eq_dist, ← Seg.length_eq_dist, ← Seg.length_eq_dist]
    apply Pythagoras_of_perp_foot
    apply Line.fst_pt_lies_on_mk_pt_pt
  have htri₂ : (dist ω.center (perp_foot ω.center (LIN A B))) ^ 2 + (dist B (perp_foot ω.center (LIN A B))) ^ 2 = (dist ω.center B) ^ 2 := by
    rw [← Seg.length_eq_dist, ← Seg.length_eq_dist, ← Seg.length_eq_dist]
    apply Pythagoras_of_perp_foot
    apply Line.snd_pt_lies_on_mk_pt_pt
  haveI : PtNe A (perp_foot ω.center (LIN A B)) := ⟨by
    intro heq
    have : (dist ω.center B) ^ 2 = ω.radius ^ 2 := by rw [hl₂]
    have : (dist ω.center B) ^ 2 > ω.radius ^ 2 := by
      calc
        _ = (dist ω.center (perp_foot ω.center (LIN A B))) ^ 2 + (dist B (perp_foot ω.center (LIN A B))) ^ 2 := by rw [htri₂]
        _ = (dist ω.center A) ^ 2 + (dist B A) ^ 2 := by rw [← heq]
        _ = ω.radius ^ 2 + (dist B A) ^ 2 := by rw [hl₁]
        _ > ω.radius ^ 2 := by
          simp
    linarith⟩
  apply vec_eq_dist_eq_of_lies_on_line_pt_pt_of_ptNe
  · have : (perp_foot ω.center (LIN A B)) LiesOn (LIN A B) := perp_foot_lies_on_line _ _
    have : Collinear A B (perp_foot ω.center (LIN A B)) := Line.pt_pt_linear this
    have : Collinear (perp_foot ω.center (LIN A B)) A B := Collinear.perm₃₁₂ this
    apply Line.pt_pt_maximal this
  apply (sq_eq_sq dist_nonneg dist_nonneg).mp
  calc
    _ = (dist B (perp_foot ω.center (LIN A B))) ^ 2 := by rw [dist_comm]
    _ = (dist ω.center B) ^ 2 - (dist ω.center (perp_foot ω.center (LIN A B))) ^ 2 := by rw [← htri₂]; ring
    _ = (dist ω.center A) ^ 2 - (dist ω.center (perp_foot ω.center (LIN A B))) ^ 2 := by rw [hl₂, hl₁]
    _ = (dist A (perp_foot ω.center (LIN A B))) ^ 2 := by rw [← htri₁]; ring
    _ = (dist (perp_foot ω.center (LIN A B)) A) ^ 2 := by rw [dist_comm]

theorem pts_lieson_circle_perpfoot_eq_midpoint {A B : P} {ω : Circle P} [hne : PtNe B A] (hl₁ : A LiesOn ω) (hl₂ : B LiesOn ω) : perp_foot ω.center (LIN A B) = (SEG A B).midpoint := by
  have eq₁ : VEC A (perp_foot ω.center (LIN A B)) = (1 / 2 : ℝ) • (VEC A B) := by
    symm
    calc
      _ = (1 / 2 : ℝ) • (VEC A (perp_foot ω.center (LIN A B)) + VEC (perp_foot ω.center (LIN A B)) B) := by rw [vec_add_vec]
      _ = (1 / 2 : ℝ) • ((2 : ℝ) • VEC A (perp_foot ω.center (LIN A B))) := by rw [← (pts_lieson_circle_vec_eq hl₁ hl₂), two_smul]
      _ = VEC A (perp_foot ω.center (LIN A B)) := by simp
  have eq₂ : VEC A (SEG A B).midpoint = (1 / 2 : ℝ) • (VEC A B) := Seg.vec_source_midpt
  apply eq_iff_vec_eq_zero.mpr
  calc
    _ = VEC A (perp_foot ω.center (LIN A B)) - VEC A (SEG A B).midpoint := by rw [vec_sub_vec]
    _ = 0 := by rw [eq₁, eq₂]; simp

theorem three_pts_lieson_circle_not_collinear {A B C : P} {ω : Circle P} [hne₁ : PtNe B A] [hne₂ : PtNe C B] [hne₃ : PtNe A C] (hl₁ : A LiesOn ω) (hl₂ : B LiesOn ω) (hl₃ : C LiesOn ω) : ¬ (Collinear A B C) := by
  intro h
  have eq₁ : VEC A (perp_foot ω.center (LIN A B)) = VEC (perp_foot ω.center (LIN A B)) B := pts_lieson_circle_vec_eq hl₁ hl₂
  have eq₂ : VEC A (perp_foot ω.center (LIN A C)) = VEC (perp_foot ω.center (LIN A C)) C := pts_lieson_circle_vec_eq hl₁ hl₃
  have ha : A LiesOn LIN A B := Line.fst_pt_lies_on_mk_pt_pt
  have hc : C LiesOn LIN A B := Line.pt_pt_maximal h
  have : LIN A C = LIN A B := Line.eq_line_of_pt_pt_of_ne ha hc
  rw [this] at eq₂
  have : VEC B C = 0 := by
    calc
      _ = VEC (perp_foot ω.center (LIN A B)) C - VEC (perp_foot ω.center (LIN A B)) B := by rw [vec_sub_vec]
      _ = 0 := by rw [← eq₁, ← eq₂, sub_self]
  have : VEC B C ≠ 0 := ne_iff_vec_ne_zero.mp hne₂.out
  tauto

end Circle

end Collinear


section antipode

namespace Circle

def IsAntipode {A B : P} (ω : Circle P) (_ha : A LiesOn ω) (_hb : B LiesOn ω) : Prop := B = pt_flip A ω.center

theorem antipode_symm {A B : P} {ω : Circle P} (ha : A LiesOn ω) (hb : B LiesOn ω) : IsAntipode ω ha hb ↔ IsAntipode ω hb ha := by
  unfold IsAntipode
  constructor
  · apply pt_flip_symm
  apply pt_flip_symm

theorem antipode_center_is_midpoint {A B : P} {ω : Circle P} (ha : A LiesOn ω) (hb : B LiesOn ω) (h : IsAntipode ω ha hb) : ω.center = (SEG A B).midpoint := pt_flip_center_is_midpoint h

theorem antipode_iff_collinear (A B : P) {ω : Circle P} [h : PtNe B A] (ha : A LiesOn ω) (hb : B LiesOn ω) : IsAntipode ω ha hb ↔ Collinear A ω.center B := by
  constructor
  · intro hh
    apply pt_flip_collinear hh
  intro hcl
  haveI : PtNe A ω.center := pt_lieson_ne_center ha
  have hl : B LiesOn LIN ω.center A := Line.pt_pt_maximal (Collinear.perm₂₁₃ hcl)
  have heq : VEC A ω.center = VEC ω.center B := by
    apply vec_eq_dist_eq_of_lies_on_line_pt_pt_of_ptNe hl
    rw [ha, hb]
  unfold IsAntipode pt_flip
  rw [heq, eq_vadd_iff_vsub_eq]
  rfl

theorem mk_pt_pt_diam_isantipode {A B : P} [h : PtNe A B] : IsAntipode (mk_pt_pt_diam A B) mk_pt_pt_diam_fst_lieson mk_pt_pt_diam_snd_lieson := by
  have hc : Collinear A (SEG A B).midpoint B := by
    apply Collinear.perm₁₃₂
    apply Line.pt_pt_linear
    show (SEG A B).midpoint LiesOn (SEG_nd A B).toLine
    apply SegND.lies_on_toLine_of_lie_on
    apply Seg.midpt_lies_on
  exact (antipode_iff_collinear _ _ mk_pt_pt_diam_fst_lieson mk_pt_pt_diam_snd_lieson).mpr hc

end Circle

end antipode


section arc

variable (ω : Circle P)

@[ext]
structure Arc (P : Type*) [EuclideanPlane P] (ω : Circle P) where
  source : P
  target : P
  ison : (source LiesOn ω) ∧ (target LiesOn ω)
  endpts_ne : PtNe target source

namespace Arc

attribute [instance] Arc.endpts_ne

protected def mk_pt_pt_circle {ω : Circle P} {A B : P} [h : PtNe B A] (ha : A LiesOn ω) (hb : B LiesOn ω) : Arc P ω where
  source := A
  target := B
  ison := ⟨ha, hb⟩
  endpts_ne := h

end Arc

scoped notation "ARC" => Arc.mk_pt_pt_circle

namespace Arc

protected def IsOn {ω : Circle P} (p : P) (β : Arc P ω) : Prop := (p LiesOn ω) ∧ (¬ p LiesOnLeft (DLIN β.source β.target))

protected def ne_endpts {ω : Circle P} (p : P) (β : Arc P ω) : Prop := (p ≠ β.source) ∧ (p ≠ β.target)

instance pt_ne_source {ω : Circle P} {p : P} {β : Arc P ω} (h : β.ne_endpts p) : PtNe β.source p := ⟨h.1.symm⟩

instance pt_ne_target {ω : Circle P} {p : P} {β : Arc P ω} (h : β.ne_endpts p) : PtNe β.target p := ⟨h.2.symm⟩

protected def IsInt {ω : Circle P} (p : P) (β : Arc P ω) : Prop := (Arc.IsOn p β) ∧ (β.ne_endpts p)

protected def carrier {ω : Circle P} (β : Arc P ω) : Set P := { p : P | Arc.IsOn p β }

protected def interior {ω : Circle P} (β : Arc P ω) : Set P := { p : P | Arc.IsInt p β }

instance : Fig (Arc P ω) P where
  carrier := Arc.carrier

instance : Interior (Arc P ω) P where
  interior := Arc.interior

theorem center_ne_endpts {ω : Circle P} (β : Arc P ω) : β.ne_endpts ω.center := by
  constructor
  · intro h
    have : β.source LiesOn ω := β.ison.1
    rw [← h] at this
    unfold lies_on Fig.carrier Circle.instFigCircle Circle.carrier Circle.IsOn at this
    simp at this
    have : ω.radius > 0 := ω.rad_pos
    linarith
  intro h
  have : β.target LiesOn ω := β.ison.2
  rw [← h] at this
  unfold lies_on Fig.carrier Circle.instFigCircle Circle.carrier Circle.IsOn at this
  simp at this
  have : ω.radius > 0 := ω.rad_pos
  linarith

instance source_ne_center {ω : Circle P} (β : Arc P ω) : PtNe β.source ω.center := ⟨ (center_ne_endpts β).1.symm ⟩

instance target_ne_center {ω : Circle P} (β : Arc P ω) : PtNe β.target ω.center := ⟨ (center_ne_endpts β).2.symm ⟩

protected def complement {ω : Circle P} (β : Arc P ω) : Arc P ω where
  source := β.target
  target := β.source
  ison := and_comm.mp β.ison
  endpts_ne := β.endpts_ne.symm

lemma pt_liesint_not_lieson_dlin {ω : Circle P} {β : Arc P ω} {p : P} (h : p LiesInt β) : ¬ (p LiesOn (DLIN β.source β.target)) := by
  intro hl
  have hl : p LiesOn (LIN β.source β.target) := hl
  have hco : Collinear β.source β.target p := Line.pt_pt_linear hl
  have hco' : ¬ (Collinear β.source β.target p) := Circle.three_pts_lieson_circle_not_collinear (hne₂ := ⟨h.2.2⟩) (hne₃ := ⟨h.2.1.symm⟩) β.ison.1 β.ison.2 h.1.1
  tauto

theorem pt_liesint_liesonright_dlin {ω : Circle P} {β : Arc P ω} {p : P} (h : p LiesInt β) : p LiesOnRight (DLIN β.source β.target) := by
  have hnl : ¬ (p LiesOn (DLIN β.source β.target)) := pt_liesint_not_lieson_dlin h
  have hnll : ¬ (p LiesOnLeft (DLIN β.source β.target)) := h.1.2
  rcases DirLine.lieson_or_liesonleft_or_liesonright p (DLIN β.source β.target) with hh | (hh | hh)
  · exfalso; tauto
  · exfalso; tauto
  exact hh

theorem pt_liesint_complementary_liesonleft_dlin {ω : Circle P} {β : Arc P ω} {p : P} (h : p LiesInt β.complement) : p LiesOnLeft (DLIN β.source β.target) := by
  have hh : p LiesOnRight (DLIN β.target β.source) := by apply pt_liesint_liesonright_dlin h
  apply liesonleft_iff_liesonright_reverse.mpr
  rw [← DirLine.pt_pt_rev_eq_rev]
  exact hh

end Arc

end arc


section chord

@[ext]
structure Chord (P : Type*) [EuclideanPlane P] (ω : Circle P) where
  toSegND : SegND P
  ison : (toSegND.source LiesOn ω) ∧ (toSegND.target LiesOn ω)

instance Chord.IsND {ω : Circle P} (s : Chord P ω) : PtNe s.1.source s.1.target := ⟨s.1.2.symm⟩

attribute [instance] Chord.IsND

variable (ω : Circle P)

namespace Chord

protected def mk_pt_pt_circle {ω : Circle P} {A B : P} [h : PtNe A B] (ha : A LiesOn ω) (hb : B LiesOn ω) : Chord P ω where
  toSegND := SEG_nd A B h.out.symm
  ison := ⟨ha, hb⟩

protected def IsOn {ω : Circle P} (A : P) (s : Chord P ω) : Prop := A LiesOn s.toSegND

protected def IsInt {ω : Circle P} (A : P) (s : Chord P ω) : Prop := A LiesInt s.toSegND

protected def carrier {ω : Circle P} (s : Chord P ω) : Set P := { p : P | Chord.IsOn p s }

protected def interior {ω : Circle P} (s : Chord P ω) : Set P := { p : P | Chord.IsInt p s }

instance : Fig (Chord P ω) P where
  carrier := Chord.carrier

instance : Interior (Chord P ω) P where
  interior := Chord.interior

protected def ne_endpts {ω : Circle P} (A : P) (s : Chord P ω) : Prop := (A ≠ s.1.source) ∧ (A ≠ s.1.target)

theorem center_ne_endpts {ω : Circle P} (s : Chord P ω) : s.ne_endpts ω.center := by
  constructor
  · intro h
    have : s.1.source LiesOn ω := s.2.1
    rw [← h] at this
    unfold lies_on Fig.carrier Circle.instFigCircle Circle.carrier Circle.IsOn at this
    simp at this
    have : ω.radius > 0 := ω.rad_pos
    linarith
  intro h
  have : s.1.target LiesOn ω := s.2.2
  rw [← h] at this
  unfold lies_on Fig.carrier Circle.instFigCircle Circle.carrier Circle.IsOn at this
  simp at this
  have : ω.radius > 0 := ω.rad_pos
  linarith

instance source_ne_center {ω : Circle P} (s : Chord P ω) : PtNe s.1.source ω.center := ⟨ (center_ne_endpts s).1.symm ⟩

instance target_ne_center {ω : Circle P} (s : Chord P ω) : PtNe s.1.target ω.center := ⟨ (center_ne_endpts s).2.symm ⟩

protected def reverse {ω : Circle P} (s : Chord P ω) : Chord P ω where
  toSegND := s.1.reverse
  ison := ⟨s.2.2, s.2.1⟩

theorem pt_liesint_liesint_circle {ω : Circle P} {A : P} {s : Chord P ω} (h : A LiesInt s) : A LiesInt ω := by
  have : s.1 SegInCir ω := by
    unfold Circle.seg_lies_inside_circle
    constructor
    · apply (Circle.liesin_iff_liesint_or_lieson _ _).mpr
      right; exact s.2.1
    apply (Circle.liesin_iff_liesint_or_lieson _ _).mpr
    right; exact s.2.2
  apply Circle.pt_lies_inside_circle_of_seg_inside_circle this h

end Chord

def Arc.toChord {ω : Circle P} (β : Arc P ω) : Chord P ω where
  toSegND := SEG_nd β.source β.target β.endpts_ne.out
  ison := β.ison

def Chord.toArc {ω : Circle P} (s : Chord P ω) : Arc P ω where
  source := s.1.source
  target := s.1.target
  ison := s.2
  endpts_ne := ⟨s.1.2⟩

theorem Circle.complementary_arc_toChord_eq_reverse {ω : Circle P} (β : Arc P ω) : β.complement.toChord = β.toChord.reverse := rfl

theorem Circle.reverse_chord_toArc_eq_complement {ω : Circle P} (s : Chord P ω) : s.reverse.toArc = s.toArc.complement := rfl

namespace Chord

protected def length {ω : Circle P} (s : Chord P ω) : ℝ := s.1.length

protected def IsDiameter {ω : Circle P} (s : Chord P ω) : Prop := ω.center LiesOn s

theorem diameter_iff_antipide {ω : Circle P} {s : Chord P ω} : Chord.IsDiameter s ↔ Circle.IsAntipode ω s.2.1 s.2.2 := by
  haveI : PtNe s.1.source s.1.target := ⟨s.1.2.symm⟩
  constructor
  · unfold Chord.IsDiameter
    intro hl
    have : Collinear s.1.source s.1.target ω.center := by
      apply Line.pt_pt_linear
      apply SegND.lies_on_toLine_of_lie_on hl
    apply (Circle.antipode_iff_collinear s.1.source s.1.target s.2.1 s.2.2).mpr (Collinear.perm₁₃₂ this)
  unfold Circle.IsAntipode
  intro hf
  have : VEC s.1.source ω.center = VEC ω.center s.1.target := pt_flip_vec_eq hf
  unfold Chord.IsDiameter
  show ω.center LiesOn s.1
  apply SegND.lies_on_iff.mpr
  use (1 / 2 : ℝ)
  constructor
  · norm_num
  constructor
  · norm_num
  apply pt_flip_vec_eq_half_vec hf

theorem diameter_length_eq_twice_radius {ω : Circle P} {s : Chord P ω} (h : Chord.IsDiameter s) : s.length = 2 * ω.radius := by
  have : VEC s.1.source ω.center = VEC ω.center s.1.target := by
    apply pt_flip_vec_eq
    show Circle.IsAntipode ω s.2.1 s.2.2
    apply diameter_iff_antipide.mp h
  have : VEC s.1.source s.1.target = (2 : ℝ) • (VEC s.1.source ω.center) := by
    calc
      _ = VEC s.1.source ω.center + VEC ω.center s.1.target := by rw [vec_add_vec]
      _ = (2 : ℝ) • (VEC s.1.source ω.center) := by rw [← this, two_smul]
  calc
    _ = s.1.length := rfl
    _ = ‖VEC s.1.source s.1.target‖ := by
      show dist s.1.source s.1.target = ‖VEC s.1.source s.1.target‖
      rw [dist_comm, NormedAddTorsor.dist_eq_norm']
      rfl
    _ = 2 * (dist ω.center s.1.source) := by
      rw [this, NormedAddTorsor.dist_eq_norm', norm_smul]
      norm_num
      rfl
    _ = 2 * ω.radius := by rw [s.2.1]

end Chord

end chord

end EuclidGeom
