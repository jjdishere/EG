import EuclideanGeometry.Foundation.Axiom.Position.Orientation
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Trigonometric
import EuclideanGeometry.Foundation.Axiom.Linear.Line_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular

noncomputable section
namespace EuclidGeom

/- Class of Circles-/
@[ext]
structure Circle (P : Type _) [EuclideanPlane P] where
  center : P
  radius : ℝ
  rad_pos : 0 < radius

variable {P : Type _} [EuclideanPlane P]

namespace Circle

def mk_pt_pt (O A : P) [h : PtNe O A] : Circle P where
  center := O
  radius := dist O A
  rad_pos := dist_pos.mpr h.out

def mk_pt_pt_pt (A B C: P) (h : ¬ collinear A B C) : Circle P := sorry

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

theorem interior_of_circle_iff_inside_not_on_circle (p : P) (ω : Circle P) : p LiesInt ω ↔ (p LiesIn ω) ∧ (¬ p LiesOn ω) := by
  show dist ω.center p < ω.radius ↔ (dist ω.center p ≤ ω.radius) ∧ (¬ dist ω.center p = ω.radius)
  push_neg
  exact lt_iff_le_and_ne

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


section collinear

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
    have : collinear A B (perp_foot ω.center (LIN A B)) := Line.pt_pt_linear this
    have : collinear (perp_foot ω.center (LIN A B)) A B := perm_collinear_trd_fst_snd this
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
  apply (eq_iff_vec_eq_zero _ _).mpr
  calc
    _ = VEC A (perp_foot ω.center (LIN A B)) - VEC A (SEG A B).midpoint := by rw [vec_sub_vec]
    _ = 0 := by rw [eq₁, eq₂]; simp

theorem three_pts_lieson_circle_not_collinear {A B C : P} {ω : Circle P} [hne₁ : PtNe B A] [hne₂ : PtNe C B] [hne₃ : PtNe A C] (hl₁ : A LiesOn ω) (hl₂ : B LiesOn ω) (hl₃ : C LiesOn ω) : ¬ (collinear A B C) := by
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
  have : VEC B C ≠ 0 := (ne_iff_vec_ne_zero _ _).mp hne₂.out
  tauto

end Circle

end collinear

section antipode

namespace Circle

def antipode (A : P) (ω : Circle P) : P := VEC A ω.center +ᵥ ω.center

theorem antipode_lieson_circle {A : P} {ω : Circle P} {ha : A LiesOn ω} : (antipode A ω) LiesOn ω := by
  show dist ω.center (antipode A ω) = ω.radius
  rw [NormedAddTorsor.dist_eq_norm', antipode,  vsub_vadd_eq_vsub_sub]
  simp only [vsub_self, zero_sub, norm_neg]
  show ‖ω.center -ᵥ A‖ = ω.radius
  rw [← NormedAddTorsor.dist_eq_norm', ha]

theorem antipode_symm {A B : P} {ω : Circle P} {ha : A LiesOn ω} (h : antipode A ω = B) : antipode B ω = A := by
  show VEC B ω.center +ᵥ ω.center = A
  symm
  apply (eq_vadd_iff_vsub_eq _ _ _).mpr
  show VEC ω.center A = VEC B ω.center
  have : VEC ω.center B = VEC A ω.center := by
    show B -ᵥ ω.center = VEC A ω.center
    apply (eq_vadd_iff_vsub_eq _ _ _).mp h.symm
  rw [← neg_vec, ← this, neg_vec]

theorem antipode_distinct {A : P} {ω : Circle P} {ha : A LiesOn ω} : antipode A ω ≠ A := by
  intro eq
  have : VEC ω.center A = VEC A ω.center := by
    show A -ᵥ ω.center = VEC A ω.center
    apply (eq_vadd_iff_vsub_eq _ _ _).mp eq.symm
  have neq : A ≠ ω.center := (pt_lieson_ne_center ha).out
  contrapose! neq
  apply (eq_iff_vec_eq_zero _ _).mpr
  have : 2 • (VEC ω.center A) = 0 := by
    rw [two_smul]
    nth_rw 1 [this]
    rw [vec_add_vec]
    simp
  apply (two_nsmul_eq_zero ℝ _).mp this

end Circle

end antipode

end EuclidGeom
