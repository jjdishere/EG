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

def mk_pt_pt_pt (A B C: P) (h : ¬ colinear A B C) : Circle P := sorry

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

def IsOutside (p : P) (ω : Circle P) : Prop := ω.radius < dist ω.center p

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
  rw [dist_comm]
  have : dist ω.center p = ω.radius := h
  have : ω.radius > 0 := ω.rad_pos
  linarith
  ⟩

-- this instance does not work due to ω cannot be infered from A B, this should made in tactic ptne in the future
instance pt_liesout_ne_pt_lieson {A B : P} {ω : Circle P} (h₁ : A LiesOut ω) (h₂ : B LiesOn ω) : PtNe A B := ⟨by
  have hgt : dist ω.center A > ω.radius := h₁
  have heq : dist ω.center B = ω.radius := h₂
  contrapose! hgt
  rw [hgt, heq]
  ⟩

theorem interior_of_circle_iff_inside_not_on_circle (p : P) (ω : Circle P) : p LiesInt ω ↔ (p LiesIn ω) ∧ (¬ p LiesOn ω) := by
  show dist ω.center p < ω.radius ↔ (dist ω.center p ≤ ω.radius) ∧ (¬ dist ω.center p = ω.radius)
  push_neg
  exact lt_iff_le_and_ne

@[simp]
theorem mk_pt_pt_lieson {O A : P} [PtNe O A] : A LiesOn (CIR O A) := rfl

@[simp]
theorem mk_pt_pt_diam_fst_lieson {A B : P} [_h : PtNe A B] : A LiesOn (mk_pt_pt_diam A B) := by
  show dist (SEG A B).midpoint A = dist (SEG A B).midpoint B
  rw [dist_comm, ← Seg.length_eq_dist, ← Seg.length_eq_dist]
  exact dist_target_eq_dist_source_of_midpt (seg := (SEG A B))

@[simp]
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


section colinear

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
  have : PtNe A (perp_foot ω.center (LIN A B))
  · apply Fact.mk
    intro heq
    have : (dist ω.center B) ^ 2 = ω.radius ^ 2 := by rw [hl₂]
    have : (dist ω.center B) ^ 2 > ω.radius ^ 2 := by
      calc
        _ = (dist ω.center (perp_foot ω.center (LIN A B))) ^ 2 + (dist B (perp_foot ω.center (LIN A B))) ^ 2 := by rw [htri₂]
        _ = (dist ω.center A) ^ 2 + (dist B A) ^ 2 := by rw [← heq]
        _ = ω.radius ^ 2 + (dist B A) ^ 2 := by rw [hl₁]
        _ > ω.radius ^ 2 := by
          simp
    linarith
  apply distinct_pts_same_dist_vec_eq
  · have : (perp_foot ω.center (LIN A B)) LiesOn (LIN A B) := perp_foot_lies_on_line _ _
    have : colinear A B (perp_foot ω.center (LIN A B)) := Line.pt_pt_linear this
    have : colinear (perp_foot ω.center (LIN A B)) A B := perm_colinear_trd_fst_snd this
    apply Line.pt_pt_maximal this
  apply (sq_eq_sq dist_nonneg dist_nonneg).mp
  calc
    _ = (dist B (perp_foot ω.center (LIN A B))) ^ 2 := by rw [dist_comm]
    _ = (dist ω.center B) ^ 2 - (dist ω.center (perp_foot ω.center (LIN A B))) ^ 2 := by rw [← htri₂]; ring
    _ = (dist ω.center A) ^ 2 - (dist ω.center (perp_foot ω.center (LIN A B))) ^ 2 := by rw [hl₂, hl₁]
    _ = (dist A (perp_foot ω.center (LIN A B))) ^ 2 := by rw [← htri₁]; ring
    _ = (dist (perp_foot ω.center (LIN A B)) A) ^ 2 := by rw [dist_comm]


theorem three_pts_lieson_circle_not_colinear {A B C : P} {ω : Circle P} [hne₁ : PtNe B A] [hne₂ : PtNe C B] [hne₃ : PtNe A C] (hl₁ : A LiesOn ω) (hl₂ : B LiesOn ω) (hl₃ : C LiesOn ω) : ¬ (colinear A B C) := by
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

end colinear

-- ray with circle
-- line with circle
end EuclidGeom
