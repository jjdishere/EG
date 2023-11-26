import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular_trash
import EuclideanGeometry.Foundation.Axiom.Triangle.Trigonometric
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

section DirLC

namespace Circle

protected def DirLine.IsDisjoint (l : DirLine P) (ω : Circle P) : Prop := dist_pt_line ω.center l.toLine > ω.radius

protected def DirLine.IsTangent (l : DirLine P) (ω : Circle P) : Prop := dist_pt_line ω.center l.toLine = ω.radius

protected def DirLine.IsSecant (l : DirLine P) (ω : Circle P) : Prop := dist_pt_line ω.center l.toLine < ω.radius

protected def DirLine.IsIntersected (l : DirLine P) (ω : Circle P) : Prop := dist_pt_line ω.center l.toLine ≤ ω.radius

end Circle

scoped infix : 50 "Secant" => Circle.DirLine.IsSecant
scoped infix : 50 "Tangent" => Circle.DirLine.IsTangent
scoped infix : 50 "Disjoint" => Circle.DirLine.IsDisjoint

namespace Circle

theorem DirLC_disjoint_pt_liesout_circle {l : DirLine P} {ω : Circle P} {A : P} (h : l Disjoint ω) (hh : A LiesOn l.toLine) : A LiesOut ω := by
  show dist ω.center A > ω.radius
  calc
    _ ≥ dist_pt_line ω.center l.toLine := by apply dist_pt_line_shortest _ _ hh
    _ > ω.radius := h


theorem DirLC_intersect_iff_tangent_or_secant {l : DirLine P} {ω : Circle P} : (DirLine.IsIntersected l ω) ↔ (l Tangent ω) ∨ (l Secant ω) := by
  constructor
  · intro h
    have : dist_pt_line ω.center l.toLine ≤ ω.radius := h
    by_cases h₁ : dist_pt_line ω.center l.toLine < ω.radius
    · right; exact h₁
    left
    push_neg at h₁
    show dist_pt_line ω.center l.toLine = ω.radius
    linarith
  intro h
  show dist_pt_line ω.center l.toLine ≤ ω.radius
  rcases h with h | h
  have : dist_pt_line ω.center l.toLine = ω.radius := h
  linarith
  have : dist_pt_line ω.center l.toLine < ω.radius := h
  linarith

theorem DirLC_inxwith_iff_intersect {l : DirLine P} {ω : Circle P} : l InxWith ω ↔ DirLine.IsIntersected l ω := sorry

theorem DirLC_inxwith_iff_tangent_or_secant {l : DirLine P} {ω : Circle P} : l InxWith ω ↔ (l Tangent ω) ∨ (l Secant ω) := Iff.trans DirLC_inxwith_iff_intersect DirLC_intersect_iff_tangent_or_secant


@[ext]
structure DirLCInxpts (P : Type _) [EuclideanPlane P] where
  front : P
  back : P

lemma dist_pt_line_ineq {l : DirLine P} {ω : Circle P} (h : l InxWith ω) : ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2 ≥ 0 := by
  have : dist_pt_line ω.center l.toLine ≤ ω.radius := by apply DirLC_inxwith_iff_intersect.mp h
  have : (dist_pt_line ω.center l.toLine) ^ 2 ≤ ω.radius ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg, abs_of_pos]
    exact this
    exact ω.rad_pos
    unfold dist_pt_line
    show 0 ≤ Vec.norm (VEC ω.center (perp_foot ω.center l.toLine))
    apply Vec.norm_nonnegative
  linarith

def DirLC_Intersected_pts {l : DirLine P} {ω : Circle P} (h : l InxWith ω) : DirLCInxpts P where
  front := ((Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.1) +ᵥ (perp_foot ω.center l.toLine)
  back := (- (Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.1) +ᵥ (perp_foot ω.center l.toLine)

lemma DirLC_inx_pts_lieson_dlin {l : DirLine P} {ω : Circle P} (h : l InxWith ω) : ((DirLC_Intersected_pts h).front LiesOn l) ∧ ((DirLC_Intersected_pts h).back LiesOn l) := by
  constructor
  · sorry
  sorry

theorem DirLC_inx_pts_lieson_circle {l : DirLine P} {ω : Circle P} (h : l InxWith ω) : ((DirLC_Intersected_pts h).front LiesOn ω) ∧ ((DirLC_Intersected_pts h).back LiesOn ω) := by
  constructor
  · have : (SEG ω.center (perp_foot ω.center l.toLine)).length ^ 2 + (SEG (DirLC_Intersected_pts h).front (perp_foot ω.center l.toLine)).length ^ 2 = (SEG ω.center (DirLC_Intersected_pts h).front).length ^ 2 := by apply Pythagoras_of_perp_foot _ _ (DirLC_inx_pts_lieson_dlin h).1
    rw [← dist_pt_line] at this
    show dist ω.center (DirLC_Intersected_pts h).front = ω.radius
    apply (sq_eq_sq _ _).mp
    calc
      _ = (dist_pt_line ω.center l.toLine) ^ 2 + (SEG (DirLC_Intersected_pts h).front (perp_foot ω.center l.toLine)).length ^ 2 := by rw [← Seg.length_eq_dist, ← this]
      _ = (dist_pt_line ω.center l.toLine) ^ 2 + (Vec.norm (VEC (DirLC_Intersected_pts h).front (perp_foot ω.center l.toLine))) ^ 2 := rfl
      _ = (dist_pt_line ω.center l.toLine) ^ 2 + (Vec.norm ((Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.1)) ^ 2 := by
        unfold DirLC_Intersected_pts
        simp
      _ = ω.radius ^ 2 := by
        rw [Vec.norm_smul_eq_mul_norm, Dir.norm_of_dir_tovec_eq_one, mul_one, Real.sq_sqrt]
        ring
        apply dist_pt_line_ineq h
        apply Real.sqrt_nonneg
    apply dist_nonneg
    apply le_iff_lt_or_eq.mpr
    left; exact ω.rad_pos
  have : (SEG ω.center (perp_foot ω.center l.toLine)).length ^ 2 + (SEG (DirLC_Intersected_pts h).back (perp_foot ω.center l.toLine)).length ^ 2 = (SEG ω.center (DirLC_Intersected_pts h).back).length ^ 2 := by apply Pythagoras_of_perp_foot _ _ (DirLC_inx_pts_lieson_dlin h).2
  rw [← dist_pt_line] at this
  show dist ω.center (DirLC_Intersected_pts h).back = ω.radius
  apply (sq_eq_sq _ _).mp
  calc
    _ = (dist_pt_line ω.center l.toLine) ^ 2 + (SEG (DirLC_Intersected_pts h).back (perp_foot ω.center l.toLine)).length ^ 2 := by rw [← Seg.length_eq_dist, ← this]
    _ = (dist_pt_line ω.center l.toLine) ^ 2 + (Vec.norm (VEC (DirLC_Intersected_pts h).back (perp_foot ω.center l.toLine))) ^ 2 := rfl
    _ = (dist_pt_line ω.center l.toLine) ^ 2 + (Vec.norm ((Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.1)) ^ 2 := by
        unfold DirLC_Intersected_pts
        simp
    _ = ω.radius ^ 2 := by
      rw [Vec.norm_smul_eq_mul_norm, Dir.norm_of_dir_tovec_eq_one, mul_one, Real.sq_sqrt]
      ring
      apply dist_pt_line_ineq h
      apply Real.sqrt_nonneg
  apply dist_nonneg
  apply le_iff_lt_or_eq.mpr
  left; exact ω.rad_pos

theorem DirLC_inx_pts_same_iff_tangent {l : DirLine P} {ω : Circle P} (h : l InxWith ω) : (DirLC_Intersected_pts h).front = (DirLC_Intersected_pts h).back ↔ (l Tangent ω) := by
  unfold DirLC_Intersected_pts
  simp
  apply Iff.trans eq_neg_self_iff
  apply Iff.trans mul_eq_zero
  constructor
  · intro hh
    rcases hh with hh | hh
    · show dist_pt_line ω.center l.toLine = ω.radius
      have : ω.radius ^ 2 - dist_pt_line ω.center l.toLine ^ 2 = 0 := by
        apply (Real.sqrt_eq_zero _).mp (Complex.ofReal_eq_zero.mp hh)
        apply dist_pt_line_ineq h
      apply (sq_eq_sq _ _).mp
      linarith
      unfold dist_pt_line
      show 0 ≤ Vec.norm (VEC ω.center (perp_foot ω.center l.toLine))
      apply Vec.norm_nonnegative
      apply le_iff_lt_or_eq.mpr
      left; exact ω.rad_pos
    exfalso
    have hh' : l.toDir.toVec ≠ 0 := by apply Dir.tovec_ne_zero
    tauto
  intro h
  have : dist_pt_line ω.center l.toLine = ω.radius := h
  left; rw [this, sub_self]
  simp

def DirLC_Tangent_pt {l : DirLine P} {ω : Circle P} (h : l Tangent ω) : P := (DirLC_Intersected_pts (DirLC_inxwith_iff_tangent_or_secant.mpr (Or.inl h))).front

lemma DirLC_tangent_pt_ne_center {l : DirLine P} {ω : Circle P} (h : l Tangent ω) : DirLC_Tangent_pt h ≠ ω.center := sorry

theorem DirLC_tangent_pt_center_perp_line {l : DirLine P} {ω : Circle P} (h : l Tangent ω) : (LIN ω.center (DirLC_Tangent_pt h) (DirLC_tangent_pt_ne_center h)) ⟂ l.toLine := sorry

/- DirLine and circle have at most two intersections. -/
/- maybe not need -/
theorem DirLC_intersection_eq_inxpts {l : DirLine P} {ω : Circle P} {A : P} (h : l InxWith ω) (h₁ : A LiesOn l.toLine) (h₂ : A LiesOn ω) : (A = (DirLC_Intersected_pts h).front) ∨ (A = (DirLC_Intersected_pts h).back) := sorry

end Circle

end DirLC


section LC

namespace Circle

protected def Line.IsDisjoint (l : Line P) (ω : Circle P) : Prop := dist_pt_line ω.center l > ω.radius

protected def Line.IsTangent (l : Line P) (ω : Circle P) : Prop := dist_pt_line ω.center l = ω.radius

protected def Line.IsSecant (l : Line P) (ω : Circle P) : Prop := dist_pt_line ω.center l < ω.radius

protected def Line.IsIntersected (l : Line P) (ω : Circle P) : Prop := dist_pt_line ω.center l ≤ ω.radius

end Circle

end LC

end EuclidGeom
