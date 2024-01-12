import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular_trash

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

scoped infix : 50 " Secant " => Circle.DirLine.IsSecant
scoped infix : 50 " Tangent " => Circle.DirLine.IsTangent
scoped infix : 50 " Disjoint " => Circle.DirLine.IsDisjoint

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


@[ext]
structure DirLCInxpts (P : Type _) [EuclideanPlane P] where
  front : P
  back : P

lemma dist_pt_line_ineq {l : DirLine P} {ω : Circle P} (h : DirLine.IsIntersected l ω) : ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2 ≥ 0 := by
  have : dist_pt_line ω.center l.toLine ≤ ω.radius := h
  have : (dist_pt_line ω.center l.toLine) ^ 2 ≤ ω.radius ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg, abs_of_pos]
    exact this
    exact ω.rad_pos
    exact length_nonneg
  linarith

def DirLC_Intersected_pts {l : DirLine P} {ω : Circle P} (_h : DirLine.IsIntersected l ω) : DirLCInxpts P where
  front := ((Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec) +ᵥ (perp_foot ω.center l.toLine)
  back := (- (Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec) +ᵥ (perp_foot ω.center l.toLine)

lemma DirLC_intersected_pts_lieson_dlin {l : DirLine P} {ω : Circle P} (h : DirLine.IsIntersected l ω) : ((DirLC_Intersected_pts h).front LiesOn l) ∧ ((DirLC_Intersected_pts h).back LiesOn l) := by
  have hl : perp_foot ω.center l.toLine LiesOn l := by
    show perp_foot ω.center l.toLine LiesOn l.toLine
    apply perp_foot_lies_on_line
  constructor
  · have : (DirLC_Intersected_pts h).front LiesOn (Ray.mk_pt_dirline (perp_foot ω.center l.toLine) l hl) := by
      apply Ray.lies_on_iff.mpr
      use (Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2))
      constructor
      apply Real.sqrt_nonneg
      unfold DirLC_Intersected_pts Vec.mkPtPt
      simp
      calc
        _ = ((Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec) +ᵥ (perp_foot ω.center l.toLine) -ᵥ (perp_foot ω.center l.toLine) := rfl
        _ = (Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec := by rw [vadd_vsub]
    have : (DirLC_Intersected_pts h).front LiesOn (Ray.mk_pt_dirline (perp_foot ω.center l.toLine) l hl).toDirLine := by
      apply Ray.lies_on_toDirLine_iff_lies_on_or_lies_on_rev.mpr
      left; exact this
    rw [ray_of_pt_dirline_toDirLine_eq_dirline] at this
    exact this
  have : (DirLC_Intersected_pts h).back LiesOn (Ray.mk_pt_dirline (perp_foot ω.center l.toLine) l hl).reverse := by
    apply Ray.lies_on_iff.mpr
    use (Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2))
    constructor
    apply Real.sqrt_nonneg
    unfold DirLC_Intersected_pts Vec.mkPtPt
    simp
    calc
      _ = -((Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec) +ᵥ (perp_foot ω.center l.toLine) -ᵥ (perp_foot ω.center l.toLine) := rfl
      _ = -((Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec) := by rw [vadd_vsub]
  have : (DirLC_Intersected_pts h).back LiesOn (Ray.mk_pt_dirline (perp_foot ω.center l.toLine) l hl).toDirLine := by
    apply Ray.lies_on_toDirLine_iff_lies_on_or_lies_on_rev.mpr
    right; exact this
  rw [ray_of_pt_dirline_toDirLine_eq_dirline] at this
  exact this

theorem DirLC_intersected_pts_lieson_circle {l : DirLine P} {ω : Circle P} (h : DirLine.IsIntersected l ω) : ((DirLC_Intersected_pts h).front LiesOn ω) ∧ ((DirLC_Intersected_pts h).back LiesOn ω) := by
  constructor
  · have : (SEG ω.center (perp_foot ω.center l.toLine)).length ^ 2 + (SEG (DirLC_Intersected_pts h).front (perp_foot ω.center l.toLine)).length ^ 2 = (SEG ω.center (DirLC_Intersected_pts h).front).length ^ 2 := by apply Pythagoras_of_perp_foot _ _ (DirLC_intersected_pts_lieson_dlin h).1
    rw [← dist_pt_line] at this
    show dist ω.center (DirLC_Intersected_pts h).front = ω.radius
    apply (sq_eq_sq _ _).mp
    calc
      _ = (dist_pt_line ω.center l.toLine) ^ 2 + (SEG (DirLC_Intersected_pts h).front (perp_foot ω.center l.toLine)).length ^ 2 := by rw [← Seg.length_eq_dist, ← this]
      _ = (dist_pt_line ω.center l.toLine) ^ 2 + ‖VEC (DirLC_Intersected_pts h).front (perp_foot ω.center l.toLine)‖ ^ 2 := by
        rw [Seg.length_eq_norm_toVec]
        simp only [seg_toVec_eq_vec]
      _ = (dist_pt_line ω.center l.toLine) ^ 2 + ‖(Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec‖ ^ 2 := by
        unfold DirLC_Intersected_pts
        simp only [vec_of_vadd_pt_pt_eq_neg_vec, norm_neg]
      _ = ω.radius ^ 2 := by
        rw [norm_smul, Dir.norm_unitVec, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
        ring
        apply dist_pt_line_ineq h
    apply dist_nonneg
    apply le_iff_lt_or_eq.mpr
    left; exact ω.rad_pos
  have : (SEG ω.center (perp_foot ω.center l.toLine)).length ^ 2 + (SEG (DirLC_Intersected_pts h).back (perp_foot ω.center l.toLine)).length ^ 2 = (SEG ω.center (DirLC_Intersected_pts h).back).length ^ 2 := by apply Pythagoras_of_perp_foot _ _ (DirLC_intersected_pts_lieson_dlin h).2
  rw [← dist_pt_line] at this
  show dist ω.center (DirLC_Intersected_pts h).back = ω.radius
  apply (sq_eq_sq _ _).mp
  calc
    _ = (dist_pt_line ω.center l.toLine) ^ 2 + (SEG (DirLC_Intersected_pts h).back (perp_foot ω.center l.toLine)).length ^ 2 := by rw [← Seg.length_eq_dist, ← this]
    _ = (dist_pt_line ω.center l.toLine) ^ 2 + ‖VEC (DirLC_Intersected_pts h).back (perp_foot ω.center l.toLine)‖ ^ 2 := by
      rw [Seg.length_eq_norm_toVec]
      simp only [seg_toVec_eq_vec]
    _ = (dist_pt_line ω.center l.toLine) ^ 2 + ‖(Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec‖ ^ 2 := by
        unfold DirLC_Intersected_pts
        simp only [neg_smul, vec_of_vadd_pt_pt_eq_neg_vec, neg_neg]
    _ = ω.radius ^ 2 := by
      rw [norm_smul, Dir.norm_unitVec, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
      ring
      apply dist_pt_line_ineq h
  apply dist_nonneg
  apply le_iff_lt_or_eq.mpr
  left; exact ω.rad_pos

theorem DirLC_inx_pts_same_iff_tangent {l : DirLine P} {ω : Circle P} (h : DirLine.IsIntersected l ω) : (DirLC_Intersected_pts h).back = (DirLC_Intersected_pts h).front ↔ (l Tangent ω) := by
  unfold DirLC_Intersected_pts
  simp
  apply Iff.trans (neg_eq_self ℝ _)
  apply Iff.trans smul_eq_zero
  constructor
  · intro hh
    rcases hh with hh | hh
    · show dist_pt_line ω.center l.toLine = ω.radius
      have : ω.radius ^ 2 - dist_pt_line ω.center l.toLine ^ 2 = 0 := by
        apply (Real.sqrt_eq_zero _).mp hh
        apply dist_pt_line_ineq h
      apply (sq_eq_sq _ _).mp
      linarith
      unfold dist_pt_line
      exact length_nonneg
      apply le_iff_lt_or_eq.mpr
      left; exact ω.rad_pos
    exfalso
    have hh' : l.toDir.unitVec ≠ 0 := by simp
    tauto
  intro h
  have : dist_pt_line ω.center l.toLine = ω.radius := h
  left; rw [this, sub_self]
  simp

def DirLC_Tangent_pt {l : DirLine P} {ω : Circle P} (h : l Tangent ω) : P := (DirLC_Intersected_pts (DirLC_intersect_iff_tangent_or_secant.mpr (Or.inl h))).front

lemma DirLC_tangent_pt_ne_center {l : DirLine P} {ω : Circle P} (h : l Tangent ω) : DirLC_Tangent_pt h ≠ ω.center := by
  apply dist_pos.mp
  have : DirLC_Tangent_pt h LiesOn ω := by
    rcases DirLC_intersected_pts_lieson_circle (DirLC_intersect_iff_tangent_or_secant.mpr (Or.inl h)) with ⟨h₁, _⟩
    exact h₁
  have : dist ω.center (DirLC_Tangent_pt h) = ω.radius := this
  rw [dist_comm, this]
  exact ω.rad_pos

theorem DirLC_tangent_pt_center_perp_line {l : DirLine P} {ω : Circle P} (h : l Tangent ω) : (LIN ω.center (DirLC_Tangent_pt h) (DirLC_tangent_pt_ne_center h)) ⟂ l.toLine := by
  have h : dist_pt_line ω.center l.toLine = ω.radius := h
  have : DirLC_Tangent_pt h = perp_foot ω.center l.toLine := by
    unfold DirLC_Tangent_pt DirLC_Intersected_pts
    simp
    apply (Real.sqrt_eq_zero _).mpr
    rw [h]; ring
    rw [h]; linarith
  have : LIN ω.center (DirLC_Tangent_pt h) (DirLC_tangent_pt_ne_center h) = perp_line ω.center l.toLine := by
    simp_rw [this]
    apply line_of_self_perp_foot_eq_perp_line_of_not_lies_on
    intro hn
    have : dist_pt_line ω.center l.toLine = 0 := (dist_eq_zero_iff_lies_on _ _).mpr hn
    have : dist_pt_line ω.center l.toLine > 0 := by
      calc
        _ = ω.radius := h
        _ > 0 := ω.rad_pos
    linarith
  rw [this]
  unfold perp_line
  apply Line.proj_eq_of_mk_pt_proj

theorem DirLC_tangent_pt_eq_perp_foot {l : DirLine P} {ω : Circle P} (h : l Tangent ω) : DirLC_Tangent_pt h = perp_foot ω.center l := by
  have hp : (DLIN ω.center (DirLC_Tangent_pt h) (DirLC_tangent_pt_ne_center h)) ⟂ l := by
    show (DLIN ω.center (DirLC_Tangent_pt h) (DirLC_tangent_pt_ne_center h)).toProj = l.toProj.perp
    calc
      _ = (LIN ω.center (DirLC_Tangent_pt h) (DirLC_tangent_pt_ne_center h)).toProj := rfl
      _ = l.toLine.toProj.perp := DirLC_tangent_pt_center_perp_line h
      _ = l.toProj.perp := by rw [DirLine.toLine_toProj_eq_toProj]
  symm
  exact perp_foot_unique (DirLC_intersected_pts_lieson_dlin _).1 (hne := ⟨(DirLC_tangent_pt_ne_center h)⟩) hp




theorem DirLC_inxwith_iff_intersect {l : DirLine P} {ω : Circle P} : l InxWith ω ↔ DirLine.IsIntersected l ω := by
  unfold intersect
  constructor
  · rintro ⟨A, ⟨h₁, h₂⟩⟩
    show dist_pt_line ω.center l.toLine ≤ ω.radius
    calc
      _ ≤ dist ω.center A := by apply dist_pt_line_shortest _ _ h₁
      _ = ω.radius := h₂
  intro h
  use (DirLC_Intersected_pts h).front
  exact ⟨(DirLC_intersected_pts_lieson_dlin h).1, (DirLC_intersected_pts_lieson_circle h).1⟩

theorem DirLC_inxwith_iff_tangent_or_secant {l : DirLine P} {ω : Circle P} : l InxWith ω ↔ (l Tangent ω) ∨ (l Secant ω) := Iff.trans DirLC_inxwith_iff_intersect DirLC_intersect_iff_tangent_or_secant

/-
If we need, we can add some coercion to state that inx_pts with respect to "InxWith".
-/

-- def DirLC_Inx_pts {l : DirLine P} {ω : Circle P} (h : l InxWith ω) : DirLCInxpts P where
--   front := (DirLC_Intersected_pts (DirLC_inxwith_iff_intersect.mp h)).front
--   back := (DirLC_Intersected_pts (DirLC_inxwith_iff_intersect.mp h)).back

-- theorem DirLC_inx_pts_lieson_dlin {l : DirLine P} {ω : Circle P} (h : l InxWith ω) : ((DirLC_Inx_pts h).front LiesOn l) ∧ ((DirLC_Inx_pts h).back LiesOn l) := by sorry

-- theorem DirLC_inx_pts_lieson_circle {l : DirLine P} {ω : Circle P} (h : l InxWith ω) : ((DirLC_Inx_pts h).front LiesOn ω) ∧ ((DirLC_Inx_pts h).back LiesOn ω) := by sorry




/- DirLine and circle have at most two intersections. -/
/- inx pts' uniqueness -/
theorem DirLC_intersection_eq_inxpts {l : DirLine P} {ω : Circle P} {A : P} (h : DirLine.IsIntersected l ω) (h₁ : A LiesOn l.toLine) (h₂ : A LiesOn ω) : (A = (DirLC_Intersected_pts h).front) ∨ (A = (DirLC_Intersected_pts h).back) := by
  rcases (DirLC_intersect_iff_tangent_or_secant.mp h) with h' | h'
  · left
    show A = DirLC_Tangent_pt h'
    calc
      _ = perp_foot ω.center l := by
        apply eq_dist_eq_perp_foot h₁
        rw [h₂, h']
      _ = DirLC_Tangent_pt h' := by rw [DirLC_tangent_pt_eq_perp_foot _]
  contrapose! h₂
  intro h₃
  haveI hne₁ : PtNe A (DirLC_Intersected_pts h).front := ⟨h₂.1⟩
  haveI hne₂ : PtNe A (DirLC_Intersected_pts h).back := ⟨h₂.2⟩
  haveI hne₃ : PtNe (DirLC_Intersected_pts h).back (DirLC_Intersected_pts h).front := ⟨ by
    intro eq
    have h'' : l Tangent ω := (DirLC_inx_pts_same_iff_tangent h).mp eq
    have : dist_pt_line ω.center l = ω.radius := h''
    have : dist_pt_line ω.center l < ω.radius := h'
    linarith⟩
  have hc : colinear A (DirLC_Intersected_pts h).front (DirLC_Intersected_pts h).back := Line.linear h₁ (DirLC_intersected_pts_lieson_dlin h).1 (DirLC_intersected_pts_lieson_dlin h).2
  have hnc : ¬ (colinear A (DirLC_Intersected_pts h).front (DirLC_Intersected_pts h).back) := three_pts_lieson_circle_not_colinear h₃ (DirLC_intersected_pts_lieson_circle h).1 (DirLC_intersected_pts_lieson_circle h).2
  tauto

theorem pt_pt_tangent_eq_tangent_pt {A B : P} {ω : Circle P} (h₁ : A LiesOut ω) (h₂ : B LiesOn ω) (ht : (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) Tangent ω) : B = DirLC_Tangent_pt ht := by
  rcases (DirLC_intersection_eq_inxpts (DirLC_intersect_iff_tangent_or_secant.mpr (Or.inl ht)) (DirLine.snd_pt_lies_on_mk_pt_pt (_h :=  (pt_liesout_ne_pt_lieson h₁ h₂).symm)) h₂) with heq | heq
  exact heq
  rw [(DirLC_inx_pts_same_iff_tangent _).mpr ht] at heq
  exact heq

theorem pt_pt_tangent_perp {A B : P} {ω : Circle P} (h₁ : A LiesOut ω) (h₂ : B LiesOn ω) (ht : (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) Tangent ω) : (DLIN ω.center B (pt_lieson_ne_center h₂).out) ⟂ (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) := by
  have heq : B = DirLC_Tangent_pt ht := pt_pt_tangent_eq_tangent_pt h₁ h₂ ht
  show (DLIN ω.center B (pt_lieson_ne_center h₂).out).toProj = (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm).toProj.perp
  calc
    _ = (DLIN ω.center (DirLC_Tangent_pt ht) (DirLC_tangent_pt_ne_center ht)).toProj := by congr
    _ = (LIN ω.center (DirLC_Tangent_pt ht) (DirLC_tangent_pt_ne_center ht)).toProj := rfl
    _ = (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm).toLine.toProj.perp := DirLC_tangent_pt_center_perp_line _

theorem pt_pt_perp_tangent {A B : P} {ω : Circle P} (h₁ : A LiesOut ω) (h₂ : B LiesOn ω) (hp : (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) ⟂ (DLIN ω.center B (pt_lieson_ne_center h₂).out)) : (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) Tangent ω := by
  have heq : perp_foot ω.center (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) = B := perp_foot_unique (DirLine.snd_pt_lies_on_mk_pt_pt (_h := ⟨ (pt_liesout_ne_pt_lieson h₁ h₂).out.symm ⟩ )) (hne := (pt_lieson_ne_center h₂)) hp.symm
  show dist_pt_line ω.center (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) = ω.radius
  calc
    _ = (SEG ω.center (perp_foot ω.center (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm))).length := rfl
    _ = (SEG ω.center B).length := by rw [heq]
    _ = dist ω.center B := Seg.length_eq_dist
    _ = ω.radius := h₂

theorem pt_pt_perp_eq_tangent_pt {A B : P} {ω : Circle P} (h₁ : A LiesOut ω) (h₂ : B LiesOn ω) (hp : (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) ⟂ (DLIN ω.center B (pt_lieson_ne_center h₂).out)) : B = DirLC_Tangent_pt (pt_pt_perp_tangent h₁ h₂ hp) := by
  calc
    _ = perp_foot ω.center (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) := by rw [perp_foot_unique (DirLine.snd_pt_lies_on_mk_pt_pt (_h := ⟨(pt_liesout_ne_pt_lieson h₁ h₂).out.symm⟩)) (hne := (pt_lieson_ne_center h₂)) hp.symm]
    _ = DirLC_Tangent_pt (pt_pt_perp_tangent h₁ h₂ hp) := by rw [DirLC_tangent_pt_eq_perp_foot _]

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
