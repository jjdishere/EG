import EuclideanGeometry.Foundation.Axiom.Circle.Basic

noncomputable section
namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

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

open Circle

namespace DirLC

theorem disjoint_pt_liesout_circle {l : DirLine P} {ω : Circle P} {A : P} (h : l Disjoint ω) (hh : A LiesOn l.toLine) : A LiesOut ω := by
  show dist ω.center A > ω.radius
  calc
    _ ≥ dist_pt_line ω.center l.toLine := by apply dist_pt_line_shortest _ _ hh
    _ > ω.radius := h


theorem intersect_iff_tangent_or_secant {l : DirLine P} {ω : Circle P} : (DirLine.IsIntersected l ω) ↔ (l Tangent ω) ∨ (l Secant ω) := by
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

theorem pt_liesint_secant {l : DirLine P} {ω : Circle P} {A : P} (h₁ : A LiesInt ω) (h₂ : A LiesOn l) : l Secant ω := by
  have : dist ω.center A < ω.radius := h₁
  have : dist_pt_line ω.center l ≤ dist ω.center A := dist_pt_line_shortest ω.center A h₂
  show dist_pt_line ω.center l < ω.radius
  linarith

theorem pt_liesint_intersect {l : DirLine P} {ω : Circle P} {A : P} (h₁ : A LiesInt ω) (h₂ : A LiesOn l) : DirLine.IsIntersected l ω := by
  apply intersect_iff_tangent_or_secant.mpr
  right
  apply pt_liesint_secant h₁ h₂

end DirLC

@[ext]
structure DirLCInxpts (P : Type*) [EuclideanPlane P] where
  front : P
  back : P

namespace DirLC

lemma dist_pt_line_ineq {l : DirLine P} {ω : Circle P} (h : DirLine.IsIntersected l ω) : ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2 ≥ 0 := by
  have : dist_pt_line ω.center l.toLine ≤ ω.radius := h
  have : (dist_pt_line ω.center l.toLine) ^ 2 ≤ ω.radius ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg, abs_of_pos]
    exact this
    exact ω.rad_pos
    exact Seg.length_nonneg
  linarith

def Inxpts {l : DirLine P} {ω : Circle P} (_h : DirLine.IsIntersected l ω) : DirLCInxpts P where
  front := ((Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec) +ᵥ (perp_foot ω.center l.toLine)
  back := (- (Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec) +ᵥ (perp_foot ω.center l.toLine)

lemma inx_pts_lieson_dlin {l : DirLine P} {ω : Circle P} (h : DirLine.IsIntersected l ω) : ((Inxpts h).front LiesOn l) ∧ ((Inxpts h).back LiesOn l) := by
  have hl : perp_foot ω.center l.toLine LiesOn l := by apply perp_foot_lies_on_line
  constructor
  · have : (Inxpts h).front LiesOn (Ray.mk_pt_dirline (perp_foot ω.center l.toLine) l hl) := by
      apply Ray.lies_on_iff.mpr
      use (Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2))
      constructor
      apply Real.sqrt_nonneg
      unfold Inxpts Vec.mkPtPt
      simp
      calc
        _ = ((Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec) +ᵥ (perp_foot ω.center l.toLine) -ᵥ (perp_foot ω.center l.toLine) := rfl
        _ = (Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec := by rw [vadd_vsub]
    have : (Inxpts h).front LiesOn (Ray.mk_pt_dirline (perp_foot ω.center l.toLine) l hl).toDirLine := by
      apply Ray.lies_on_toDirLine_iff_lies_on_or_lies_on_rev.mpr
      left; exact this
    rw [ray_of_pt_dirline_toDirLine_eq_dirline] at this
    exact this
  have : (Inxpts h).back LiesOn (Ray.mk_pt_dirline (perp_foot ω.center l.toLine) l hl).reverse := by
    apply Ray.lies_on_iff.mpr
    use (Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2))
    constructor
    apply Real.sqrt_nonneg
    unfold Inxpts Vec.mkPtPt
    simp
    calc
      _ = -((Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec) +ᵥ (perp_foot ω.center l.toLine) -ᵥ (perp_foot ω.center l.toLine) := rfl
      _ = -((Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec) := by rw [vadd_vsub]
  have : (Inxpts h).back LiesOn (Ray.mk_pt_dirline (perp_foot ω.center l.toLine) l hl).toDirLine := by
    apply Ray.lies_on_toDirLine_iff_lies_on_or_lies_on_rev.mpr
    right; exact this
  rw [ray_of_pt_dirline_toDirLine_eq_dirline] at this
  exact this

theorem inx_pts_lieson_circle {l : DirLine P} {ω : Circle P} (h : DirLine.IsIntersected l ω) : ((Inxpts h).front LiesOn ω) ∧ ((Inxpts h).back LiesOn ω) := by
  constructor
  · have : (SEG ω.center (perp_foot ω.center l.toLine)).length ^ 2 + (SEG (Inxpts h).front (perp_foot ω.center l.toLine)).length ^ 2 = (SEG ω.center (Inxpts h).front).length ^ 2 := by apply Pythagoras_of_perp_foot _ _ (inx_pts_lieson_dlin h).1
    rw [← dist_pt_line] at this
    show dist ω.center (Inxpts h).front = ω.radius
    apply (sq_eq_sq _ _).mp
    calc
      _ = (dist_pt_line ω.center l.toLine) ^ 2 + (SEG (Inxpts h).front (perp_foot ω.center l.toLine)).length ^ 2 := by rw [← Seg.length_eq_dist, ← this]
      _ = (dist_pt_line ω.center l.toLine) ^ 2 + ‖VEC (Inxpts h).front (perp_foot ω.center l.toLine)‖ ^ 2 := by
        rw [Seg.length_eq_norm_toVec]
        simp only [seg_toVec_eq_vec]
      _ = (dist_pt_line ω.center l.toLine) ^ 2 + ‖(Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec‖ ^ 2 := by
        unfold Inxpts
        simp only [vec_of_vadd_pt_pt_eq_neg_vec, norm_neg]
      _ = ω.radius ^ 2 := by
        rw [norm_smul, Dir.norm_unitVec, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
        ring
        apply dist_pt_line_ineq h
    apply dist_nonneg
    apply le_iff_lt_or_eq.mpr
    left; exact ω.rad_pos
  have : (SEG ω.center (perp_foot ω.center l.toLine)).length ^ 2 + (SEG (Inxpts h).back (perp_foot ω.center l.toLine)).length ^ 2 = (SEG ω.center (Inxpts h).back).length ^ 2 := by apply Pythagoras_of_perp_foot _ _ (inx_pts_lieson_dlin h).2
  rw [← dist_pt_line] at this
  show dist ω.center (Inxpts h).back = ω.radius
  apply (sq_eq_sq _ _).mp
  calc
    _ = (dist_pt_line ω.center l.toLine) ^ 2 + (SEG (Inxpts h).back (perp_foot ω.center l.toLine)).length ^ 2 := by rw [← Seg.length_eq_dist, ← this]
    _ = (dist_pt_line ω.center l.toLine) ^ 2 + ‖VEC (Inxpts h).back (perp_foot ω.center l.toLine)‖ ^ 2 := by
      rw [Seg.length_eq_norm_toVec]
      simp only [seg_toVec_eq_vec]
    _ = (dist_pt_line ω.center l.toLine) ^ 2 + ‖(Real.sqrt (ω.radius ^ 2 - (dist_pt_line ω.center l.toLine) ^ 2)) • l.toDir.unitVec‖ ^ 2 := by
        unfold Inxpts
        simp only [neg_smul, vec_of_vadd_pt_pt_eq_neg_vec, neg_neg]
    _ = ω.radius ^ 2 := by
      rw [norm_smul, Dir.norm_unitVec, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
      ring
      apply dist_pt_line_ineq h
  apply dist_nonneg
  apply le_iff_lt_or_eq.mpr
  left; exact ω.rad_pos

theorem inx_pts_same_iff_tangent {l : DirLine P} {ω : Circle P} (h : DirLine.IsIntersected l ω) : (Inxpts h).back = (Inxpts h).front ↔ (l Tangent ω) := by
  unfold Inxpts
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
      exact Seg.length_nonneg
      apply le_iff_lt_or_eq.mpr
      left; exact ω.rad_pos
    exfalso
    have hh' : l.toDir.unitVec ≠ 0 := by simp
    tauto
  intro h
  have : dist_pt_line ω.center l.toLine = ω.radius := h
  left; rw [this, sub_self]
  simp

lemma inx_pts_ne_center {l : DirLine P} {ω : Circle P} (h : DirLine.IsIntersected l ω) : ((Inxpts h).front ≠ ω.center) ∧ ((Inxpts h).back ≠ ω.center) := by
  constructor
  · apply (pt_lieson_ne_center (inx_pts_lieson_circle h).1).out
  apply (pt_lieson_ne_center (inx_pts_lieson_circle h).2).out

theorem inx_pts_antipode_iff_center_lieson {l : DirLine P} {ω : Circle P} (h : DirLine.IsIntersected l ω) : IsAntipode ω (inx_pts_lieson_circle h).1 (inx_pts_lieson_circle h).2 ↔ ω.center LiesOn l := sorry

theorem inxwith_iff_intersect {l : DirLine P} {ω : Circle P} : l InxWith ω ↔ DirLine.IsIntersected l ω := by
  unfold intersect
  constructor
  · rintro ⟨A, ⟨h₁, h₂⟩⟩
    show dist_pt_line ω.center l.toLine ≤ ω.radius
    calc
      _ ≤ dist ω.center A := by apply dist_pt_line_shortest _ _ h₁
      _ = ω.radius := h₂
  intro h
  use (Inxpts h).front
  exact ⟨(inx_pts_lieson_dlin h).1, (inx_pts_lieson_circle h).1⟩

theorem inxwith_iff_tangent_or_secant {l : DirLine P} {ω : Circle P} : l InxWith ω ↔ (l Tangent ω) ∨ (l Secant ω) := Iff.trans inxwith_iff_intersect intersect_iff_tangent_or_secant


/- Tangent point -/
def Tangentpt {l : DirLine P} {ω : Circle P} (h : l Tangent ω) : P := (Inxpts (intersect_iff_tangent_or_secant.mpr (Or.inl h))).front

lemma tangent_pt_ne_center {l : DirLine P} {ω : Circle P} (h : l Tangent ω) : Tangentpt h ≠ ω.center := (inx_pts_ne_center (intersect_iff_tangent_or_secant.mpr (Or.inl h))).1

theorem tangent_pt_center_perp_line {l : DirLine P} {ω : Circle P} (h : l Tangent ω) : (LIN ω.center (Tangentpt h) (tangent_pt_ne_center h)) ⟂ l.toLine := by
  have h : dist_pt_line ω.center l.toLine = ω.radius := h
  have : Tangentpt h = perp_foot ω.center l.toLine := by
    unfold Tangentpt Inxpts
    simp
    apply (Real.sqrt_eq_zero _).mpr
    rw [h]; ring
    rw [h]; linarith
  have : LIN ω.center (Tangentpt h) (tangent_pt_ne_center h) = perp_line ω.center l.toLine := by
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

theorem tangent_pt_eq_perp_foot {l : DirLine P} {ω : Circle P} (h : l Tangent ω) : Tangentpt h = perp_foot ω.center l := by
  haveI : PtNe (Tangentpt h) ω.center := ⟨tangent_pt_ne_center h⟩
  have hp : (DLIN ω.center (Tangentpt h)) ⟂ l := by
    show (DLIN ω.center (Tangentpt h)).toProj = l.toProj.perp
    calc
      _ = (LIN ω.center (Tangentpt h)).toProj := rfl
      _ = l.toLine.toProj.perp := tangent_pt_center_perp_line h
      _ = l.toProj.perp := by rw [DirLine.toLine_toProj_eq_toProj]
  symm
  exact perp_foot_unique (inx_pts_lieson_dlin _).1 hp

end DirLC

/-
If we need, we can add some coercion to state that inx_pts with respect to "InxWith".
-/

-- def Inxpts {l : DirLine P} {ω : Circle P} (h : l InxWith ω) : DirLCInxpts P where
--   front := (Inxpts (DirLC_inxwith_iff_intersect.mp h)).front
--   back := (Inxpts (DirLC_inxwith_iff_intersect.mp h)).back

-- theorem Inxpts_lieson_dlin {l : DirLine P} {ω : Circle P} (h : l InxWith ω) : ((Inxpts h).front LiesOn l) ∧ ((Inxpts h).back LiesOn l) := by sorry

-- theorem Inxpts_lieson_circle {l : DirLine P} {ω : Circle P} (h : l InxWith ω) : ((Inxpts h).front LiesOn ω) ∧ ((Inxpts h).back LiesOn ω) := by sorry




/- DirLine and circle have at most two intersections. -/
/- inx pts' uniqueness -/
namespace Circle

open DirLC

theorem DirLC_intersection_eq_inxpts {l : DirLine P} {ω : Circle P} {A : P} (h : DirLine.IsIntersected l ω) (h₁ : A LiesOn l.toLine) (h₂ : A LiesOn ω) : (A = (Inxpts h).front) ∨ (A = (Inxpts h).back) := by
  rcases (intersect_iff_tangent_or_secant.mp h) with h' | h'
  · left
    show A = Tangentpt h'
    calc
      _ = perp_foot ω.center l := by
        apply eq_dist_eq_perp_foot h₁
        rw [h₂, h']
      _ = Tangentpt h' := by rw [tangent_pt_eq_perp_foot _]
  contrapose! h₂
  intro h₃
  haveI hne₁ : PtNe A (Inxpts h).front := ⟨h₂.1⟩
  haveI hne₂ : PtNe A (Inxpts h).back := ⟨h₂.2⟩
  haveI hne₃ : PtNe (Inxpts h).back (Inxpts h).front := ⟨ by
    intro eq
    have h'' : l Tangent ω := (inx_pts_same_iff_tangent h).mp eq
    have : dist_pt_line ω.center l = ω.radius := h''
    have : dist_pt_line ω.center l < ω.radius := h'
    linarith⟩
  have hc : Collinear A (Inxpts h).front (Inxpts h).back := Line.linear h₁ (inx_pts_lieson_dlin h).1 (inx_pts_lieson_dlin h).2
  have hnc : ¬ (Collinear A (Inxpts h).front (Inxpts h).back) := three_pts_lieson_circle_not_collinear h₃ (inx_pts_lieson_circle h).1 (inx_pts_lieson_circle h).2
  tauto

theorem pt_pt_tangent_eq_tangent_pt {A B : P} {ω : Circle P} (h₁ : A LiesOut ω) (h₂ : B LiesOn ω) (ht : (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) Tangent ω) : B = Tangentpt ht := by
  haveI : PtNe A B := pt_liesout_ne_pt_lieson h₁ h₂
  rcases (DirLC_intersection_eq_inxpts (intersect_iff_tangent_or_secant.mpr (Or.inl ht)) DirLine.snd_pt_lies_on_mk_pt_pt h₂) with heq | heq
  exact heq
  rw [(inx_pts_same_iff_tangent _).mpr ht] at heq
  exact heq

theorem chord_toDirLine_intersected {ω : Circle P} (s : Chord P ω) : DirLine.IsIntersected s.1.toDirLine ω := by
  show dist_pt_line ω.center s.1.toDirLine ≤ ω.radius
  rw [← s.2.1]
  apply dist_pt_line_shortest ω.center s.1.source DirLine.fst_pt_lies_on_mk_pt_pt

theorem chord_toDirLine_inx_front_pt_eq_target {ω : Circle P} (s : Chord P ω) : (Inxpts (chord_toDirLine_intersected s)).front = s.1.target := sorry

theorem chord_toDirLine_inx_back_pt_eq_source {ω : Circle P} (s : Chord P ω) : (Inxpts (chord_toDirLine_intersected s)).back = s.1.source := sorry

/- Equivalent condition for tangency -/
theorem pt_pt_tangent_perp {A B : P} {ω : Circle P} (h₁ : A LiesOut ω) (h₂ : B LiesOn ω) (ht : (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) Tangent ω) : (DLIN ω.center B (pt_lieson_ne_center h₂).out) ⟂ (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) := by
  haveI : PtNe A B := pt_liesout_ne_pt_lieson h₁ h₂
  haveI : PtNe B ω.center := pt_lieson_ne_center h₂
  haveI : PtNe (Tangentpt ht) ω.center := ⟨tangent_pt_ne_center ht⟩
  have heq : B = Tangentpt ht := pt_pt_tangent_eq_tangent_pt h₁ h₂ ht
  show (DLIN ω.center B).toProj = (DLIN A B).toProj.perp
  calc
    _ = (DLIN ω.center (Tangentpt ht)).toProj := by congr
    _ = (LIN ω.center (Tangentpt ht)).toProj := rfl
    _ = (DLIN A B).toLine.toProj.perp := tangent_pt_center_perp_line _

theorem pt_pt_perp_tangent {A B : P} {ω : Circle P} (h₁ : A LiesOut ω) (h₂ : B LiesOn ω) (hp : (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) ⟂ (DLIN ω.center B (pt_lieson_ne_center h₂).out)) : (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) Tangent ω := by
  haveI : PtNe A B := pt_liesout_ne_pt_lieson h₁ h₂
  haveI : PtNe B ω.center := pt_lieson_ne_center h₂
  have heq : perp_foot ω.center (DLIN A B) = B := perp_foot_unique DirLine.snd_pt_lies_on_mk_pt_pt hp.symm
  show dist_pt_line ω.center (DLIN A B) = ω.radius
  calc
    _ = (SEG ω.center (perp_foot ω.center (DLIN A B))).length := rfl
    _ = (SEG ω.center B).length := by rw [heq]
    _ = dist ω.center B := Seg.length_eq_dist
    _ = ω.radius := h₂

theorem pt_pt_perp_eq_tangent_pt {A B : P} {ω : Circle P} (h₁ : A LiesOut ω) (h₂ : B LiesOn ω) (hp : (DLIN A B (pt_liesout_ne_pt_lieson h₁ h₂).out.symm) ⟂ (DLIN ω.center B (pt_lieson_ne_center h₂).out)) : B = Tangentpt (pt_pt_perp_tangent h₁ h₂ hp) := by
  haveI : PtNe A B := pt_liesout_ne_pt_lieson h₁ h₂
  haveI : PtNe B ω.center := pt_lieson_ne_center h₂
  calc
    _ = perp_foot ω.center (DLIN A B) := by rw [perp_foot_unique DirLine.snd_pt_lies_on_mk_pt_pt hp.symm]
    _ = Tangentpt (pt_pt_perp_tangent h₁ h₂ hp) := by rw [tangent_pt_eq_perp_foot _]

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
