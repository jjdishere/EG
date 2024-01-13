import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem ne_source_of_lies_int_seg_nd (A B C : P) [hne : PtNe B A] (h : C LiesInt (SEG_nd A B)) : C ≠ A := by sorry

theorem ne_source_of_lies_int_seg (A B C : P) (h2 : C LiesInt (SEG A B)) : C ≠ A := by sorry

theorem eq_todir_of_lies_int_seg_nd (A B C : P) [hne : PtNe B A] (h : C LiesInt (SEG A B)) : (SEG_nd A B).toDir = (SEG_nd A C (ne_source_of_lies_int_seg_nd A B C h)).toDir := by sorry

theorem lies_int_seg_nd_of_lies_int_seg (A B C : P) [hne : PtNe B A] (h : C LiesInt (SEG A B)) : C LiesInt (SEG_nd A B) := by sorry

theorem lies_on_seg_nd_of_lies_on_seg (A B C : P) [hne : PtNe B A] (h : C LiesOn (SEG A B)) : C LiesOn (SEG_nd A B) := by sorry

theorem same_dist_eq_or_eq_neg {A B C : P} [hne : PtNe B A] (h : C LiesOn (LIN A B)) (heq : dist A C = dist A B) : (C = B) ∨ (VEC A C = VEC B A) := by
  have : LIN A B = (RAY A B).toLine := rfl
  rw [this] at h
  rcases Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mp h with h | h
  · left; apply (eq_iff_vec_eq_zero _ _).mpr
    have : VEC A C = (dist A C) • (RAY A B).2.unitVec := Ray.lieson_eq_dist h
    calc
      _ = VEC A C - VEC A B := by rw [vec_sub_vec]
      _ = (dist A B) • (RAY A B).2.unitVec - VEC A B := by rw [this, heq]
      _ = (dist A B) • (RAY A B).2.unitVec - ‖VEC_nd A B‖ • (VEC_nd A B).toDir.unitVec := by simp
      _ = (dist A B) • (RAY A B).2.unitVec - ‖VEC_nd A B‖ • (RAY A B).2.unitVec := rfl
      _ = 0 := by
        rw [← sub_smul, dist_comm, NormedAddTorsor.dist_eq_norm']
        simp
        apply sub_eq_zero.mpr
        rfl
  right
  calc
    _ = (dist A C) • (RAY A B).reverse.2.unitVec := Ray.lieson_eq_dist h
    _ = (dist A C) • (- (VEC_nd A B).toDir.unitVec) := by simp
    _ = (dist A B) • (- (VEC_nd A B).toDir.unitVec) := by rw [heq]
    _ = - (‖VEC_nd A B‖ • (VEC_nd A B).toDir.unitVec) := by
      rw [smul_neg, dist_comm, NormedAddTorsor.dist_eq_norm']
      rfl
    _ = - (VEC_nd A B).1 := by simp
    _ = - VEC A B := rfl
    _ = VEC B A := by rw [neg_vec]

theorem distinct_pts_same_dist_vec_eq {A B C : P} [hne₁ : PtNe B A] [hne₂ : PtNe C B] (h : C LiesOn (LIN A B)) (heq : dist A C = dist A B) : VEC B A = VEC A C := by
  rcases same_dist_eq_or_eq_neg h heq with rfl | hh
  · exact absurd rfl hne₂.out
  exact hh.symm

theorem midpoint_dist_lt_iff_liesint {A B C : P} [hne : PtNe B C] (h : A LiesOn (LIN B C)) : dist A (SEG B C).midpoint < dist B (SEG B C).midpoint ↔ A LiesInt (SEG B C) := sorry

theorem midpoint_dist_eq_iff_eq_endpts {A B C : P} [hne : PtNe B C] (h : A LiesOn (LIN B C)) : dist A (SEG B C).midpoint = dist B (SEG B C).midpoint ↔ (A = B) ∨ (A = C) := by
  haveI : PtNe (SEG B C).midpoint B := ⟨SegND.midpt_ne_source (seg_nd := SEG_nd B C)⟩
  constructor
  · intro hh
    rw [dist_comm, ← Seg.length_eq_dist, dist_comm, Seg.length_eq_dist] at hh
    have : A LiesOn (LIN (SEG B C).midpoint B) := by sorry
    rcases same_dist_eq_or_eq_neg this hh with h₁ | h₂
    · left; exact h₁
    right
    apply (eq_iff_vec_eq_zero _ _).mpr
    calc
      _ = VEC (SEG B C).midpoint A - VEC (SEG B C).midpoint C := by rw [vec_sub_vec]
      _ = VEC B (SEG B C).midpoint - VEC (SEG B C).midpoint C := by rw [h₂]
      _ = 0 := by
        rw [Seg.vec_midpt_eq (seg := SEG B C)]
        simp
  intro hh
  rcases hh with hh | hh
  · rw [hh]
  rw [hh, dist_comm, ← Seg.length_eq_dist, ← Seg.length_eq_dist]
  symm
  apply dist_target_eq_dist_source_of_midpt (seg := (SEG B C))

theorem midpoint_dist_gt_iff_liesout {A B C : P} [hne : PtNe B C] (h : A LiesOn (LIN B C)) : dist A (SEG B C).midpoint > dist B (SEG B C).midpoint ↔ ¬ (A LiesOn (SEG B C)) := by
  apply Iff.not_right
  push_neg
  apply Iff.trans le_iff_lt_or_eq
  constructor
  · intro heq
    rcases heq with heq | heq
    · have : A LiesInt (SEG B C) := (midpoint_dist_lt_iff_liesint h).mp heq
      exact this.1
    rcases (midpoint_dist_eq_iff_eq_endpts h).mp heq with heq | heq
    · rw [heq]
      apply Seg.source_lies_on
    rw [heq]
    apply Seg.target_lies_on
  intro hh
  by_cases hh' : A LiesInt (SEG B C)
  · left
    exact (midpoint_dist_lt_iff_liesint h).mpr hh'
  right
  apply (midpoint_dist_eq_iff_eq_endpts h).mpr
  contrapose! hh'
  exact ⟨hh, hh'.1, hh'.2⟩

theorem liesint_segnd_iff_lieson_ray_reverse {A B C : P} [hne₁ : PtNe B C] [hne₂ : PtNe A B] (h : A LiesOn (LIN B C)) : A LiesInt (SEG B C) ↔ C LiesOn (RAY A B).reverse := sorry

theorem not_lies_on_segnd_iff_lieson_ray {A B C : P} [hne₁ : PtNe B C] [hne₂ : PtNe A B] (h : A LiesOn (LIN B C)) : ¬ (A LiesOn (SEG B C)) ↔ C LiesOn (RAY A B) := sorry

--Guan Nailin
theorem ne_vertex_of_lies_int_seg_nd {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (A ≠ seg_nd.source) ∧ (A ≠ seg_nd.target) := by sorry
theorem eq_toDir_of_source_to_pt_lies_int {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd seg_nd.source A (ne_vertex_of_lies_int_seg_nd h).1).toDir = seg_nd.toDir := by sorry
theorem eq_toDirLine_of_source_to_pt_lies_int {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd seg_nd.source A (ne_vertex_of_lies_int_seg_nd h).1).toDirLine = seg_nd.toDirLine := by sorry
theorem eq_toDir_of_pt_lies_int_to_target {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd A seg_nd.target (ne_vertex_of_lies_int_seg_nd h).2.symm).toDir = seg_nd.toDir := by sorry
theorem eq_toDirLine_of_pt_lies_int_to_target {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd A seg_nd.target (ne_vertex_of_lies_int_seg_nd h).2.symm).toDirLine = seg_nd.toDirLine := by sorry


end EuclidGeom
