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

--Guan Nailin
theorem ne_vertex_of_lies_int_seg_nd {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (A ≠ seg_nd.source) ∧ (A ≠ seg_nd.target) := by sorry
theorem eq_toDir_of_source_to_pt_lies_int {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd seg_nd.source A (ne_vertex_of_lies_int_seg_nd h).1).toDir = seg_nd.toDir := by sorry
theorem eq_toDirLine_of_source_to_pt_lies_int {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd seg_nd.source A (ne_vertex_of_lies_int_seg_nd h).1).toDirLine = seg_nd.toDirLine := by sorry
theorem eq_toDir_of_pt_lies_int_to_target {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd A seg_nd.target (ne_vertex_of_lies_int_seg_nd h).2.symm).toDir = seg_nd.toDir := by sorry
theorem eq_toDirLine_of_pt_lies_int_to_target {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd A seg_nd.target (ne_vertex_of_lies_int_seg_nd h).2.symm).toDirLine = seg_nd.toDirLine := by sorry

namespace DirLine
section linear_order
-- linear order and ne
theorem ne_iff_ne_as_line_elem {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) : (A ≠ B) ↔ ((⟨A, ha⟩ : Dl.carrier.Elem) ≠ ⟨B, hb⟩) := by sorry
-- linear order and LiesInt
theorem lies_int_of_lt_and_lt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_lt_b : (⟨A, ha⟩ : Dl.carrier.Elem) < ⟨B, hb⟩) (b_lt_c : (⟨B, hb⟩ : Dl.carrier.Elem) < ⟨C, hc⟩) : B LiesInt (SEG A C) := by sorry
theorem lies_int_of_gt_and_gt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_gt_b : (⟨A, ha⟩ : Dl.carrier.Elem) > ⟨B, hb⟩) (b_gt_c : (⟨B, hb⟩ : Dl.carrier.Elem) > ⟨C, hc⟩) : B LiesInt (SEG A C) := by sorry
theorem lt_and_lt_or_gt_and_gt_of_lies_int {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesInt (SEG A C)) : (((⟨A, ha⟩ : Dl.carrier.Elem) < ⟨B, hb⟩) ∧ ((⟨B, hb⟩ : Dl.carrier.Elem) < ⟨C, hc⟩)) ∨ (((⟨A, ha⟩ : Dl.carrier.Elem) > ⟨B, hb⟩) ∧ ((⟨B, hb⟩ : Dl.carrier.Elem) > ⟨C, hc⟩)) := by sorry
-- linear order and LiesOn
theorem lies_on_of_le_and_le {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_le_b : (⟨A, ha⟩ : Dl.carrier.Elem) ≤ ⟨B, hb⟩) (b_le_c : (⟨B, hb⟩ : Dl.carrier.Elem) ≤ ⟨C, hc⟩) : B LiesOn (SEG A C) := by sorry
theorem lies_on_of_ge_and_ge {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_ge_b : (⟨A, ha⟩ : Dl.carrier.Elem) ≥ ⟨B, hb⟩) (b_ge_c : (⟨B, hb⟩ : Dl.carrier.Elem) ≥ ⟨C, hc⟩) : B LiesOn (SEG A C) := by sorry
theorem le_and_le_or_ge_and_ge_of_lies_on {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesOn (SEG A C)) : (((⟨A, ha⟩ : Dl.carrier.Elem) ≤ ⟨B, hb⟩) ∧ ((⟨B, hb⟩ : Dl.carrier.Elem) ≤ ⟨C, hc⟩)) ∨ (((⟨A, ha⟩ : Dl.carrier.Elem) ≥ ⟨B, hb⟩) ∧ ((⟨B, hb⟩ : Dl.carrier.Elem) ≥ ⟨C, hc⟩)) := by sorry
-- linear order and toDir
theorem eq_toDir_of_lt {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (a_lt_b : (⟨A, ha⟩ : Dl.carrier.Elem) < ⟨B, hb⟩) : (RAY A B ((ne_iff_ne_as_line_elem ha hb).mpr (ne_of_lt a_lt_b)).symm).toDir = Dl.toDir := by sorry
theorem neg_toDir_of_gt {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (a_gt_b : (⟨A, ha⟩ : Dl.carrier.Elem) > ⟨B, hb⟩) : (RAY A B ((ne_iff_ne_as_line_elem ha hb).mpr (ne_of_gt a_gt_b)).symm).toDir = - Dl.toDir := by sorry
end linear_order
end DirLine

end EuclidGeom
