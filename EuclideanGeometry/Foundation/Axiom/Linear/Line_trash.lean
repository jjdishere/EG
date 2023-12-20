import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem same_dist_eq_or_eq_neg {A B C : P} (hne : B ≠ A) (h : C LiesOn (LIN A B hne)) (heq : dist A C = dist A B) : (C = B) ∨ (VEC A C = VEC B A) := by
  have : LIN A B hne = (RAY A B hne).toLine := rfl
  rw [this] at h
  rcases Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mp h with h | h
  · left; apply (eq_iff_vec_eq_zero _ _).mpr
    have : VEC A C = (dist A C) • (RAY A B hne).2.unitVec := Ray.lieson_eq_dist h
    calc
      _ = VEC A C - VEC A B := by rw [vec_sub_vec]
      _ = (dist A B) • (RAY A B hne).2.unitVec - VEC A B := by rw [this, heq]
      _ = (dist A B) • (RAY A B hne).2.unitVec - ‖VEC_nd A B hne‖ • (VEC_nd A B hne).toDir.unitVec := by simp
      _ = (dist A B) • (RAY A B hne).2.unitVec - ‖VEC_nd A B hne‖ • (RAY A B hne).2.unitVec := rfl
      _ = 0 := by
        rw [← sub_smul, dist_comm, NormedAddTorsor.dist_eq_norm']
        simp
        apply sub_eq_zero.mpr
        rfl

  right
  calc
    _ = (dist A C) • (RAY A B hne).reverse.2.unitVec := Ray.lieson_eq_dist h
    _ = (dist A C) • (- (VEC_nd A B hne).toDir.unitVec) := by simp
    _ = (dist A B) • (- (VEC_nd A B hne).toDir.unitVec) := by rw [heq]
    _ = - (‖VEC_nd A B hne‖ • (VEC_nd A B hne).toDir.unitVec) := by
      rw [smul_neg, dist_comm, NormedAddTorsor.dist_eq_norm']
      rfl
    _ = - (VEC_nd A B hne).1 := by simp
    _ = - VEC A B := rfl
    _ = VEC B A := by rw [neg_vec]

theorem distinct_pts_same_dist_vec_eq {A B C : P} (hne₁ : B ≠ A) (hne₂ : C ≠ B) (h : C LiesOn (LIN A B hne₁)) (heq : dist A C = dist A B) : VEC B A = VEC A C := by
  rcases same_dist_eq_or_eq_neg hne₁ h heq with hh | hh
  · exfalso; tauto
  exact hh.symm

--Guan Nailin
theorem ne_vertex_of_lies_int_seg_nd {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (A ≠ seg_nd.source) ∧ (A ≠ seg_nd.target) := by sorry
theorem eq_toDir_of_source_to_pt_lies_int {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd seg_nd.source A (ne_vertex_of_lies_int_seg_nd h).1).toDir = seg_nd.toDir := by sorry
theorem eq_toDirLine_of_source_to_pt_lies_int {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd seg_nd.source A (ne_vertex_of_lies_int_seg_nd h).1).toDirLine = seg_nd.toDirLine := by sorry
theorem eq_toDir_of_pt_lies_int_to_target {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd A seg_nd.target (ne_vertex_of_lies_int_seg_nd h).2.symm).toDir = seg_nd.toDir := by sorry
theorem eq_toDirLine_of_pt_lies_int_to_target {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd A seg_nd.target (ne_vertex_of_lies_int_seg_nd h).2.symm).toDirLine = seg_nd.toDirLine := by sorry
end EuclidGeom
