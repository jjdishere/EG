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

end EuclidGeom
