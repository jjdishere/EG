import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem ne_source_of_lies_int_seg_nd (A B C : P) (h1 : B ≠ A) (h2 : C LiesInt (SEG_nd A B h1)) : C ≠ A := by sorry

theorem ne_source_of_lies_int_seg (A B C : P) (h2 : C LiesInt (SEG A B)) : C ≠ A := by sorry

theorem eq_todir_of_lies_int_seg_nd (A B C : P) (h1 : B ≠ A) (h2 : C LiesInt (SEG A B)) : (SEG_nd A B h1).toDir = (SEG_nd A C (ne_source_of_lies_int_seg_nd A B C h1 h2)).toDir := by sorry

theorem lies_int_seg_nd_of_lies_int_seg (A B C : P) (h1 : B ≠ A) (h2 : C LiesInt (SEG A B)) : C LiesInt (SEG_nd A B h1) := by sorry

theorem lies_on_seg_nd_of_lies_on_seg (A B C : P) (h1 : B ≠ A) (h2 : C LiesOn (SEG A B)) : C LiesOn (SEG_nd A B h1) := by sorry

namespace Ray

theorem snd_pt_lies_int_mk_pt_pt {A B : P} (h : B ≠ A) : B LiesInt (RAY A B h) := by sorry

end Ray
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

end EuclidGeom
