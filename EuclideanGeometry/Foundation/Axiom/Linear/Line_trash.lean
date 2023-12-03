import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem same_dist_eq_or_eq_neg {A B C : P} (hne : B ≠ A) (h : C LiesOn (LIN A B hne)) (heq : dist A C = dist A B) : (C = B) ∨ (VEC A C = VEC B A) := by
  have : LIN A B hne = (RAY A B hne).toLine := rfl
  rw [this] at h
  rcases Ray.lies_on_toline_iff_lies_on_or_lies_on_rev.mp h with h | h
  · left; apply (eq_iff_vec_eq_zero _ _).mpr
    have : VEC A C = (dist A C) • (RAY A B hne).2.1 := Ray.lieson_eq_dist h
    calc
      _ = VEC A C - VEC A B := by rw [vec_sub_vec]
      _ = (dist A B) • (RAY A B hne).2.1 - VEC A B := by rw [this, heq]
      _ = (dist A B) • (RAY A B hne).2.1 - (VEC_nd A B hne).norm • (VEC_nd A B hne).toDir.1 := by simp; rfl
      _ = (dist A B) • (RAY A B hne).2.1 - (SEG A B).length • (RAY A B hne).2.1 := rfl
      _ = 0 := by rw [← sub_smul, Seg.length_eq_dist, sub_self, zero_smul]
  right
  calc
    _ = (dist A C) • (RAY A B hne).reverse.2.1 := Ray.lieson_eq_dist h
    _ = (dist A C) • (- (VEC_nd A B hne).toDir.1) := rfl
    _ = (dist A B) • (- (VEC_nd A B hne).toDir.1) := by rw [heq]
    _ = - ((SEG A B).length • (VEC_nd A B hne).toDir.1) := by rw [smul_neg, Seg.length_eq_dist]
    _ = - ((VEC_nd A B hne).norm • (VEC_nd A B hne).toDir.1) := rfl
    _ = - (VEC_nd A B hne).1 := by simp
    _ = - VEC A B := rfl
    _ = VEC B A := by rw [neg_vec]

theorem distinct_pts_same_dist_vec_eq {A B C : P} (hne₁ : B ≠ A) (hne₂ : C ≠ B) (h : C LiesOn (LIN A B hne₁)) (heq : dist A C = dist A B) : VEC B A = VEC A C := by
  rcases same_dist_eq_or_eq_neg hne₁ h heq with hh | hh
  · exfalso; tauto
  exact hh.symm

end EuclidGeom
