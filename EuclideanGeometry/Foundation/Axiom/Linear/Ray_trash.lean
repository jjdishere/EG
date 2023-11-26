import EuclideanGeometry.Foundation.Axiom.Linear.Ray

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem Seg_nd.not_lies_int_extn_and_rev_extn_of_lies_on {A : P} {seg_nd : Seg_nd P} (lieson : A LiesOn seg_nd.1) : ¬ A LiesInt seg_nd.extension ∧ ¬ A LiesInt seg_nd.reverse.extension := by
  constructor
  apply Ray.not_lies_int_of_lies_on_rev
  simp only [extn_eq_rev_toray_rev, Ray.rev_rev_eq_self]
  apply lies_on_toray_of_lies_on
  apply Seg.lies_on_rev_iff_lies_on.mpr
  exact lieson
  apply Ray.not_lies_int_of_lies_on_rev
  simp only [extn_eq_rev_toray_rev, Ray.rev_rev_eq_self, Seg_nd.rev_rev_eq_self]
  exact lies_on_toray_of_lies_on lieson


theorem Seg.length_eq_dist {A B : P} : (SEG A B).length = dist A B := by
  unfold Seg.length
  rw [dist_comm, NormedAddTorsor.dist_eq_norm']
  rfl


theorem Seg.midpt_target_length_eq {A B : P} : 2 * dist (SEG A B).midpoint B = dist A B := by
  unfold Seg.midpoint
  rw [NormedAddTorsor.dist_eq_norm', NormedAddTorsor.dist_eq_norm']
  simp
  rw [vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev, ← sub_eq_add_neg, AbsoluteValue.map_neg Complex.abs _, ← Vec.mk_pt_pt]
  calc
    _ = 2 * Complex.abs ((2⁻¹ - 1) * (VEC A B)) := by rw [sub_mul, one_mul]
    _ = 2 * Complex.abs ((- 2⁻¹) * (VEC A B)) := by norm_num
    _ = 2 * Complex.abs (2⁻¹ * (VEC A B)) := by rw [← neg_mul_eq_neg_mul, AbsoluteValue.map_neg Complex.abs _]
    _ = Complex.abs (VEC A B) := by
      rw [AbsoluteValue.map_mul Complex.abs, ← mul_assoc]
      norm_num

theorem Seg_nd.midpt_ne_target {A B : P} (h : B ≠ A) : (SEG A B).midpoint ≠ B := by
  apply dist_pos.mp
  have : 2 * dist (SEG A B).midpoint B > 0 := by
    rw [Seg.midpt_target_length_eq]
    apply dist_pos.mpr h.symm
  linarith

end EuclidGeom
