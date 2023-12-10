import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] (seg_nd : SegND P)

theorem SegND.not_lies_int_extn_and_rev_extn_of_lies_on {A : P} {seg_nd : SegND P} (lieson : A LiesOn seg_nd.1) : ¬ A LiesInt seg_nd.extension ∧ ¬ A LiesInt seg_nd.reverse.extension := by
  constructor
  apply Ray.not_lies_int_of_lies_on_rev
  simp only [extn_eq_rev_toRay_rev, Ray.rev_rev_eq_self]
  apply lies_on_toRay_of_lies_on
  apply Seg.lies_on_rev_iff_lies_on.mpr
  exact lieson
  apply Ray.not_lies_int_of_lies_on_rev
  simp only [extn_eq_rev_toRay_rev, Ray.rev_rev_eq_self, SegND.rev_rev_eq_self]
  exact lies_on_toRay_of_lies_on lieson

-- theorem same_extn_of_source_lies_int {seg_nd : Seg_nd P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd A seg_nd.target ) = seg_nd.extension

-- Define the extpoint of a ray to be a point lies on the ray.toLine which has given distence to the ray.source
def Ray.extpoint (l : Ray P) (r : ℝ) : P := r • l.toDir.unitVec +ᵥ l.source

theorem lies_on_of_nonneg_extpoint {l : Ray P} {A : P} {r : ℝ} {hnonneg : 0 ≤ r} (h : A = Ray.extpoint l r) : A LiesOn l := sorry
theorem lies_int_of_pos_extpoint {l : Ray P} {A : P} {r : ℝ} {hpos : 0 < r} (h : A = Ray.extpoint l r) : A LiesInt l := sorry
theorem seg_length_eq_dist_of_extpoint (l : Ray P) {A : P} {r : ℝ} {hnonneg : 0 ≤ r} (h : A = Ray.extpoint l r): (SEG l.source A).length = r := sorry
-- 暂时只是想实现这一功能，能够写“延长AB到C使得AB=BC”这种话，内容可能还不是很好

theorem length_eq_length_add_length_of_lies_on_extension (seg_nd : SegND P) {A : P} (h : A LiesOn seg_nd.extension) : (SEG seg_nd.source A).length = seg_nd.1.length + (SEG seg_nd.target A).length := sorry

theorem Seg.length_eq_dist {A B : P} : (SEG A B).length = dist A B := by
  unfold Seg.length
  rw [dist_comm, NormedAddTorsor.dist_eq_norm']
  rfl


theorem Seg.midpt_target_length_eq {A B : P} : 2 * dist (SEG A B).midpoint B = dist A B := by
  unfold Seg.midpoint
  rw [NormedAddTorsor.dist_eq_norm', NormedAddTorsor.dist_eq_norm',
    ← show ‖(2 : ℝ)‖ = 2 by norm_num, ← norm_smul, vadd_vsub_assoc, smul_add, smul_smul]
  norm_num
  rw [two_smul, ← add_assoc, ← Vec.mkPtPt, vec_add_vec, vec_same_eq_zero, zero_add]

theorem Seg_nd.midpt_ne_target {A B : P} (h : B ≠ A) : (SEG A B).midpoint ≠ B := by
  apply dist_pos.mp
  have : 2 * dist (SEG A B).midpoint B > 0 := by
    rw [Seg.midpt_target_length_eq]
    apply dist_pos.mpr h.symm
  linarith

theorem Seg_nd_midpoint_not_eq_source : seg_nd.1.midpoint ≠ seg_nd.source := by sorry

theorem Seg_nd_midpoint_not_eq_target : seg_nd.1.midpoint ≠ seg_nd.target := by sorry

theorem Ray.pt_lies_int_pt_pt (A B : P) (h : B ≠ A) : B LiesInt (RAY _ _ h) := by sorry

theorem Ray.pt_lies_on_pt_pt (A B : P) (h : B ≠ A) : B LiesOn (RAY _ _ h) := by sorry

end EuclidGeom
