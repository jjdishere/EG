import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] (seg_nd : SegND P)

-- theorem same_extn_of_source_lies_int {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd A seg_nd.target ) = seg_nd.extension

-- Define the extpoint of a ray to be a point lies on the ray.toLine which has given distence to the ray.source
def Ray.extpoint (l : Ray P) (r : ℝ) : P := sorry -- r * l.toDir.toVec +ᵥ l.source

theorem lies_on_of_nonneg_extpoint (l : Ray P) {A : P} {r : ℝ} {hnonneg : 0 ≤ r} (h : A = Ray.extpoint l r) : A LiesOn l := sorry
theorem lies_int_of_pos_extpoint (l : Ray P) {A : P} {r : ℝ} {hpos : 0 < r} (h : A = Ray.extpoint l r) : A LiesInt l := sorry
theorem seg_length_eq_dist_of_extpoint (l : Ray P) {A : P} {r : ℝ} {hnonneg : 0 ≤ r} (h : A = Ray.extpoint l r): (SEG l.source A).length = r := sorry
-- 暂时只是想实现这一功能，能够写“延长AB到C使得AB=BC”这种话，内容可能还不是很好

theorem length_eq_length_add_length_of_lies_on_extension (seg_nd : SegND P) {A : P} (h : A LiesOn seg_nd.extension) : (SEG seg_nd.source A).length = seg_nd.1.length + (SEG seg_nd.target A).length := sorry

theorem Ray.lieson_eq_dist {A : P} {r : Ray P} (h : A LiesOn r) : VEC r.1 A = (dist r.1 A) • r.2.unitVec := by
  by_cases heq : A = r.1
  · rw [← heq, vec_same_eq_zero, dist_self, zero_smul]
  push_neg at heq
  have h : A LiesInt r := ⟨h, heq⟩
  have h₁ : RAY r.1 A h.2 = r := Ray.pt_pt_eq_ray h
  calc
    _ = (VEC_nd r.1 A h.2).1 := rfl
    _ = ‖VEC_nd r.1 A h.2‖ • (VEC_nd r.1 A h.2).toDir.unitVec := by simp
    _ = (dist r.1 A) • (VEC_nd r.1 A h.2).toDir.unitVec := by
      rw [dist_comm, NormedAddTorsor.dist_eq_norm']
      rfl
    _ = (dist r.1 A) • (RAY r.1 A h.2).2.unitVec := rfl
    _ = (dist r.1 A) • r.2.unitVec := by rw [h₁]

/-SegND_eq_midpoint_iff_in_seg_and_dist_target_eq_dist_source should be replaced by the following three
  midpoint → liesint seg_nd
  midpoint → dist source = dist target
  lieson ∧ dist source = dist target → midpoint

  by the way in_seg shoud be renamed by current naming system
-/


theorem lies_int_of_midpoint_of_seg_nd {seg_nd : SegND P} : seg_nd.midpoint LiesInt seg_nd := by sorry

theorem dist_source_eq_dist_target_of_midpoint {seg : Seg P} : (SEG seg.midpoint seg.source).length = (SEG seg.midpoint seg.target).length := by sorry

theorem eq_midpoint_of_lies_on_and_dist_source_eq_dist_target {seg : Seg P} {M : P} {h : M LiesOn seg} {heq : (SEG M seg.source).length = (SEG M seg.target).length} : M = seg.midpoint := by sorry
theorem midpt_of_rev_eq_midpt (A B : P) : (SEG A B).midpoint = (SEG B A).midpoint := by sorry

theorem lies_int_toray_of_lies_int_ext_of_seg_nd (A B C : P) (h1 : B ≠ A) (h : C LiesInt ((SEG_nd A B h1).extension)) : C LiesInt (SEG_nd A B h1).toRay := by sorry

end EuclidGeom
