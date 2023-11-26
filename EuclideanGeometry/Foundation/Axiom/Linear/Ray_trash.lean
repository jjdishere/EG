import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]
variable {P : Type _} [EuclideanPlane P] (seg_nd : Seg_nd P)

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

def Ray.extpoint (l : Ray P) (r : ℝ) : P := r * l.toDir.toVec +ᵥ l.source
def Ray.dist_of_extpoint (l : Ray P) (A : P) (h : A LiesOn l) : ℝ := Vec.norm (VEC l.source A)

theorem lies_on_of_extpoint (l : Ray P) {A : P} {r : ℝ} (h : A = Ray.extpoint l r) : A LiesOn l := sorry
theorem dist_eq_of_extpoint (l : Ray P) {A : P} {r : ℝ} (h : A = Ray.extpoint l r) : Ray.dist_of_extpoint l A (lies_on_of_extpoint l h) = r := sorry
theorem extpoint_of_dist (l : Ray P) {A : P} {h : A LiesOn l} : Ray.extpoint l (Ray.dist_of_extpoint l A h) = A := sorry
theorem seg_length_eq_dist_of_extpoint (l : Ray P) {A : P} {r : ℝ} (h : A = Ray.extpoint l r): (SEG l.source A).length = r := sorry
-- 暂时只是想实现这一功能，能够写“延长AB到C使得AB=BC”这种话，内容可能还不是很好

theorem Seg_nd_midpoint_not_eq_source : seg_nd.1.midpoint ≠ seg_nd.source := by sorry

theorem Seg_nd_midpoint_not_eq_target : seg_nd.1.midpoint ≠ seg_nd.target := by sorry

end EuclidGeom
