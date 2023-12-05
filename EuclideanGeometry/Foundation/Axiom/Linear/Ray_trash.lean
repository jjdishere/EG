import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] (seg_nd : SegND P)

-- theorem same_extn_of_source_lies_int {seg_nd : Seg_nd P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd A seg_nd.target ) = seg_nd.extension

-- Define the extpoint of a ray to be a point lies on the ray.toLine which has given distence to the ray.source
def Ray.extpoint (l : Ray P) (r : ℝ) : P := r • l.toDir.unitVec +ᵥ l.source

theorem lies_on_of_nonneg_extpoint {l : Ray P} {A : P} {r : ℝ} {hnonneg : 0 ≤ r} (h : A = Ray.extpoint l r) : A LiesOn l := sorry
theorem lies_int_of_pos_extpoint {l : Ray P} {A : P} {r : ℝ} {hpos : 0 < r} (h : A = Ray.extpoint l r) : A LiesInt l := sorry
theorem seg_length_eq_dist_of_extpoint (l : Ray P) {A : P} {r : ℝ} {hnonneg : 0 ≤ r} (h : A = Ray.extpoint l r): (SEG l.source A).length = r := sorry
-- 暂时只是想实现这一功能，能够写“延长AB到C使得AB=BC”这种话，内容可能还不是很好

theorem length_eq_length_add_length_of_lies_on_extension (seg_nd : SegND P) {A : P} (h : A LiesOn seg_nd.extension) : (SEG seg_nd.source A).length = seg_nd.1.length + (SEG seg_nd.target A).length := sorry

end EuclidGeom
