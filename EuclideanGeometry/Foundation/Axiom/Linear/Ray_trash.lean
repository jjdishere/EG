import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] (seg_nd : SegND P)

-- theorem same_extn_of_source_lies_int {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd A seg_nd.target ) = seg_nd.extension

/-SegND_eq_midpoint_iff_in_seg_and_dist_target_eq_dist_source should be replaced by the following three
  midpoint → liesint seg_nd
  midpoint → dist source = dist target
  lieson ∧ dist source = dist target → midpoint

  by the way in_seg shoud be renamed by current naming system
-/

-- 以前的length_pos_iff_nd不是很好用，现在加一个PtNe的版本,但是PtNe是instance，以后还需要修改
/-- A segment has positive length if and only if its source is not equal to its target. -/
theorem length_pos_iff_PtNe {seg : Seg P} : 0 < seg.length ↔ (PtNe seg.source seg.target) := sorry

end EuclidGeom
