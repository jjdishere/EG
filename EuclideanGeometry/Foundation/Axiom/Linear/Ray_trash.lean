import EuclideanGeometry.Foundation.Axiom.Linear.Ray

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

theorem Seg_nd_midpoint_not_eq_source : seg_nd.1.midpoint ≠ seg_nd.source := by sorry

theorem Seg_nd_midpoint_not_eq_target : seg_nd.1.midpoint ≠ seg_nd.target := by sorry

theorem Ray.pt_lies_int_pt_pt (A B : P) (h : B ≠ A) : B LiesInt (RAY _ _ h) := by sorry

theorem Ray.pt_lies_on_pt_pt (A B : P) (h : B ≠ A) : B LiesOn (RAY _ _ h) := by sorry

end EuclidGeom
