import EuclideanGeometry.Foundation.Axiom.Linear.Ray

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

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

  end EuclidGeom
