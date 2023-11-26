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

theorem pt_lies_int_pt_pt_iff_pt_lies_int_pt_pt {A B C : P} (b_ne_a : B ≠ A) (c_ne_a : C ≠ A) : B LiesInt RAY A C c_ne_a ↔ C LiesInt RAY A B b_ne_a := by sorry

end EuclidGeom
