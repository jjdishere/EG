import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] 

-- compatibility with coersion to Proj
section compatibility_coersion_to_Proj

theorem Ray.toProj_eq_toLine_toProj (ray : Ray P) : ray.toProj = ray.toLine.toProj := by
  symm
  apply ray_toLine_toProj_eq_ray_toProj ray

theorem Seg_nd.toProj_eq_toLine_toProj (seg_nd : Seg_nd P) : seg_nd.toProj = seg_nd.toLine.toProj := by
  set ray := seg_nd.toRay with ray_def
  have h₁ : seg_nd.toProj = ray.toProj := by
    rw [ray_def]
    apply Seg_nd.toProj_eq_toRay_toProj
  have h₂ : seg_nd.toLine.toProj = ray.toLine.toProj := by
    rw [ray_def, Seg_nd.toLine_eq_toRay_toLine seg_nd]
  rw [h₁, h₂, Ray.toProj_eq_toLine_toProj ray]

theorem lies_on_iff_eq_toProj {A B : P} {l : Line P} (h : B ≠ A) (hA : A LiesOn l) : B LiesOn l ↔ (SEG_nd A B h).toProj = l.toProj := Seg_nd_toProj_eq_toProj_iff_lies_on hA h


end compatibility_coersion_to_Proj

section reverse
-- A point lies on a line associated to a ray if and only if it lies on the ray or the reverse of the ray

theorem Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev (a : P) (l : Ray P) : (a LiesOn l.toLine) ↔ (a LiesOn l) ∨ (a LiesOn l.reverse) := sorry

theorem Ray.toLine_eq_rev_toLine (ray : Ray P) : ray.toLine = ray.reverse.toLine := sorry

theorem Seg_nd.toLine_eq_rev_toLine (seg_nd : Ray P) : seg_nd.toLine = seg_nd.reverse.toLine := sorry

end reverse

section extension

theorem toLine_eq_extn_toLine (seg_nd : Seg_nd P) : seg_nd.toLine = seg_nd.extension.toLine := sorry

theorem lies_on_extn_or_rev_extn_iff_lies_on_toLine_of_not_lies_on {A : P} (seg_nd : Seg_nd P) (h : ¬ A LiesInt seg_nd.1) : A LiesOn seg_nd.toLine ↔ (A LiesOn seg_nd.extension) ∨ (A LiesOn seg_nd.reverse.extension) := sorry

end extension

end EuclidGeom