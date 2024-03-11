import EuclideanGeometry.Foundation.Axiom.Triangle.IsocelesTriangle
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular_trash

noncomputable section
namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

lemma isoceles_tri_pts_ne {tri : Triangle P} (h : tri.IsIsoceles) (hne : tri.point₂ ≠ tri.point₃) : (tri.point₁ ≠ tri.point₂) ∧ (tri.point₁ ≠ tri.point₃) := sorry

theorem is_isoceles_tri_ang_eq_ang_of_tri {tri : Triangle P} (h : tri.IsIsoceles) (hne : tri.point₂ ≠ tri.point₃) : ∠ tri.point₃ tri.point₂ tri.point₁ hne.symm (isoceles_tri_pts_ne h hne).1 = ∠ tri.point₁ tri.point₃ tri.point₂ (isoceles_tri_pts_ne h hne).2 hne := by sorry

theorem ang_acute_of_is_isoceles {A B C : P} (h : ¬ Collinear A B C) (isoceles_ABC : (▵ A B C).IsIsoceles) : Angle.IsAcu (ANG C B A (ne_of_not_collinear h).1 (ne_of_not_collinear h).2.2.symm) := by sorry

theorem ang_acute_of_is_isoceles_variant {A B C : P} (h : ¬ Collinear A B C) (isoceles_ABC : (▵ A B C).IsIsoceles) : Angle.IsAcu (ANG A C B (ne_of_not_collinear h).2.1 (ne_of_not_collinear h).1.symm) := by sorry

theorem midpt_eq_perp_foot_of_isIsoceles {A B C : P} [PtNe B C] (h : (▵ A B C).IsIsoceles) : (SEG B C).midpoint = perp_foot A (LIN B C) := sorry

theorem perp_foot_eq_midpt_of_is_isoceles {A B C : P} (not_collinear_ABC : ¬ Collinear A B C) (isoceles_ABC : (▵ A B C).IsIsoceles) : perp_foot A (LIN B C (ne_of_not_collinear not_collinear_ABC).1) = (SEG B C).midpoint := by
  sorry

end EuclidGeom
