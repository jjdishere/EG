import EuclideanGeometry.Foundation.Axiom.Triangle.IsocelesTriangle
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular_trash

noncomputable section
namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

lemma isoceles_tri_pts_ne {tri : Triangle P} (h : tri.IsIsoceles) (hne : tri.point₂ ≠ tri.point₃) : (tri.point₁ ≠ tri.point₂) ∧ (tri.point₁ ≠ tri.point₃) := sorry

theorem is_isoceles_tri_ang_eq_ang_of_tri {tri : Triangle P} (h : tri.IsIsoceles) (hne : tri.point₂ ≠ tri.point₃) : ∠ tri.point₃ tri.point₂ tri.point₁ hne.symm (isoceles_tri_pts_ne h hne).1 = ∠ tri.point₁ tri.point₃ tri.point₂ (isoceles_tri_pts_ne h hne).2 hne := by sorry

theorem ang_acute_of_is_isoceles {A B C : P} (not_colinear_ABC : ¬ Collinear A B C) (isoceles_ABC : (▵ A B C).IsIsoceles) : Angle.IsAcu (ANG C B A (ne_of_not_collinear not_colinear_ABC).1 (ne_of_not_collinear not_colinear_ABC).2.2.symm) := by sorry

theorem ang_acute_of_is_isoceles_variant {A B C : P} (not_collinear_ABC : ¬ Collinear A B C) (isoceles_ABC : (▵ A B C).IsIsoceles) : Angle.IsAcu (ANG A C B (ne_of_not_collinear not_collinear_ABC).2.1 (ne_of_not_collinear not_collinear_ABC).1.symm) := by sorry

theorem perp_foot_eq_midpt_of_is_isoceles {A B C : P} (not_collinear_ABC : ¬ Collinear A B C) (isoceles_ABC : (▵ A B C).IsIsoceles) : perp_foot A (LIN B C (ne_of_not_collinear not_collinear_ABC).1) = (SEG B C).midpoint := by
  let D := (SEG B C).midpoint
  have : D ≠ A := by sorry
  haveI h1: PtNe D A := ⟨this⟩
  haveI h2: PtNe C B := ⟨(ne_of_not_collinear not_collinear_ABC).1⟩
  have D_int_BC : D LiesInt (SEG B C) := by sorry
  have D_on_line_BC : D LiesOn (LIN B C) := by sorry
  have DB_eq_DC : (SEG D B).length = (SEG D C).length := by sorry
  apply perp_foot_unique'
  exact D_on_line_BC
  show LIN A D ⟂ LIN B C
  sorry
end EuclidGeom
