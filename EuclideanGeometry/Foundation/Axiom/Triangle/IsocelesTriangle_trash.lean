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
  haveI C_ne_B: PtNe C B := ⟨(ne_of_not_collinear not_collinear_ABC).1⟩
  have D_int_BC : D LiesInt (SEG B C) := by
    apply SegND.midpt_lies_int (seg_nd := (SEG_nd B C))
  have D_on_line_BC : D LiesOn (LIN B C) := by
    apply SegND.lies_on_toLine_of_lie_on (s := SEG_nd B C)
    show D LiesOn (SEG B C); exact D_int_BC.1
  have : D ≠ A := by
    by_contra h; absurd not_collinear_ABC
    simp only [h.symm]; apply Seg.collinear_of_lies_on D_int_BC.1
    apply Seg.source_lies_on; apply Seg.target_lies_on
  haveI D_ne_A: PtNe D A := ⟨this⟩
  have DB_eq_DC : (SEG D B).length = (SEG D C).length := by
    calc
    _= (SEG B D).length := by apply length_of_rev_eq_length'
    _= _ := by apply Seg.dist_target_eq_dist_source_of_midpt (seg := (SEG B C))
  apply perp_foot_unique'
  exact D_on_line_BC
  show LIN A D ⟂ LIN B C
  sorry
end EuclidGeom
