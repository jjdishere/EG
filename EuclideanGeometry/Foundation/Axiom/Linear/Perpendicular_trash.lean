import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Position.Angle

noncomputable section
namespace EuclidGeom

open Line

variable {P : Type _} [EuclideanPlane P]

theorem segnd_perp_line_of_line_perp_line {A B : P} (B_ne_A : B ≠ A) {l : Line P} (h : (SEG_nd A B B_ne_A) ⟂ l) : (LIN A B B_ne_A) ⟂ l := by sorry
theorem perp_foot_unique' {A B : P} {l : DirLine P} (h : A LiesOn l) (hne : B ≠ A) (hp : (DLIN B A hne.symm) ⟂ l) : perp_foot B l = A := sorry


theorem not_collinear_with_perp_foot_of_ne_perp_foot (A B C : P) (l : Line P) (B_on_l : B LiesOn l) (A_not_on_l : ¬ A LiesOn l) (C_is_perp_foot : C = (perp_foot A l)) (B_ne_C : B ≠ C): ¬ collinear C B A := sorry

theorem perp_foot_unique {A B : P} {l : DirLine P} (h : A LiesOn l) [_hne : PtNe A B] (hp : (DLIN B A) ⟂ l) : perp_foot B l = A := sorry

theorem eq_dist_eq_perp_foot {A B : P} {l : DirLine P} (h : A LiesOn l) (heq : dist B A = dist_pt_line B l) : A = perp_foot B l := sorry

end EuclidGeom
