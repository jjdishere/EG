import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular

noncomputable section
namespace EuclidGeom

open Line

variable {P : Type _} [EuclideanPlane P]

theorem segnd_perp_line_of_line_perp_line {A B : P} (B_ne_A : B ≠ A) {l : Line P} (h : (SEG_nd A B B_ne_A) ⟂ l) : (LIN A B B_ne_A) ⟂ l := by sorry

end EuclidGeom
