import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular

noncomputable section
namespace EuclidGeom

open Line

variable {P : Type _} [EuclideanPlane P]
section Perpendicular_constructions

theorem pt_to_perp_foot_perp_line {A : P} {l : Line P} (h : ¬ (A LiesOn l)) : (LIN A (perp_foot A l) ((not_congr (perp_foot_eq_self_iff_lies_on A l)).mpr h)) ⟂ l := by sorry

end Perpendicular_constructions

variable {P : Type _} [EuclideanPlane P]

theorem dist_pt_line_shortest (A B : P) {l : Line P} (h : B LiesOn l) : dist A B ≥ dist_pt_line A l := sorry

end EuclidGeom
