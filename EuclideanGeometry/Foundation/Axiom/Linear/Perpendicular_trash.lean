import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Position.Angle

noncomputable section
namespace EuclidGeom

open Line

variable {P : Type*} [EuclideanPlane P]

theorem perp_of_angle_dvalue_eq_pi_div_two {A B C : P} [h1 : PtNe B A] [h2 : PtNe C A] (h : (ANG B A C).dvalue = ↑(π / 2)) : LIN B A ⟂ LIN C A := by
  sorry
end EuclidGeom
