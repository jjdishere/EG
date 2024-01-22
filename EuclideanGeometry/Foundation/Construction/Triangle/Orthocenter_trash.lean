import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Construction.Triangle.Orthocenter
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace TriangleND
theorem perp_foot_lies_int_edge_of_acute_acute₁ (tr_nd : TriangleND P) (acu₂ : Angle.IsAcuteAngle tr_nd.angle₂) (acu₃ : Angle.IsAcuteAngle tr_nd.angle₂) : (perp_foot tr_nd.point₁ tr_nd.edge_nd₁.toLine) LiesInt tr_nd.edge_nd₁ := sorry
end TriangleND
end EuclidGeom
