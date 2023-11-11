import EuclideanGeometry.Foundation.Axiom.Position.Angle

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem sin_pos_iff_angle_pos (A : Angle P) : 0 < Real.sin A.value ↔ (0 < A.value ∧ A.value < π) := sorry

end EuclidGeom
