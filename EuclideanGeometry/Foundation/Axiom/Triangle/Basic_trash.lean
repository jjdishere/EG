import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_ex

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

structure Triangle_nd.IsAcute (tri_nd : Triangle_nd P) : Prop where
  angle₁ : - π / 2 < tri_nd.angle₁.value ∧ tri_nd.angle₁.value < π / 2
  angle₂ : - π / 2 < tri_nd.angle₂.value ∧ tri_nd.angle₂.value < π / 2
  angle₃ : - π / 2 < tri_nd.angle₃.value ∧ tri_nd.angle₃.value < π / 2

end EuclidGeom
