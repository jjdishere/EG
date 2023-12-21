import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem acongr_of_AAS_variant (tr_nd₁ tr_nd₂ : TriangleND P) (a₁ : tr_nd₁.angle₁.dvalue = - tr_nd₂.angle₁.dvalue) (a₂ : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value) (e₃ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length) : tr_nd₁ ≅ₐ tr_nd₂ := by sorry


end EuclidGeom
