import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace cong_trash


theorem acongr_of_AAS (tr_nd₁ tr_nd₂ : TriangleND P) (a₁ : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value) (a₂ : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value) (e₃ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length) : tr_nd₁ ≅ₐ tr_nd₂ := by sorry

end cong_trash

end EuclidGeom
