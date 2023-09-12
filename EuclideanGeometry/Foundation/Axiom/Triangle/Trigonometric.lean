import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Circle.Basic
-- should we exclude circle in this file? this file is supposed to be used to establish congruent.

noncomputable section
namespace EuclidGeom
variable {P : Type _} [EuclideanPlane P]

namespace Triangle

-- Cosine rule : for a nontrivial triangle ABC, AB^2 = AC^2 + BC^2 + AC * BC * cos ∠ BAC.

theorem cosine_rule (tr_nd : Triangle_nd P) : tr_nd.1.edge₃.length ^ 2 = tr_nd.1.edge₁.length ^ 2 + tr_nd.1.edge₂.length ^ 2 + tr_nd.1.edge₁.length * tr_nd.1.edge₂.length * Real.cos tr_nd.angle₁ := sorry


-- Sine rule (but only for counterclockwise triangle here, or we need some absolute values)
-- Should we reformulate it without circle?
theorem side_eq_cradius_times_sine_angle (tr_nd : Triangle_nd P) (cclock : tr_nd.is_cclock) : tr_nd.1.edge₁.length = 2 * (tr_nd.toCir).radius * Real.sin (tr_nd.angle₁) ∧ tr_nd.1.edge₂.length = 2 * (tr_nd.toCir).radius * Real.sin (tr_nd.angle₂) ∧ tr_nd.1.edge₃.length = 2 * (tr_nd.toCir).radius * Real.sin (tr_nd.angle₃):= sorry

end Triangle

end EuclidGeom