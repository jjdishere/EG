import EuclideanGeometry.Foundation.Axiom.Triangle
import EuclideanGeometry.Foundation.Axiom.Circle

noncomputable section
namespace EuclidGeom
variable {P : Type _} [EuclideanPlane P]

namespace Triangle

-- Cosine rule : for a nontrivial triangle ABC, AB^2 = AC^2 + BC^2 + AC * BC * cos ∠ BAC.

theorem cosine_rule (tr : Triangle P) (nontriv : tr.is_nontriv) : tr.edge₃.length ^ 2 = tr.edge₁.length ^ 2 + tr.edge₂.length ^ 2 + tr.edge₁.length * tr.edge₂.length * Real.cos (tr.angle₁ nontriv) := sorry


-- Sine rule
theorem side_eq_cradius_times_sine_angle (tr : Triangle P) (nontriv : tr.is_nontriv) : tr.edge₁.length = (tr.toCir_of_nontriv nontriv) Real.sin (tr.angle₁ nontriv):= sorry



end Triangle

end EuclidGeom