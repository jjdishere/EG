import EuclideanGeometry.Foundation.Axiom.Basic.Angle

namespace EuclidGeom

theorem dir_eq_of_angvalue_eq {d₁ : Dir} {d₂ : Dir} : d₁ = d₂ ↔ d₁.toAngValue = d₂.toAngValue := sorry

theorem theta_sub_half_theta_eq_half_theta (θ : AngValue) : θ - (2⁻¹ * θ.toReal).toAngValue = (2⁻¹ * θ.toReal).toAngValue := sorry

theorem neg_half_pi_le_half_angvalue (θ : AngValue) : -π < 2⁻¹ * θ.toReal := sorry

theorem half_angvalue_le_half_pi (θ : AngValue) : 2⁻¹ * θ.toReal ≤ π := sorry

theorem real_eq_toangvalue_toreal_real_iff_neg_pi_le_real_le_pi (θ : ℝ) : θ = θ.toAngValue.toReal ↔ (-π < θ) ∧ (θ ≤ π) := sorry

end EuclidGeom
