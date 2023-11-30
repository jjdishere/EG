import EuclideanGeometry.Foundation.Axiom.Basic.Angle

namespace EuclidGeom

theorem dir_eq_of_angvalue_eq {d₁ : Dir} {d₂ : Dir} : d₁ = d₂ ↔ d₁.toAngValue = d₂.toAngValue := sorry

theorem theta_sub_half_theta_eq_half_theta (θ : AngValue) : θ - (2⁻¹ * θ.toReal).toAngValue = (2⁻¹ * θ.toReal).toAngValue := sorry

theorem neg_half_pi_le_half_angvalue (θ : AngValue) : -2⁻¹ * π < 2⁻¹ * θ.toReal := sorry

theorem half_angvalue_le_half_pi (θ : AngValue) : 2⁻¹ * θ.toReal ≤ 2⁻¹ * π := sorry

end EuclidGeom
