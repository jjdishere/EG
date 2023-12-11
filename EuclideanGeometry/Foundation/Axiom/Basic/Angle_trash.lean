import EuclideanGeometry.Foundation.Axiom.Basic.Angle

noncomputable section
namespace EuclidGeom

theorem two_smul_value_eq_iff_dvalue_eq (x y : AngValue) : 2 • x = 2 • y ↔ (x : AngDValue) = (y : AngDValue) := sorry

/-
theorem dir_eq_of_angvalue_eq {d₁ : Dir} {d₂ : Dir} : d₁ = d₂ ↔ d₁.toAngValue = d₂.toAngValue := sorry
-/

theorem theta_sub_half_theta_eq_half_theta {θ : AngValue} : θ - θ.half = θ.half := sorry

theorem neg_half_pi_le_half_angvalue {θ : AngValue} : -π < θ.toReal/2 := sorry

theorem half_angvalue_le_half_pi {θ : AngValue} : θ.toReal/2 ≤ π := sorry

theorem real_eq_toangvalue_toreal_real_iff_neg_pi_le_real_le_pi {r : ℝ} : r = (∠[r]).toReal ↔ (-π < r) ∧ (r ≤ π) := sorry

theorem half_angvalue_is_pos_if_angvalue_is_pos {α : AngValue} {β : AngValue} (g : α.toReal = β.toReal/2) (h : β.IsPos) : α.IsPos := sorry

theorem half_angvalue_is_neg_if_angvalue_is_neg {α : AngValue} {β : AngValue} (g : α.toReal = β.toReal/2) (h : β.IsNeg) : α.IsNeg := sorry

theorem toreal_eq_half_pi_of_eq_half_pi_toangvalue {θ : AngValue} (g : θ.toReal = π/2) : θ = ∠[π/2] := sorry

end EuclidGeom
