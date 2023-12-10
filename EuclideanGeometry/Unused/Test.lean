import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

example (x y : ℝ) : ((x + y) : Real.Angle) = (x:Real.Angle) + y := by simp only
example (x y : ℝ) :  (x:Real.Angle) + y = ((x + y) : Real.Angle) := by simp only
example (x: ℝ) : (((2 • x): Real) : Real.Angle) = 2 • (x : Real.Angle) := by
  simp? -- Try this: simp only [nsmul_eq_mul, Nat.cast_ofNat]
  sorry

@[simp]
theorem two_smul_coe (x: ℝ) : (((2 • x): Real) : Real.Angle) = 2 • (x : Real.Angle) := AddCircle.coe_nsmul (2 * Real.pi) (n := 2) (x := x)

example (x: ℝ) : (((2 • x): Real) : Real.Angle) = 2 • (x : Real.Angle) := by
  simp? -- Try this: simp only [nsmul_eq_mul, Nat.cast_ofNat]
  sorry


@[simp↓]
theorem nsmul_coe (n : ℕ) (x : ℝ) : (((n • x): Real) : Real.Angle) = n • (x : Real.Angle) := AddCircle.coe_nsmul (2 * Real.pi)

example (x: ℝ) : (((2 • x): Real) : Real.Angle) = 2 • (x : Real.Angle) := by
  simp? -- Try this: simp only [nsmul_eq_mul, Nat.cast_ofNat]


/-
#synth Coe ℝ AngValue
#synth AddGroup AngValue
#synth SMul ℤ AngValue
-/
