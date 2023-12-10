import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

example (x y : ℝ) : ((x + y) : AngValue) = (x:AngValue) + y := by simp only
example (x y : ℝ) :  (x:AngValue) + y = ((x + y) : AngValue) := by simp only
example (x: ℝ) : (((2 • x): Real) : AngValue) = 2 • (x : AngValue) := by
  simp? -- Try this: simp only [nsmul_eq_mul, Nat.cast_ofNat]
  sorry

@[simp]
theorem two_smul_coe (x: ℝ) : (((2 • x): Real) : AngValue) = 2 • (x : AngValue) := AddCircle.coe_nsmul (2 * Real.pi) (n := 2) (x := x)

example (x: ℝ) : (((2 • x): Real) : AngValue) = 2 • (x : AngValue) := by
  simp? -- Try this: simp only [nsmul_eq_mul, Nat.cast_ofNat]
  sorry


@[simp↓]
theorem nsmul_coe (n : ℕ) (x : ℝ) : (((n • x): Real) : AngValue) = n • (x : AngValue) := AddCircle.coe_nsmul (2 * Real.pi)

example (x: ℝ) : (((2 • x): Real) : AngValue) = 2 • (x : AngValue) := by
  simp? -- Try this: simp only [nsmul_eq_mul, Nat.cast_ofNat]


/-
#synth Coe ℝ AngValue
#synth AddGroup AngValue
#synth SMul ℤ AngValue
-/
