import EuclideanGeometry.Foundation.Axiom.Basic.Angle.FromMathlib
import Mathlib.Data.Int.Parity

/-!
# Theorems that should exist in Mathlib

Maybe we can create some PRs to mathlib in the future.
-/

open Real Classical
attribute [ext] Complex.ext

/-!
### More theorems about trigonometric functions in Mathlib

These theorems about trigonometric functions mostly exist in Mathlib in the version of `Real.sin`,
`Real.cos` or `Real.tan` but not in the version of `Real.Angle.sin`, `Real.Angle.cos` or
`Real.Angle.tan`.

In this section, we will translate these theorems into the version of `EuclidGeom.AngValue.sin`,
`EuclidGeom.AngValue.cos` or `EuclidGeom.AngValue.tan`.
-/

namespace EuclidGeom

namespace AngValue

variable {θ : AngValue}

section Mathlib.Data.Complex.Exponential
/-
Translate useful theorems in `Mathlib.Data.Complex.Exponential` to `AngValue.sin` or `AngValue.cos`, such as the sum and difference formulas, product-to-sum formulas and so on.
For example, the following theorems should be moved here.

theorem Real.sin_sub (x : ℝ) (y : ℝ) :
Real.sin (x - y) = Real.sin x * Real.cos y - Real.cos x * Real.sin y

theorem Real.cos_sub (x : ℝ) (y : ℝ) :
Real.cos (x - y) = Real.cos x * Real.cos y + Real.sin x * Real.sin y

-- The product-to-sum formulas. The version of `Real.sin` and `Real.cos` may need to be proven first.
cos ⁡ θ * cos ⁡ φ = (cos ⁡ ( θ + φ ) + cos ⁡ ( θ − φ )) / 2

sin ⁡ θ * sin ⁡ φ = (cos ⁡ ( θ − φ ) − cos ⁡ ( θ + φ )) / 2

sin ⁡ θ * cos ⁡ φ = (sin ⁡ ( θ + φ ) + sin ⁡ ( θ − φ )) / 2

cos ⁡ θ * sin ⁡ φ = (sin ⁡ ( θ + φ ) − sin ⁡ ( θ − φ )) / 2

theorem Real.tan_mul_cos {x : ℝ} (hx : Real.cos x ≠ 0) :
Real.tan x * Real.cos x = Real.sin x

@[simp]
theorem Real.tan_neg (x : ℝ) :
Real.tan (-x) = -Real.tan x

@[simp]
theorem Real.sin_sq_add_cos_sq (x : ℝ) :
Real.sin x ^ 2 + Real.cos x ^ 2 = 1

theorem Real.sin_sq_le_one (x : ℝ) :
Real.sin x ^ 2 ≤ 1

theorem Real.cos_sq_le_one (x : ℝ) :
Real.cos x ^ 2 ≤ 1

theorem Real.abs_sin_le_one (x : ℝ) :
|Real.sin x| ≤ 1

theorem Real.abs_cos_le_one (x : ℝ) :
|Real.cos x| ≤ 1

theorem Real.sin_le_one (x : ℝ) :
Real.sin x ≤ 1

0 ≤ 1 - sin θ

theorem Real.cos_le_one (x : ℝ) :
Real.cos x ≤ 1

0 ≤ 1 - cos θ

theorem Real.neg_one_le_sin (x : ℝ) :
-1 ≤ Real.sin x

0 ≤ 1 + cos θ

theorem Real.neg_one_le_cos (x : ℝ) :
-1 ≤ Real.cos x

0 ≤ 1 + sin θ

theorem Real.cos_two_mul (x : ℝ) :
Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1

theorem Real.cos_two_mul' (x : ℝ) :
Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2

theorem Real.sin_two_mul (x : ℝ) :
Real.sin (2 * x) = 2 * (Real.sin x * Real.cos x)

theorem Real.cos_sq (x : ℝ) :
Real.cos x ^ 2 = 1 / 2 + Real.cos (2 * x) / 2

theorem Real.cos_sq' (x : ℝ) :
Real.cos x ^ 2 = 1 - Real.sin x ^ 2

theorem Real.sin_sq (x : ℝ) :
Real.sin x ^ 2 = 1 - Real.cos x ^ 2

theorem Real.sin_sq_eq_half_sub (x : ℝ) :
Real.sin x ^ 2 = 1 / 2 - Real.cos (2 * x) / 2

theorem Real.abs_sin_eq_sqrt_one_sub_cos_sq (x : ℝ) :
|Real.sin x| = Real.sqrt (1 - Real.cos x ^ 2)

theorem Real.abs_cos_eq_sqrt_one_sub_sin_sq (x : ℝ) :
|Real.cos x| = Real.sqrt (1 - Real.sin x ^ 2)

theorem Real.inv_one_add_tan_sq {x : ℝ} (hx : Real.cos x ≠ 0) :
(1 + Real.tan x ^ 2)⁻¹ = Real.cos x ^ 2

theorem Real.tan_sq_div_one_add_tan_sq {x : ℝ} (hx : Real.cos x ≠ 0) :
Real.tan x ^ 2 / (1 + Real.tan x ^ 2) = Real.sin x ^ 2

theorem Real.inv_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < Real.cos x) :
(Real.sqrt (1 + Real.tan x ^ 2))⁻¹ = Real.cos x

theorem Real.tan_div_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < Real.cos x) :
Real.tan x / Real.sqrt (1 + Real.tan x ^ 2) = Real.sin x

theorem Real.cos_three_mul (x : ℝ) :
Real.cos (3 * x) = 4 * Real.cos x ^ 3 - 3 * Real.cos x

theorem Real.sin_three_mul (x : ℝ) :
Real.sin (3 * x) = 3 * Real.sin x - 4 * Real.sin x ^ 3

-/

end Mathlib.Data.Complex.Exponential

section Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
/-
Translate useful theorems in `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` to `AngValue.sin` or `AngValue.cos`. Maybe the inequalities here should correspond to the inequalities about `toReal`.
For example, the following theorems may need to be moved here.

@[simp]
theorem Real.cos_pi_div_two :
Real.cos (π / 2) = 0

@[simp]
theorem Real.sin_pi :
Real.sin π = 0

@[simp]
theorem Real.cos_pi :
Real.cos π = -1

@[simp]
theorem Real.sin_pi_div_two :
Real.sin (π / 2) = 1


-- The following 8 theorems have already been translated. Please refer to the existing content below.
theorem Real.sin_pos_of_pos_of_lt_pi {x : ℝ} (h0x : 0 < x) (hxp : x < π) :
0 < Real.sin x

theorem Real.sin_nonneg_of_nonneg_of_le_pi {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π) :
0 ≤ Real.sin x

theorem Real.sin_neg_of_neg_of_neg_pi_lt {x : ℝ} (hx0 : x < 0) (hpx : -π < x) :
Real.sin x < 0

theorem Real.sin_nonpos_of_nonnpos_of_neg_pi_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -π ≤ x) :
Real.sin x ≤ 0

theorem Real.cos_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (- π / 2) (π / 2)) :
0 < Real.cos x

theorem Real.cos_nonneg_of_neg_pi_div_two_le_of_le {x : ℝ} (hl : - π / 2 ≤ x) (hu : x ≤ π / 2) :
0 ≤ Real.cos x

theorem Real.cos_neg_of_pi_div_two_lt_of_lt {x : ℝ} (hx₁ : π / 2 < x) (hx₂ : x < π + π / 2) :
Real.cos x < 0

theorem Real.cos_nonpos_of_pi_div_two_le_of_le {x : ℝ} (hx₁ : π / 2 ≤ x) (hx₂ : x ≤ π + π / 2) :
Real.cos x ≤ 0


theorem Real.sin_eq_sqrt_one_sub_cos_sq {x : ℝ} (hl : 0 ≤ x) (hu : x ≤ π) :
Real.sin x = Real.sqrt (1 - Real.cos x ^ 2)

theorem Real.cos_eq_sqrt_one_sub_sin_sq {x : ℝ} (hl : - π / 2 ≤ x) (hu : x ≤ π / 2) :
Real.cos x = Real.sqrt (1 - Real.sin x ^ 2)

theorem Real.sin_eq_zero_iff_of_lt_of_lt {x : ℝ} (hx₁ : -π < x) (hx₂ : x < π) :
Real.sin x = 0 ↔ x = 0

theorem Real.sin_eq_zero_iff_cos_eq {x : ℝ} :
Real.sin x = 0 ↔ Real.cos x = 1 ∨ Real.cos x = -1

theorem Real.cos_eq_one_iff_of_lt_of_lt {x : ℝ} (hx₁ : -(2 * π) < x) (hx₂ : x < 2 * π) :
Real.cos x = 1 ↔ x = 0

theorem Real.cos_lt_cos_of_nonneg_of_le_pi_div_two {x : ℝ} {y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π / 2) (hxy : x < y) :
Real.cos y < Real.cos x

theorem Real.cos_lt_cos_of_nonneg_of_le_pi {x : ℝ} {y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π) (hxy : x < y) :
Real.cos y < Real.cos x

theorem Real.cos_le_cos_of_nonneg_of_le_pi {x : ℝ} {y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π) (hxy : x ≤ y) :
Real.cos y ≤ Real.cos x

theorem Real.sin_lt_sin_of_lt_of_le_pi_div_two {x : ℝ} {y : ℝ} (hx₁ : - π / 2 ≤ x) (hy₂ : y ≤ π / 2) (hxy : x < y) :
Real.sin x < Real.sin y

theorem Real.sin_le_sin_of_le_of_le_pi_div_two {x : ℝ} {y : ℝ} (hx₁ : - π / 2 ≤ x) (hy₂ : y ≤ π / 2) (hxy : x ≤ y) :
Real.sin x ≤ Real.sin y

theorem Real.surjOn_sin :
Set.SurjOn Real.sin (Set.Icc (- π / 2) (π / 2)) (Set.Icc (-1) 1)

theorem Real.surjOn_cos :
Set.SurjOn Real.cos (Set.Icc 0 π) (Set.Icc (-1) 1)

theorem Real.range_cos_infinite :
Set.Infinite (Set.range Real.cos)

theorem Real.range_sin_infinite :
Set.Infinite (Set.range Real.sin)

@[simp]
theorem Real.cos_pi_div_four :
Real.cos (π / 4) = Real.sqrt 2 / 2

@[simp]
theorem Real.sin_pi_div_four :
Real.sin (π / 4) = Real.sqrt 2 / 2

@[simp]
theorem Real.cos_pi_div_eight :
Real.cos (π / 8) = Real.sqrt (2 + Real.sqrt 2) / 2

@[simp]
theorem Real.sin_pi_div_eight :
Real.sin (π / 8) = Real.sqrt (2 - Real.sqrt 2) / 2

@[simp]
theorem Real.cos_pi_div_sixteen :
Real.cos (π / 16) = Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) / 2

@[simp]
theorem Real.sin_pi_div_sixteen :
Real.sin (π / 16) = Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) / 2

@[simp]
theorem Real.cos_pi_div_thirty_two :
Real.cos (π / 32) = Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) / 2

@[simp]
theorem Real.sin_pi_div_thirty_two :
Real.sin (π / 32) = Real.sqrt (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) / 2

/-- The cosine of π / 3 is 1 / 2. -/
@[simp]
theorem Real.cos_pi_div_three :
Real.cos (π / 3) = 1 / 2

/-- The cosine of π / 6 is √3 / 2. -/
@[simp]
theorem Real.cos_pi_div_six :
Real.cos (π / 6) = Real.sqrt 3 / 2

/-- The square of the cosine of π / 6 is 3 / 4 (this is sometimes more convenient than the result for cosine itself). -/
theorem Real.sq_cos_pi_div_six :
Real.cos (π / 6) ^ 2 = 3 / 4

/-- The sine of π / 6 is 1 / 2. -/
@[simp]
theorem Real.sin_pi_div_six :
Real.sin (π / 6) = 1 / 2

/-- The square of the sine of π / 3 is 3 / 4 (this is sometimes more convenient than the result for cosine itself). -/
theorem Real.sq_sin_pi_div_three :
Real.sin (π / 3) ^ 2 = 3 / 4

/-- The sine of π / 3 is √3 / 2. -/
@[simp]
theorem Real.sin_pi_div_three :
Real.sin (π / 3) = Real.sqrt 3 / 2

@[simp]
theorem Real.tan_pi_div_four :
Real.tan (π / 4) = 1

@[simp]
theorem Real.tan_pi_div_two :
Real.tan (π / 2) = 0

theorem Real.tan_pos_of_pos_of_lt_pi_div_two {x : ℝ} (h0x : 0 < x) (hxp : x < π / 2) :
0 < Real.tan x

theorem Real.tan_nonneg_of_nonneg_of_le_pi_div_two {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π / 2) :
0 ≤ Real.tan x

theorem Real.tan_neg_of_neg_of_pi_div_two_lt {x : ℝ} (hx0 : x < 0) (hpx : - π / 2 < x) :
Real.tan x < 0

theorem Real.tan_nonpos_of_nonpos_of_neg_pi_div_two_le {x : ℝ} (hx0 : x ≤ 0) (hpx : - π / 2 ≤ x) :
Real.tan x ≤ 0

theorem Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two {x : ℝ} {y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y < π / 2) (hxy : x < y) :
Real.tan x < Real.tan y

theorem Real.tan_lt_tan_of_lt_of_lt_pi_div_two {x : ℝ} {y : ℝ} (hx₁ : - π / 2 < x) (hy₂ : y < π / 2) (hxy : x < y) :
Real.tan x < Real.tan y

theorem Real.injOn_tan :
Set.InjOn Real.tan (Set.Ioo (- π / 2) (π / 2))

theorem Real.tan_inj_of_lt_of_lt_pi_div_two {x : ℝ} {y : ℝ} (hx₁ : - π / 2 < x) (hx₂ : x < π / 2) (hy₁ : - π / 2 < y) (hy₂ : y < π / 2) (hxy : Real.tan x = Real.tan y) :
x = y

@[simp]
theorem Real.tan_pi :
Real.tan π = 0

theorem Real.tan_pi_sub (x : ℝ) :
Real.tan (π - x) = - Real.tan x

theorem Real.tan_pi_div_two_sub (x : ℝ) :
Real.tan (π / 2 - x) = (Real.tan x)⁻¹

-/

@[simp]
theorem sin_pi_sub : sin (π - θ) = sin θ := by
  rw [← θ.coe_toReal]
  exact (θ.toReal).sin_pi_sub

@[simp]
theorem cos_pi_sub : cos (π - θ) = - cos θ := by
  rw [← θ.coe_toReal]
  exact (θ.toReal).cos_pi_sub

theorem zero_lt_sin_of_zero_lt_toReal_lt_pi (h : 0 < θ.toReal) (hp : θ.toReal < π) : 0 < sin θ :=
  θ.sin_toReal.trans_gt (sin_pos_of_pos_of_lt_pi h hp)

theorem zero_le_zero_of_zero_le_toReal (h : 0 ≤ θ.toReal) : 0 ≤ sin θ :=
  θ.sin_toReal.trans_ge (sin_nonneg_of_nonneg_of_le_pi h θ.toReal_le_pi)

theorem sin_lt_zero_of_toReal_lt_zero (h : θ.toReal < 0) : sin θ < 0 :=
  θ.sin_toReal.symm.trans_lt (sin_neg_of_neg_of_neg_pi_lt h θ.neg_pi_lt_toReal)

theorem sin_le_zero_of_toReal_le_zero (h : θ.toReal ≤ 0) : sin θ ≤ 0 :=
  θ.sin_toReal.symm.trans_le (sin_nonpos_of_nonnpos_of_neg_pi_le h (le_of_lt θ.neg_pi_lt_toReal))

theorem zero_lt_cos_of_neg_pi_div_two_lt_of_lt_pi_div_two (hn : - π / 2 < θ.toReal) (h : θ.toReal < π / 2) : 0 < cos θ :=
  θ.cos_toReal.trans_gt (cos_pos_of_mem_Ioo ⟨(neg_div' 2 π).trans_lt hn, h⟩)

theorem zero_le_cos_of_neg_pi_div_two_le_of_le_pi_div_two (hn : - π / 2 ≤ θ.toReal) (h : θ.toReal ≤ π / 2) : 0 ≤ cos θ :=
  θ.cos_toReal.trans_ge (cos_nonneg_of_neg_pi_div_two_le_of_le ((neg_div' 2 π).trans_le hn) h)

theorem cos_lt_zero_of_pi_div_two_lt_toReal (h :  π / 2 < θ.toReal) : cos θ < 0 :=
  θ.cos_toReal.symm.trans_lt (cos_neg_of_pi_div_two_lt_of_lt h (by linarith [θ.toReal_le_pi]))

theorem cos_lt_zero_of_toReal_lt_neg_pi_div_two (h : θ.toReal < - π / 2) : cos θ < 0 :=
  θ.cos_toReal.symm.trans_lt <| θ.toReal.cos_add_two_pi.symm.trans_lt <|
    cos_neg_of_pi_div_two_lt_of_lt (by linarith [θ.neg_pi_lt_toReal]) (by linarith)

theorem cos_le_zero_of_pi_div_two_le_toReal (h :  π / 2 ≤ θ.toReal) : cos θ ≤ 0 :=
  θ.cos_toReal.symm.trans_le (cos_nonpos_of_pi_div_two_le_of_le h (by linarith [θ.toReal_le_pi]))

theorem cos_le_zero_of_toReal_le_neg_pi_div_two (h : θ.toReal ≤ - π / 2) : cos θ ≤ 0 :=
  θ.cos_toReal.symm.trans_le <| θ.toReal.cos_add_two_pi.symm.trans_le <|
    cos_nonpos_of_pi_div_two_le_of_le (by linarith [θ.neg_pi_lt_toReal]) (by linarith)

theorem zero_lt_cos_iff : 0 < cos θ ↔ - π / 2 < θ.toReal ∧ θ.toReal < π / 2 := by
  refine' ⟨fun h ↦ _, fun h ↦ zero_lt_cos_of_neg_pi_div_two_lt_of_lt_pi_div_two h.1 h.2⟩
  by_contra hr
  rw [not_and_or, not_lt, not_lt] at hr
  exact Or.casesOn hr (fun hr ↦ not_le.mpr h (cos_le_zero_of_toReal_le_neg_pi_div_two hr))
    fun hr ↦ not_le.mpr h (cos_le_zero_of_pi_div_two_le_toReal hr)

theorem cos_lt_zero_iff : cos θ < 0 ↔ θ.toReal < - π / 2 ∨  π / 2 < θ.toReal := by
  refine' ⟨fun h ↦ _, fun h ↦ Or.casesOn h (fun h ↦ cos_lt_zero_of_toReal_lt_neg_pi_div_two h)
    fun h ↦ cos_lt_zero_of_pi_div_two_lt_toReal h⟩
  by_contra hr
  rw [not_or, not_lt, not_lt] at hr
  exact not_le.mpr h (zero_le_cos_of_neg_pi_div_two_le_of_le_pi_div_two hr.1 hr.2)

end Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

end AngValue

end EuclidGeom



/-!
### Compatibility among group, addtorsor and order
-/

section Mathlib.Algebra.Order.Group.Defs

/-- A circular ordered additive commutative group is an additive commutative group with
a circular order whose order is stable under addition and compatiable with negation. -/
class CircularOrderedAddCommGroup (G : Type*) extends AddCommGroup G, CircularOrder G where
  btw_add_left {a b c : G} (h : btw a b c) (g : G) : btw (g + a) (g + b) (g + c)
  btw_neg {a b c : G} (h : btw a b c) : btw (- a) (- c) (- b)

/-- A circular ordered commutative group is a commutative group with a circular order whose
order is stable under multiplication and compatiable with inverse. -/
@[to_additive]
class CircularOrderedCommGroup (G : Type*) extends CommGroup G, CircularOrder G where
  btw_mul_left {a b c : G} (h : btw a b c) (g : G) : btw (g * a) (g * b) (g * c)
  btw_inv {a b c : G} (h : btw a b c) : btw a⁻¹ c⁻¹ b⁻¹

variable {G : Type*} [CircularOrderedCommGroup G]

@[to_additive]
theorem btw_mul_left {a b c : G} (h : btw a b c) (g : G) : btw (g * a) (g * b) (g * c) :=
  CircularOrderedCommGroup.btw_mul_left h g

@[to_additive (attr := simp)]
theorem btw_mul_left_iff {g a b c : G} : btw (g * a) (g * b) (g * c) ↔ btw a b c :=
  ⟨fun h ↦ by
    rw [← inv_mul_cancel_left g a, ← inv_mul_cancel_left g b, ← inv_mul_cancel_left g c]
    exact btw_mul_left h g⁻¹, fun h ↦ btw_mul_left h g⟩

@[to_additive (attr := simp)]
theorem sbtw_mul_left_iff {g a b c : G} : sbtw (g * a) (g * b) (g * c) ↔ sbtw a b c :=  by
  simp only [sbtw_iff_not_btw, btw_mul_left_iff]

@[to_additive]
theorem sbtw_mul_left {a b c : G} (h : sbtw a b c) (g : G) : sbtw (g * a) (g * b) (g * c) :=
  sbtw_mul_left_iff.mpr h

@[to_additive (attr := simp)]
theorem btw_mul_right_iff {a b c g : G} : btw (a * g) (b * g) (c * g) ↔ btw a b c := by
  rw [mul_comm a g, mul_comm b g, mul_comm c g]
  exact btw_mul_left_iff

@[to_additive]
theorem btw_mul_right {a b c : G} (h : btw a b c) (g : G) : btw (a * g) (b * g) (c * g) :=
  btw_mul_right_iff.mpr h

@[to_additive (attr := simp)]
theorem sbtw_mul_right_iff {a b c g : G} : sbtw (a * g) (b * g) (c * g) ↔ sbtw a b c :=  by
  simp only [sbtw_iff_not_btw, btw_mul_right_iff]

@[to_additive]
theorem sbtw_mul_right {a b c : G} (h : sbtw a b c) (g : G) : sbtw (a * g) (b * g) (c * g) :=
  sbtw_mul_right_iff.mpr h

@[to_additive]
theorem btw_inv {a b c : G} (h : btw a b c) : btw a⁻¹ c⁻¹ b⁻¹ := CircularOrderedCommGroup.btw_inv h

@[to_additive (attr := simp)]
theorem btw_inv_iff {a b c : G} : btw a⁻¹ b⁻¹ c⁻¹ ↔ btw a c b :=
  ⟨fun h ↦ by
    rw [← inv_inv a, ← inv_inv b, ← inv_inv c]
    exact btw_inv h, btw_inv⟩

@[to_additive]
theorem btw_inv_iff' {a b c : G} : btw a⁻¹ b⁻¹ c⁻¹ ↔ btw c b a :=
  btw_inv_iff.trans btw_cyclic.symm

@[to_additive]
theorem btw_inv_iff'' {a b c : G} : btw a⁻¹ b⁻¹ c⁻¹ ↔ btw b a c :=
  btw_inv_iff.trans btw_cyclic

@[to_additive]
theorem btw_inv_iff_not_sbtw {a b c : G} : btw a⁻¹ b⁻¹ c⁻¹ ↔ ¬ sbtw a b c :=
  btw_inv_iff'.trans btw_iff_not_sbtw

@[to_additive]
theorem not_btw_inv_iff_sbtw {a b c : G} : ¬ btw a⁻¹ b⁻¹ c⁻¹ ↔ sbtw a b c :=
  btw_inv_iff_not_sbtw.not_left

@[to_additive]
theorem sbtw_inv_iff_not_btw {a b c : G} : sbtw a⁻¹ b⁻¹ c⁻¹ ↔ ¬ btw a b c :=
  sbtw_iff_not_btw.trans btw_inv_iff'.not

@[to_additive]
theorem not_sbtw_inv_iff_btw {a b c : G} : ¬ sbtw a⁻¹ b⁻¹ c⁻¹ ↔ btw a b c :=
  sbtw_inv_iff_not_btw.not_left

@[to_additive (attr := simp)]
theorem sbtw_inv_iff {a b c : G} : sbtw a⁻¹ b⁻¹ c⁻¹ ↔ sbtw a c b :=
  sbtw_inv_iff_not_btw.trans (sbtw_iff_not_btw.symm.trans sbtw_cyclic)

@[to_additive]
theorem sbtw_inv {a b c : G} (h : sbtw a b c) : sbtw a⁻¹ c⁻¹ b⁻¹ := sbtw_inv_iff.mpr h

@[to_additive]
theorem sbtw_inv_iff' {a b c : G} : sbtw a⁻¹ b⁻¹ c⁻¹ ↔ sbtw c b a :=
  sbtw_inv_iff.trans sbtw_cyclic.symm

@[to_additive]
theorem sbtw_inv_iff'' {a b c : G} : sbtw a⁻¹ b⁻¹ c⁻¹ ↔ sbtw b a c :=
  sbtw_inv_iff.trans sbtw_cyclic

@[to_additive]
theorem btw_div_left {a b c : G} (h : btw a b c) (g : G) : btw (g / a) (g / c) (g / b) := by
  simp only [div_eq_mul_inv]
  exact btw_mul_left (btw_inv h) g

@[to_additive (attr := simp)]
theorem btw_div_left_iff {g a b c : G} : btw (g / a) (g / b) (g / c) ↔ btw a c b :=
  ⟨fun h ↦ btw_inv_iff.mp <| by
    simp only [div_eq_mul_inv] at h
    exact btw_mul_left_iff.mp h, fun h ↦ btw_div_left h g⟩

@[to_additive]
theorem btw_div_left_iff' {g a b c : G} : btw (g / a) (g / b) (g / c) ↔ btw c b a :=
  btw_div_left_iff.trans btw_cyclic.symm

@[to_additive]
theorem btw_div_left_iff'' {g a b c : G} : btw (g / a) (g / b) (g / c) ↔ btw b a c :=
  btw_div_left_iff.trans btw_cyclic

@[to_additive]
theorem sbtw_div_left {a b c : G} (h : sbtw a b c) (g : G) : sbtw (g / a) (g / c) (g / b) := by
  simp only [div_eq_mul_inv]
  exact sbtw_mul_left (sbtw_inv h) g

@[to_additive (attr := simp)]
theorem sbtw_div_left_iff {a b c g : G} : sbtw (g / a) (g / b) (g / c) ↔ sbtw a c b :=
  ⟨fun h ↦ sbtw_inv_iff.mp <| by
    simp only [div_eq_mul_inv] at h
    exact sbtw_mul_left_iff.mp h, fun h ↦ sbtw_div_left h g⟩

@[to_additive]
theorem sbtw_div_left_iff' {g a b c : G} : sbtw (g / a) (g / b) (g / c) ↔ sbtw c b a :=
  sbtw_div_left_iff.trans sbtw_cyclic.symm

@[to_additive]
theorem sbtw_div_left_iff'' {g a b c : G} : sbtw (g / a) (g / b) (g / c) ↔ sbtw b a c :=
  sbtw_div_left_iff.trans sbtw_cyclic

@[to_additive]
theorem btw_div_left_iff_not_sbtw {g a b c : G} : btw (g / a) (g / b) (g / c) ↔ ¬ sbtw a b c :=
  btw_div_left_iff'.trans btw_iff_not_sbtw

@[to_additive]
theorem not_btw_div_left_iff_sbtw {g a b c : G} : ¬ btw (g / a) (g / b) (g / c) ↔ sbtw a b c :=
  btw_div_left_iff_not_sbtw.not_left

@[to_additive]
theorem sbtw_div_left_iff_not_btw {g a b c : G} : sbtw (g / a) (g / b) (g / c) ↔ ¬ btw a b c :=
  sbtw_div_left_iff'.trans sbtw_iff_not_btw

@[to_additive]
theorem not_sbtw_div_left_iff_btw {g a b c : G} : ¬ sbtw (g / a) (g / b) (g / c) ↔ btw a b c :=
  sbtw_div_left_iff_not_btw.not_left

@[to_additive]
theorem btw_div_right {a b c : G} (h : btw a b c) (g : G) : btw (a / g) (b / g) (c / g) := by
  simp only [div_eq_mul_inv]
  exact btw_mul_right h g⁻¹

@[to_additive (attr := simp)]
theorem btw_div_right_iff {a b c g : G} : btw (a / g) (b / g) (c / g) ↔ btw a b c :=
  ⟨fun h ↦ by
    rw [← div_mul_cancel' a g, ← div_mul_cancel' b g, ← div_mul_cancel' c g]
    exact btw_mul_right h g, fun h ↦ btw_div_right h g⟩

@[to_additive]
theorem sbtw_div_right {a b c : G} (h : sbtw a b c) (g : G) : sbtw (a / g) (b / g) (c / g) := by
  simp only [div_eq_mul_inv]
  exact sbtw_mul_right h g⁻¹

@[to_additive (attr := simp)]
theorem sbtw_div_right_iff {a b c g : G} : sbtw (a / g) (b / g) (c / g) ↔ sbtw a b c :=
  ⟨fun h ↦ by
    rw [← div_mul_cancel' a g, ← div_mul_cancel' b g, ← div_mul_cancel' c g]
    exact sbtw_mul_right h g, fun h ↦ sbtw_div_right h g⟩

namespace QuotientAddGroup

instance instCircularOrderedAddCommGroup (G : Type*) [LinearOrderedAddCommGroup G] [Archimedean G] {p : G} [Fact (0 < p)] : CircularOrderedAddCommGroup (G ⧸ AddSubgroup.zmultiples p) where
  btw_add_left := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩ h ⟨⟩
    apply btw_coe_iff'.mpr
    simpa only [add_sub_add_left_eq_sub] using h
  btw_neg := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩ h
    apply btw_coe_iff.mpr
    simp only [toIcoMod_neg, toIocMod_neg, neg_neg]
    exact sub_le_sub_left (btw_coe_iff.mp h) p

variable {G : Type*} [LinearOrderedAddCommGroup G] [Archimedean G] {p : G} [hp : Fact (0 < p)]

theorem sbtw_coe_iff' {a b c : G} : sbtw (a : G ⧸ AddSubgroup.zmultiples p) b c ↔ toIocMod hp.out 0 (a - c) < toIcoMod hp.out 0 (b - c) :=
  not_iff_not.mp (btw_iff_not_sbtw.symm.trans not_lt.symm)

theorem sbtw_coe_iff {a b c : G} : sbtw (a : G ⧸ AddSubgroup.zmultiples p) b c ↔ toIocMod hp.out c a < toIcoMod hp.out c b :=
  not_iff_not.mp (btw_iff_not_sbtw.symm.trans (btw_coe_iff.trans not_lt.symm))

end QuotientAddGroup

end Mathlib.Algebra.Order.Group.Defs



section Mathlib.GroupTheory.GroupAction

section PartialOrder

/-- A partial ordered additive group action is a additive group action on a partial
order which is stable under the additive group action. -/
class OrderedAddAction (G : outParam Type*) (P : Type*) [outParam (AddGroup G)] extends AddAction G P, PartialOrder P where
  vadd_left_le {a b : P} (h : a ≤ b) (g : G) : g +ᵥ a ≤ g +ᵥ b

/-- A partial ordered multiplicative group action is a multiplicative group action on a partial
order which is stable under the multiplicative group action. -/
@[to_additive]
class OrderedMulAction (G : outParam Type*) (P : Type*) [outParam (Group G)] extends MulAction G P, PartialOrder P where
  smul_left_le {a b : P} (h : a ≤ b) (g : G) : g • a ≤ g • b

variable {G : outParam Type*} {P : Type*} [outParam (Group G)] [OrderedMulAction G P]

@[to_additive]
theorem smul_left_le {a b : P} (h : a ≤ b) (g : G) : g • a ≤ g • b :=
  OrderedMulAction.smul_left_le h g

@[to_additive (attr := simp)]
theorem smul_left_le_iff {g : G} {a b : P} : g • a ≤ g • b ↔ a ≤ b := by
  refine' ⟨fun h ↦ _, fun h ↦ smul_left_le h g⟩
  have h := smul_left_le h g⁻¹
  simp only [inv_smul_smul] at h
  exact h

@[to_additive (attr := simp)]
theorem smul_left_lt_iff {g : G} {a b : P} : g • a < g • b ↔ a < b := by
  simp only [lt_iff_le_not_le, smul_left_le_iff]

@[to_additive]
theorem smul_left_lt {a b : P} (h : a < b) (g : G) : g • a < g • b := smul_left_lt_iff.mpr h

end PartialOrder

section LinearOrder

/-- A linearly ordered additive group action is an additive group action on a linearly order which
is stable under the additive group action. -/
class LinearOrderedAddAction (G : outParam Type*) (P : Type*) [outParam (AddGroup G)] extends
  OrderedAddAction G P, LinearOrder P

/-- A linearly ordered multiplicative group action is a multiplicative group action on a linearly
order which is stable under the multiplicative group action. -/
@[to_additive]
class LinearOrderedMulAction (G : outParam Type*) (P : Type*) [outParam (Group G)] extends
  OrderedMulAction G P, LinearOrder P

variable {G : outParam Type*} {P : Type*} [outParam (Group G)] [LinearOrderedMulAction G P]

@[to_additive]
theorem min_smul {a b : P} (g : G) : min (g • a) (g • b) = g • min a b := by
  simp only [min_def, smul_left_le_iff]
  if h : a ≤ b then simp only [h, ite_true]
  else simp only [h, ite_false]

@[to_additive]
theorem max_smul {a b : P} (g : G) : max (g • a) (g • b) = g • max a b := by
  simp only [max_def, smul_left_le_iff]
  if h : a ≤ b then simp only [h, ite_true]
  else simp only [h, ite_false]

end LinearOrder

section CircularOrder

/-- A circular ordered additive group action is an additive group action on a circular order which
is stable under the additive group action. -/
class CircularOrderedAddAction (G : outParam Type*) (P : Type*) [outParam (AddGroup G)] extends AddAction G P, CircularOrder P where
  btw_vadd_left {a b c : P} (h : btw a b c) (g : G) : btw (g +ᵥ a) (g +ᵥ b) (g +ᵥ c)

/-- A circular ordered multiplicative group action is a multiplicative group action on a circular
order which is stable under the multiplicative group action. -/
@[to_additive]
class CircularOrderedMulAction (G : outParam Type*) (P : Type*) [outParam (Group G)] extends MulAction G P, CircularOrder P where
  btw_smul_left {a b c : P} (h : btw a b c) (g : G) : btw (g • a) (g • b) (g • c)

variable {G : outParam Type*} {P : Type*} [outParam (Group G)] [CircularOrderedMulAction G P]

@[to_additive]
theorem btw_smul_left {a b c : P} (h : btw a b c) (g : G) : btw (g • a) (g • b) (g • c) :=
  CircularOrderedMulAction.btw_smul_left h g

@[to_additive (attr := simp)]
theorem btw_smul_left_iff {g : G} {a b c : P} : btw (g • a) (g • b) (g • c) ↔ btw a b c := by
  refine' ⟨fun h ↦ _, fun h ↦ btw_smul_left h g⟩
  have h := btw_smul_left h g⁻¹
  simp only [inv_smul_smul] at h
  exact h

@[to_additive (attr := simp)]
theorem sbtw_smul_left_iff {g : G} {a b c : P} : sbtw (g • a) (g • b) (g • c) ↔ sbtw a b c :=  by
  simp only [sbtw_iff_not_btw, btw_smul_left_iff]

@[to_additive]
theorem sbtw_smul_left {a b c : P} (h : sbtw a b c) (g : G) : sbtw (g • a) (g • b) (g • c) :=
  sbtw_smul_left_iff.mpr h

end CircularOrder

end Mathlib.GroupTheory.GroupAction



section Mathlib.Algebra.AddTorsor

section Class

section PartialOrder

/-- A partial ordered `AddTorsor` is an `AddTorsor` with partial orders on the group and
the type acted on, such that both orders are compatiable with the additive group action. -/
class OrderedAddTorsor (G : outParam Type*) (P : Type*) [outParam (OrderedAddCommGroup G)] extends OrderedAddAction G P, AddTorsor G P where
  vadd_right_le {f g : G} (h : f ≤ g) (a : P) : f +ᵥ a ≤ g +ᵥ a

variable {G : outParam Type*} {P : Type*} [outParam (OrderedAddCommGroup G)] [OrderedAddTorsor G P]

theorem vadd_right_le {f g : G} (h : f ≤ g) (a : P) : f +ᵥ a ≤ g +ᵥ a :=
  OrderedAddTorsor.vadd_right_le h a

theorem vadd_right_lt {f g : G} (h : f < g) (a : P) : f +ᵥ a < g +ᵥ a :=
  Ne.lt_of_le (fun eq ↦ h.ne (vadd_right_cancel a eq)) (vadd_right_le (le_of_lt h) a)

end PartialOrder

section LinearOrder

variable (G : outParam Type*) (P : Type*) [outParam (LinearOrderedAddCommGroup G)]

/-- A linearly ordered `AddTorsor` is an `AddTorsor` with linearly orders on the group and
the type acted on, such that both orders are compatiable with the additive group action. -/
class LinearOrderedAddTorsor extends LinearOrderedAddAction G P, OrderedAddTorsor G P

variable {G} {P} [outParam (LinearOrderedAddCommGroup G)] [LinearOrderedAddTorsor G P]

@[simp]
theorem vadd_right_le_iff {f g : G} {a : P} : f +ᵥ a ≤ g +ᵥ a ↔ f ≤ g :=
  ⟨fun h ↦ not_lt.mp (fun lt ↦ (not_lt_of_le h) (vadd_right_lt lt a)), fun h ↦ vadd_right_le h a⟩

@[simp]
theorem vadd_right_lt_iff {f g : G} {a : P} : f +ᵥ a < g +ᵥ a ↔ f < g := by
  simp only [lt_iff_not_ge, vadd_right_le_iff]

@[simp]
theorem vsub_right_le_iff {a b x : P} : a -ᵥ x ≤ b -ᵥ x ↔ a ≤ b := by
  nth_rw 2 [← vsub_vadd a x, ← vsub_vadd b x]
  exact vadd_right_le_iff.symm

theorem vsub_right_le {a b : P} (h : a ≤ b) (x : P) : a -ᵥ x ≤ b -ᵥ x := vsub_right_le_iff.mpr h

@[simp]
theorem vsub_left_le_iff {x a b : P} : x -ᵥ a ≤ x -ᵥ b ↔ b ≤ a := by
  rw [← neg_vsub_eq_vsub_rev a x, ← neg_vsub_eq_vsub_rev b x]
  exact neg_le_neg_iff.trans vsub_right_le_iff

theorem vsub_left_le {a b : P} (h : a ≤ b) (x : P) : x -ᵥ b ≤ x -ᵥ a := vsub_left_le_iff.mpr h

end LinearOrder

section CircularOrder

variable (G : outParam Type*) (P : Type*) [outParam (CircularOrderedAddCommGroup G)]

/-- A circular ordered `AddTorsor` is an `AddTorsor` with circular orders on the group and
the type acted on, such that both orders are compatiable with the additive group action. -/
class CircularOrderedAddTorsor extends CircularOrderedAddAction G P, AddTorsor G P where
  btw_vadd_right {e f g : G} (h : Btw.btw e f g) (a : P) : btw (e +ᵥ a) (f +ᵥ a) (g +ᵥ a)

variable {G} {P} [outParam (CircularOrderedAddCommGroup G)] [CircularOrderedAddTorsor G P]

theorem btw_vadd_right {e f g : G} (h : btw e f g) (a : P) : btw (e +ᵥ a) (f +ᵥ a) (g +ᵥ a) :=
  CircularOrderedAddTorsor.btw_vadd_right h a

theorem sbtw_vadd_right {e f g : G} (h : sbtw e f g) (a : P) : sbtw (e +ᵥ a) (f +ᵥ a) (g +ᵥ a) := by
  by_contra hn
  rcases (btw_vadd_right h.btw a).antisymm (btw_iff_not_sbtw.mpr hn) with eq | eq | eq
  · rw [vadd_right_cancel a eq] at h
    exact sbtw_irrefl_left h
  · rw [vadd_right_cancel a eq] at h
    exact sbtw_irrefl_right h
  · rw [vadd_right_cancel a eq] at h
    exact sbtw_irrefl_left_right h

@[simp]
theorem btw_vadd_right_iff {e f g : G} {a : P} : btw (e +ᵥ a) (f +ᵥ a) (g +ᵥ a) ↔ btw e f g :=
  ⟨fun h ↦ btw_iff_not_sbtw.mpr (fun hs ↦ sbtw_iff_not_btw.mp (sbtw_vadd_right hs a) h),
    fun h ↦ btw_vadd_right h a⟩

@[simp]
theorem sbtw_vadd_right_iff {e f g : G} {a : P} : sbtw (e +ᵥ a) (f +ᵥ a) (g +ᵥ a) ↔ sbtw e f g := by
  simp only [sbtw_iff_not_btw, btw_vadd_right_iff]

@[simp]
theorem btw_vsub_right_iff {a b c x : P} : btw (a -ᵥ x) (b -ᵥ x) (c -ᵥ x) ↔ btw a b c := by
  nth_rw 2 [← vsub_vadd a x, ← vsub_vadd b x, ← vsub_vadd c x]
  exact btw_vadd_right_iff.symm

theorem btw_vsub_right {a b c : P} (h : btw a b c) (x : P) : btw (a -ᵥ x) (b -ᵥ x) (c -ᵥ x) :=
  btw_vsub_right_iff.mpr h

@[simp]
theorem sbtw_vsub_right_iff {a b c x : P} : sbtw (a -ᵥ x) (b -ᵥ x) (c -ᵥ x) ↔ sbtw a b c := by
  simp only [sbtw_iff_not_btw, btw_vsub_right_iff]

theorem sbtw_vsub_right {a b c : P} (h : sbtw a b c) (x : P) : sbtw (a -ᵥ x) (b -ᵥ x) (c -ᵥ x) :=
  sbtw_vsub_right_iff.mpr h

@[simp]
theorem btw_vsub_left_iff {x a b c : P} : btw (x -ᵥ a) (x -ᵥ b) (x -ᵥ c) ↔ btw a c b := by
  rw [← neg_vsub_eq_vsub_rev a x, ← neg_vsub_eq_vsub_rev b x, ← neg_vsub_eq_vsub_rev c x]
  exact btw_neg_iff.trans btw_vsub_right_iff

theorem btw_vsub_left {a b c : P} (h : btw a b c) (x : P) : btw (x -ᵥ a) (x -ᵥ c) (x -ᵥ b) :=
  btw_vsub_left_iff.mpr h

theorem btw_vsub_left_iff' {x a b c : P} : btw (x -ᵥ a) (x -ᵥ b) (x -ᵥ c) ↔ btw c b a :=
  btw_vsub_left_iff.trans btw_cyclic.symm

theorem btw_vsub_left_iff'' {x a b c : P} : btw (x -ᵥ a) (x -ᵥ b) (x -ᵥ c) ↔ btw b a c :=
  btw_vsub_left_iff.trans btw_cyclic

theorem btw_vsub_left_iff_not_sbtw {x a b c : P} : btw (x -ᵥ a) (x -ᵥ b) (x -ᵥ c) ↔ ¬ sbtw a b c :=
  btw_vsub_left_iff'.trans btw_iff_not_sbtw

theorem not_btw_vsub_left_iff_sbtw {x a b c : P} : ¬ btw (x -ᵥ a) (x -ᵥ b) (x -ᵥ c) ↔ sbtw a b c :=
  btw_vsub_left_iff_not_sbtw.not_left

theorem sbtw_vsub_left_iff_not_btw {x a b c : P} : sbtw (x -ᵥ a) (x -ᵥ b) (x -ᵥ c) ↔ ¬ btw a b c :=
  sbtw_iff_not_btw.trans btw_vsub_left_iff'.not

theorem not_sbtw_vsub_left_iff_btw {x a b c : P} : ¬ sbtw (x -ᵥ a) (x -ᵥ b) (x -ᵥ c) ↔ btw a b c :=
  sbtw_vsub_left_iff_not_btw.not_left

@[simp]
theorem sbtw_vsub_left_iff {x a b c : P} : sbtw (x -ᵥ a) (x -ᵥ b) (x -ᵥ c) ↔ sbtw a c b :=
  sbtw_vsub_left_iff_not_btw.trans (sbtw_iff_not_btw.symm.trans sbtw_cyclic)

theorem sbtw_vsub_left {a b c : P} (h : sbtw a b c) (x : P) : sbtw (x -ᵥ a) (x -ᵥ c) (x -ᵥ b) :=
  sbtw_vsub_left_iff.mpr h

end CircularOrder

end Class

section symmetry
-- These lemmas show that the following definitions satisfy symmetry.

variable {G : outParam Type*} {P : Type*}

lemma vsub_le_zero_iff_zero_le_vsub_rev [outParam (OrderedAddCommGroup G)] [AddTorsor G P] (a b : P) : a -ᵥ b ≤ 0 ↔ 0 ≤ b -ᵥ a :=
  (add_le_add_iff_right (b -ᵥ a)).symm.trans (by rw [vsub_add_vsub_cancel, vsub_self, zero_add])

lemma vsub_lt_zero_iff_zero_lt_vsub_rev [outParam (OrderedAddCommGroup G)] [AddTorsor G P] (a b : P) : a -ᵥ b < 0 ↔ 0 < b -ᵥ a :=
  (add_lt_add_iff_right (b -ᵥ a)).symm.trans (by rw [vsub_add_vsub_cancel, vsub_self, zero_add])

variable [outParam (CircularOrderedAddCommGroup G)] [AddTorsor G P] (a b c : P)

lemma btw_vsub_fst_iff_btw_vsub_snd : btw 0 (b -ᵥ a) (c -ᵥ a) ↔ btw (a -ᵥ b) 0 (c -ᵥ b) :=
  Iff.trans (by simp only [vsub_add_vsub_cancel, vsub_self, zero_add]) (btw_add_right_iff (g := b -ᵥ a))

lemma btw_vsub_fst_iff_btw_vsub_trd : btw 0 (b -ᵥ a) (c -ᵥ a) ↔ btw (a -ᵥ c) (b -ᵥ c) 0 :=
  Iff.trans (by simp only [vsub_add_vsub_cancel, vsub_self, zero_add]) (btw_add_right_iff (g := c -ᵥ a))

lemma btw_vsub_snd_iff_btw_vsub_trd : btw (a -ᵥ b) 0 (c -ᵥ b) ↔ btw (a -ᵥ c) (b -ᵥ c) 0 :=
  (btw_vsub_fst_iff_btw_vsub_snd a b c).symm.trans (btw_vsub_fst_iff_btw_vsub_trd a b c)

lemma sbtw_vsub_fst_iff_sbtw_vsub_snd : sbtw 0 (b -ᵥ a) (c -ᵥ a) ↔ sbtw (a -ᵥ b) 0 (c -ᵥ b) :=
  Iff.trans (by simp only [vsub_add_vsub_cancel, vsub_self, zero_add]) (sbtw_add_right_iff (g := b -ᵥ a))

lemma sbtw_vsub_fst_iff_sbtw_vsub_trd : sbtw 0 (b -ᵥ a) (c -ᵥ a) ↔ sbtw (a -ᵥ c) (b -ᵥ c) 0 :=
  Iff.trans (by simp only [vsub_add_vsub_cancel, vsub_self, zero_add]) (sbtw_add_right_iff (g := c -ᵥ a))

lemma sbtw_vsub_snd_iff_sbtw_vsub_trd : sbtw (a -ᵥ b) 0 (c -ᵥ b) ↔ sbtw (a -ᵥ c) (b -ᵥ c) 0 :=
  (sbtw_vsub_fst_iff_sbtw_vsub_snd a b c).symm.trans (sbtw_vsub_fst_iff_sbtw_vsub_trd a b c)

end symmetry

namespace AddTorsor

section contruction

variable (G : outParam Type*) (P : Type*)

/-- If the group acting on an `AddTorsor` is a partial ordered group, then there is a natual
partial order on the `AddTorsor` along with a corresponding structure of partial ordered `AddTorsor`
induced by the partial ordered group. This is not an instance, since we do not want it to
conflict with other partial order structures that may exist on the `AddTorsor`. -/
local instance OrderedAddTorsor_of_OrderedAddCommGroup [outParam (OrderedAddCommGroup G)] [AddTorsor G P] : OrderedAddTorsor G P where
  vsub_vadd' := vsub_vadd'
  vadd_vsub' := vadd_vsub'
  le a b := a -ᵥ b ≤ 0
  lt a b := a -ᵥ b < 0
  le_refl _ := by simp only [vsub_self, le_refl]
  le_trans a b c hab hbc := (vsub_add_vsub_cancel a b c).symm.trans_le (add_nonpos hab hbc)
  lt_iff_le_not_le a b :=
    have h : a -ᵥ b < 0 ↔ a -ᵥ b ≤ 0 ∧ ¬ 0 ≤ a -ᵥ b := Preorder.lt_iff_le_not_le (a -ᵥ b) 0
    ⟨fun hab ↦ ⟨(h.1 hab).1, (vsub_le_zero_iff_zero_le_vsub_rev b a).not.mpr (h.1 hab).2⟩,
      fun ⟨hab, hba⟩ ↦ h.2 ⟨hab, (vsub_le_zero_iff_zero_le_vsub_rev b a).not.mp hba⟩⟩
  le_antisymm a b hab hba := eq_of_vsub_eq_zero <|
    PartialOrder.le_antisymm (a -ᵥ b) 0 hab ((vsub_le_zero_iff_zero_le_vsub_rev b a).mp hba)
  vadd_left_le h _ := by simpa only [vadd_vsub_vadd_cancel_left] using h
  vadd_right_le h _ := by
    simpa only [vadd_vsub_vadd_cancel_right, tsub_le_iff_right, zero_add] using h

/-- If the group acting on an `AddTorsor` is a linearly ordered group, then there is a natual
linearly order on the `AddTorsor` along with a corresponding structure of linearly ordered `AddTorsor`
induced by the linearly ordered group. This is not an instance, since we do not want it to
conflict with other linearly order structures that may exist on the `AddTorsor`. -/
noncomputable local instance LinearOrderedAddTorsor_of_LinearOrderedAddCommGroup [outParam (LinearOrderedAddCommGroup G)] [AddTorsor G P] : LinearOrderedAddTorsor G P where
  le_total := fun a b ↦
    (or_congr_right (vsub_le_zero_iff_zero_le_vsub_rev b a)).mpr (LinearOrder.le_total (a -ᵥ b) 0)
  decidableLE := decRel fun _ ↦ _
  vsub_vadd' := vsub_vadd'
  vadd_vsub' := vadd_vsub'
  vadd_right_le := vadd_right_le

/-- If the group acting on an `AddTorsor` is a circular ordered group, then there is a natual
circular order on the `AddTorsor` along with a corresponding structure of circular ordered `AddTorsor`
induced by the circular ordered group. This is not an instance, since we do not want it to
conflict with other circular order structures that may exist on the `AddTorsor`. -/
local instance CircularOrderedAddTorsor_of_CircularOrderedAddCommGroup [outParam (CircularOrderedAddCommGroup G)] [AddTorsor G P] : CircularOrderedAddTorsor G P where
  vsub_vadd' := vsub_vadd'
  vadd_vsub' := vadd_vsub'
  btw a b c := btw 0 (b -ᵥ a) (c -ᵥ a)
  sbtw a b c := sbtw 0 (b -ᵥ a) (c -ᵥ a)
  btw_refl a := by simp only [vsub_self, btw_rfl]
  btw_cyclic_left h := btw_cyclic_left ((btw_vsub_fst_iff_btw_vsub_snd _ _ _).mp h)
  sbtw_iff_btw_not_btw {a} {b} {c} := by
    simp only [btw_vsub_fst_iff_btw_vsub_trd c b a]
    exact sbtw_iff_btw_not_btw
  sbtw_trans_left {a} {b} _ _ ha h := by
    have h := sbtw_add_right h (b -ᵥ a)
    rw [zero_add, vsub_add_vsub_cancel, vsub_add_vsub_cancel] at h
    exact sbtw_trans_left ha h
  btw_antisymm ha h := by
    have h := btw_antisymm ha ((btw_vsub_fst_iff_btw_vsub_trd _ _ _).mp h)
    nth_rw 1 [vsub_left_cancel_iff, vsub_eq_zero_iff_eq, eq_comm, vsub_eq_zero_iff_eq, eq_comm] at h
    exact h
  btw_total a b c := by
    simp only [btw_vsub_fst_iff_btw_vsub_trd c b a]
    exact btw_total 0 (b -ᵥ a) (c -ᵥ a)
  btw_vadd_left h _ := by
    simpa only [vadd_vsub_vadd_cancel_left] using h
  btw_vadd_right {e} {_} {_} h _ := by
    simp only [vadd_vsub_vadd_cancel_right, ← sub_self e]
    exact btw_sub_right h e

end contruction

end AddTorsor

end Mathlib.Algebra.AddTorsor
