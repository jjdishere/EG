import EuclideanGeometry.Foundation.Axiom.Basic.Angle.FromMathlib

/-!
# Theorems that should exist in Mathlib

Maybe we can create some PRs to mathlib in the future.
-/

open Real

/-!
## More theorems about trigonometric functions in Mathlib

These theorems about trigonometric functions mostly exist in Mathlib in the version of `Real.sin`, `Real.cos` or `Real.tan` but not in the version of `Real.Angle.sin`, `Real.Angle.cos` or `Real.Angle.tan`.
In this file, we will translate these theorems into the version of `EuclidGeom.AngValue.sin`, `EuclidGeom.AngValue.cos` or `EuclidGeom.AngValue.tan`.
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
## Compatibility among group, addtorsor and order
-/

section Mathlib.Algebra.Order.Group.Defs

class CircularOrderAddCommGroup (G : Type*) extends AddCommGroup G, CircularOrder G where
  btw_add {a b c : G} (h : btw a b c) (t : G) : btw (a + t) (b + t) (c + t)

namespace CircularOrderAddCommGroup

variable {G : Type*} [CircularOrderAddCommGroup G]

@[simp]
theorem btw_add_iff {a b c t : G} : btw (a + t) (b + t) (c + t) ↔ btw a b c := by
  refine' ⟨fun h ↦ _, fun h ↦ btw_add h t⟩
  have h := btw_add h (- t)
  simp only [add_neg_cancel_right] at h
  exact h

theorem sbtw_add {a b c : G} (h : sbtw a b c) (t : G) : sbtw (a + t) (b + t) (c + t) := sorry

@[simp]
theorem sbtw_add_iff {a b c t : G} : sbtw (a + t) (b + t) (c + t) ↔ sbtw a b c := sorry

end CircularOrderAddCommGroup

instance QuotientAddGroup.instCircularOrderAddCommGroup (G : Type*) [LinearOrderedAddCommGroup G] [ha : Archimedean G] {p : G} [hp : Fact (0 < p)] : CircularOrderAddCommGroup (G ⧸ AddSubgroup.zmultiples p) := sorry

section Mathlib.Algebra.Order.Group.Defs



section Mathlib.Algebra.AddTorsor

variable {V : outParam Type*} {L : Type*} [outParam (AddCommGroup V)] [AddTorsor V L]

section PartialOrder

end PartialOrder

section LinearOrder

end LinearOrder

section CircularOrder

end CircularOrder

end Mathlib.Algebra.AddTorsor
