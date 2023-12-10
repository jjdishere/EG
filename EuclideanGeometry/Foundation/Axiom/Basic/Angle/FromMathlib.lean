import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# APIs about Angle from Mathlib

We use `AngValue` as an alias of `Real.Angle`.
-/

noncomputable section

open Real

section Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

namespace EuclidGeom

def AngValue : Type := Angle

namespace AngValue

instance : NormedAddCommGroup AngValue :=
  inferInstanceAs (NormedAddCommGroup Angle)

instance : Inhabited AngValue :=
  inferInstanceAs (Inhabited Angle)

/-- The canonical map from `ℝ` to the quotient `AngValue`. -/
@[coe]
protected def coe (r : ℝ) : AngValue := Angle.coe r

instance : Coe ℝ AngValue := ⟨AngValue.coe⟩

instance : CircularOrder AngValue :=
  inferInstanceAs (CircularOrder Angle)

@[continuity]
theorem continuous_coe : Continuous ((↑) : ℝ → AngValue) :=
  continuous_quotient_mk'

/-- Coercion `ℝ → AngValue` as an additive homomorphism. -/
def coeHom : ℝ →+ AngValue :=
  Angle.coeHom

@[simp]
theorem coe_coeHom : (coeHom : ℝ → AngValue) = ((↑) : ℝ → AngValue) :=
  rfl

/-- An induction principle to deduce results for `AngValue` from those for `ℝ`, used with
`induction θ using AngValue.induction_on`. -/
@[elab_as_elim]
protected theorem induction_on {p : AngValue → Prop} (θ : AngValue) (h : ∀ x : ℝ, p x) : p θ :=
  Quotient.inductionOn' θ h

@[simp, norm_cast]
theorem coe_zero : ↑(0 : ℝ) = (0 : AngValue) :=
  rfl

@[simp, norm_cast]
theorem coe_add (x y : ℝ) : ↑(x + y : ℝ) = (↑x + ↑y : AngValue) :=
  rfl

@[simp, norm_cast]
theorem coe_neg (x : ℝ) : ↑(-x : ℝ) = -(↑x : AngValue) :=
  rfl

@[simp, norm_cast]
theorem coe_sub (x y : ℝ) : ↑(x - y : ℝ) = (↑x - ↑y : AngValue) :=
  rfl

@[norm_cast]
theorem coe_nsmul (n : ℕ) (x : ℝ) : ↑(n • x : ℝ) = n • (↑x : AngValue) :=
  rfl

@[norm_cast]
theorem coe_zsmul (z : ℤ) (x : ℝ) : ↑(z • x : ℝ) = z • (↑x : AngValue) :=
  rfl

@[simp, norm_cast]
theorem coe_nat_mul_eq_nsmul (x : ℝ) (n : ℕ) : ↑((n : ℝ) * x) = n • (↑x : AngValue) :=
  Angle.coe_nat_mul_eq_nsmul _ _

@[simp, norm_cast]
theorem coe_int_mul_eq_zsmul (x : ℝ) (n : ℤ) : ↑((n : ℝ) * x : ℝ) = n • (↑x : AngValue) :=
  Angle.coe_int_mul_eq_zsmul _ _

theorem eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : AngValue) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * π * k :=
  Angle.angle_eq_iff_two_pi_dvd_sub

@[simp]
theorem coe_two_pi : ↑(2 * π : ℝ) = (0 : AngValue) :=
  Angle.coe_two_pi

@[simp]
theorem neg_coe_pi : -(π : AngValue) = π :=
  Angle.neg_coe_pi

@[simp]
theorem two_nsmul_coe_div_two (θ : ℝ) : (2 : ℕ) • (↑(θ / 2) : AngValue) = θ :=
  Angle.two_nsmul_coe_div_two _

@[simp]
theorem two_zsmul_coe_div_two (θ : ℝ) : (2 : ℤ) • (↑(θ / 2) : AngValue) = θ :=
  Angle.two_zsmul_coe_div_two _

-- Porting note: @[simp] can prove it
theorem two_nsmul_neg_pi_div_two : (2 : ℕ) • (↑(-π / 2) : AngValue) = π :=
  Angle.two_nsmul_neg_pi_div_two

-- Porting note: @[simp] can prove it
theorem two_zsmul_neg_pi_div_two : (2 : ℤ) • (↑(-π / 2) : AngValue) = π :=
  Angle.two_zsmul_neg_pi_div_two

theorem sub_coe_pi_eq_add_coe_pi (θ : AngValue) : θ - π = θ + π :=
  Angle.sub_coe_pi_eq_add_coe_pi _

@[simp]
theorem two_nsmul_coe_pi : (2 : ℕ) • (π : AngValue) = 0 :=
  Angle.two_nsmul_coe_pi

@[simp]
theorem two_zsmul_coe_pi : (2 : ℤ) • (π : AngValue) = 0 :=
  Angle.two_zsmul_coe_pi

@[simp]
theorem coe_pi_add_coe_pi : (π : AngValue) + π = 0 :=
  Angle.coe_pi_add_coe_pi

theorem zsmul_eq_iff {ψ θ : AngValue} {z : ℤ} (hz : z ≠ 0) :
    z • ψ = z • θ ↔ ∃ k : Fin z.natAbs, ψ = θ + (k : ℕ) • (2 * π / z : ℝ) :=
  Angle.zsmul_eq_iff hz

theorem nsmul_eq_iff {ψ θ : AngValue} {n : ℕ} (hz : n ≠ 0) :
    n • ψ = n • θ ↔ ∃ k : Fin n, ψ = θ + (k : ℕ) • (2 * π / n : ℝ) :=
  Angle.nsmul_eq_iff hz

theorem two_zsmul_eq_iff {ψ θ : AngValue} : (2 : ℤ) • ψ = (2 : ℤ) • θ ↔ ψ = θ ∨ ψ = θ + ↑π :=
  Angle.two_zsmul_eq_iff

theorem two_nsmul_eq_iff {ψ θ : AngValue} : (2 : ℕ) • ψ = (2 : ℕ) • θ ↔ ψ = θ ∨ ψ = θ + ↑π :=
  Angle.two_nsmul_eq_iff

theorem two_nsmul_eq_zero_iff {θ : AngValue} : (2 : ℕ) • θ = 0 ↔ θ = 0 ∨ θ = π :=
  Angle.two_nsmul_eq_zero_iff

theorem two_nsmul_ne_zero_iff {θ : AngValue} : (2 : ℕ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π :=
  Angle.two_nsmul_ne_zero_iff

theorem two_zsmul_eq_zero_iff {θ : AngValue} : (2 : ℤ) • θ = 0 ↔ θ = 0 ∨ θ = π :=
  Angle.two_zsmul_eq_zero_iff

theorem two_zsmul_ne_zero_iff {θ : AngValue} : (2 : ℤ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π :=
  Angle.two_zsmul_ne_zero_iff

theorem eq_neg_self_iff {θ : AngValue} : θ = -θ ↔ θ = 0 ∨ θ = π :=
  Angle.eq_neg_self_iff

theorem ne_neg_self_iff {θ : AngValue} : θ ≠ -θ ↔ θ ≠ 0 ∧ θ ≠ π :=
  Angle.ne_neg_self_iff

theorem neg_eq_self_iff {θ : AngValue} : -θ = θ ↔ θ = 0 ∨ θ = π :=
  Angle.neg_eq_self_iff

theorem neg_ne_self_iff {θ : AngValue} : -θ ≠ θ ↔ θ ≠ 0 ∧ θ ≠ π :=
  Angle.neg_ne_self_iff

theorem two_nsmul_eq_pi_iff {θ : AngValue} : (2 : ℕ) • θ = π ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) :=
  Angle.two_nsmul_eq_pi_iff

theorem two_zsmul_eq_pi_iff {θ : AngValue} : (2 : ℤ) • θ = π ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) :=
  Angle.two_nsmul_eq_pi_iff

theorem cos_eq_iff_coe_eq_or_eq_neg {θ ψ : ℝ} :
    cos θ = cos ψ ↔ (θ : AngValue) = ψ ∨ (θ : AngValue) = -ψ :=
  Angle.cos_eq_iff_coe_eq_or_eq_neg

theorem sin_eq_iff_coe_eq_or_add_eq_pi {θ ψ : ℝ} :
    sin θ = sin ψ ↔ (θ : AngValue) = ψ ∨ (θ : AngValue) + ψ = π :=
  Angle.sin_eq_iff_coe_eq_or_add_eq_pi

theorem cos_sin_inj {θ ψ : ℝ} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : (θ : AngValue) = ψ :=
  Angle.cos_sin_inj Hcos Hsin

/-- The sine of a `AngValue`. -/
def sin (θ : AngValue) : ℝ :=
  Angle.sin θ

@[simp]
theorem sin_coe (x : ℝ) : sin (x : AngValue) = Real.sin x :=
  Angle.sin_coe _

@[continuity]
theorem continuous_sin : Continuous sin :=
  Angle.continuous_sin

/-- The cosine of a `AngValue`. -/
def cos (θ : AngValue) : ℝ :=
  Angle.cos θ

@[simp]
theorem cos_coe (x : ℝ) : cos (x : AngValue) = Real.cos x :=
  Angle.cos_coe _

@[continuity]
theorem continuous_cos : Continuous cos :=
  Angle.continuous_cos

theorem cos_eq_real_cos_iff_eq_or_eq_neg {θ : AngValue} {ψ : ℝ} :
    cos θ = Real.cos ψ ↔ θ = ψ ∨ θ = -ψ :=
  Angle.cos_eq_real_cos_iff_eq_or_eq_neg

theorem cos_eq_iff_eq_or_eq_neg {θ ψ : AngValue} : cos θ = cos ψ ↔ θ = ψ ∨ θ = -ψ :=
  Angle.cos_eq_iff_eq_or_eq_neg

theorem sin_eq_real_sin_iff_eq_or_add_eq_pi {θ : AngValue} {ψ : ℝ} :
    sin θ = Real.sin ψ ↔ θ = ψ ∨ θ + ψ = π :=
  Angle.sin_eq_real_sin_iff_eq_or_add_eq_pi

theorem sin_eq_iff_eq_or_add_eq_pi {θ ψ : AngValue} : sin θ = sin ψ ↔ θ = ψ ∨ θ + ψ = π :=
  Angle.sin_eq_iff_eq_or_add_eq_pi

@[simp]
theorem sin_zero : sin (0 : AngValue) = 0 :=
  Angle.sin_zero

-- Porting note: @[simp] can prove it
theorem sin_coe_pi : sin (π : AngValue) = 0 :=
  Angle.sin_coe_pi

theorem sin_eq_zero_iff {θ : AngValue} : sin θ = 0 ↔ θ = 0 ∨ θ = π :=
  Angle.sin_eq_zero_iff

theorem sin_ne_zero_iff {θ : AngValue} : sin θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π :=
  Angle.sin_ne_zero_iff

@[simp]
theorem sin_neg (θ : AngValue) : sin (-θ) = -sin θ :=
  Angle.sin_neg _

theorem sin_antiperiodic : Function.Antiperiodic sin (π : AngValue) :=
  Angle.sin_antiperiodic

@[simp]
theorem sin_add_pi (θ : AngValue) : sin (θ + π) = -sin θ :=
  Angle.sin_add_pi _

@[simp]
theorem sin_sub_pi (θ : AngValue) : sin (θ - π) = -sin θ :=
  Angle.sin_sub_pi _

@[simp]
theorem cos_zero : cos (0 : AngValue) = 1 :=
  Angle.cos_zero

-- Porting note: @[simp] can prove it
theorem cos_coe_pi : cos (π : AngValue) = -1 :=
  Angle.cos_coe_pi

@[simp]
theorem cos_neg (θ : AngValue) : cos (-θ) = cos θ :=
  Angle.cos_neg _

theorem cos_antiperiodic : Function.Antiperiodic cos (π : AngValue) :=
  Angle.cos_antiperiodic

@[simp]
theorem cos_add_pi (θ : AngValue) : cos (θ + π) = -cos θ :=
  Angle.cos_add_pi _

@[simp]
theorem cos_sub_pi (θ : AngValue) : cos (θ - π) = -cos θ :=
  Angle.cos_sub_pi _

theorem cos_eq_zero_iff {θ : AngValue} : cos θ = 0 ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) :=
  Angle.cos_eq_zero_iff

theorem sin_add (θ₁ θ₂ : AngValue) : sin (θ₁ + θ₂) = sin θ₁ * cos θ₂ + cos θ₁ * sin θ₂ :=
  Angle.sin_add _ _

theorem cos_add (θ₁ θ₂ : AngValue) : cos (θ₁ + θ₂) = cos θ₁ * cos θ₂ - sin θ₁ * sin θ₂ :=
  Angle.cos_add _ _

@[simp]
theorem cos_sq_add_sin_sq (θ : AngValue) : cos θ ^ 2 + sin θ ^ 2 = 1 :=
  Angle.cos_sq_add_sin_sq _

theorem sin_add_pi_div_two (θ : AngValue) : sin (θ + ↑(π / 2)) = cos θ :=
  Angle.sin_add_pi_div_two _

theorem sin_sub_pi_div_two (θ : AngValue) : sin (θ - ↑(π / 2)) = -cos θ :=
  Angle.sin_sub_pi_div_two _

theorem sin_pi_div_two_sub (θ : AngValue) : sin (↑(π / 2) - θ) = cos θ :=
  Angle.sin_pi_div_two_sub _

theorem cos_add_pi_div_two (θ : AngValue) : cos (θ + ↑(π / 2)) = -sin θ :=
  Angle.cos_add_pi_div_two _

theorem cos_sub_pi_div_two (θ : AngValue) : cos (θ - ↑(π / 2)) = sin θ :=
  Angle.cos_sub_pi_div_two _

theorem cos_pi_div_two_sub (θ : AngValue) : cos (↑(π / 2) - θ) = sin θ :=
  Angle.cos_pi_div_two_sub _

theorem abs_sin_eq_of_two_nsmul_eq {θ ψ : AngValue} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) :
    |sin θ| = |sin ψ| :=
  Angle.abs_sin_eq_of_two_nsmul_eq h

theorem abs_sin_eq_of_two_zsmul_eq {θ ψ : AngValue} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) :
    |sin θ| = |sin ψ| :=
  Angle.abs_sin_eq_of_two_zsmul_eq h

theorem abs_cos_eq_of_two_nsmul_eq {θ ψ : AngValue} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) :
    |cos θ| = |cos ψ| :=
  Angle.abs_cos_eq_of_two_nsmul_eq h

theorem abs_cos_eq_of_two_zsmul_eq {θ ψ : AngValue} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) :
    |cos θ| = |cos ψ| :=
  Angle.abs_cos_eq_of_two_zsmul_eq h

@[simp]
theorem coe_toIcoMod (θ ψ : ℝ) : ↑(toIcoMod two_pi_pos ψ θ) = (θ : AngValue) :=
  Angle.coe_toIcoMod _ _

@[simp]
theorem coe_toIocMod (θ ψ : ℝ) : ↑(toIocMod two_pi_pos ψ θ) = (θ : AngValue) :=
  Angle.coe_toIocMod _ _

/-- Convert a `AngValue` to a real number in the interval `Ioc (-π) π`. -/
def toReal (θ : AngValue) : ℝ :=
  Angle.toReal θ

theorem toReal_coe (θ : ℝ) : (θ : AngValue).toReal = toIocMod two_pi_pos (-π) θ :=
  rfl

theorem toReal_coe_eq_self_iff {θ : ℝ} : (θ : AngValue).toReal = θ ↔ -π < θ ∧ θ ≤ π :=
  Angle.toReal_coe_eq_self_iff

theorem toReal_coe_eq_self_iff_mem_Ioc {θ : ℝ} : (θ : AngValue).toReal = θ ↔ θ ∈ Set.Ioc (-π) π :=
  Angle.toReal_coe_eq_self_iff_mem_Ioc

theorem toReal_injective : Function.Injective toReal :=
  Angle.toReal_injective

@[simp]
theorem toReal_inj {θ ψ : AngValue} : θ.toReal = ψ.toReal ↔ θ = ψ :=
  Angle.toReal_inj

@[simp]
theorem coe_toReal (θ : AngValue) : (θ.toReal : AngValue) = θ :=
  Angle.coe_toReal _

theorem neg_pi_lt_toReal (θ : AngValue) : -π < θ.toReal :=
  Angle.neg_pi_lt_toReal _

theorem toReal_le_pi (θ : AngValue) : θ.toReal ≤ π :=
  Angle.toReal_le_pi _

theorem abs_toReal_le_pi (θ : AngValue) : |θ.toReal| ≤ π :=
  Angle.abs_toReal_le_pi _

theorem toReal_mem_Ioc (θ : AngValue) : θ.toReal ∈ Set.Ioc (-π) π :=
  Angle.toReal_mem_Ioc _

@[simp]
theorem toIocMod_toReal (θ : AngValue) : toIocMod two_pi_pos (-π) θ.toReal = θ.toReal :=
  Angle.toIocMod_toReal _

@[simp]
theorem toReal_zero : (0 : AngValue).toReal = 0 :=
  Angle.toReal_zero

@[simp]
theorem toReal_eq_zero_iff {θ : AngValue} : θ.toReal = 0 ↔ θ = 0 :=
  Angle.toReal_eq_zero_iff

@[simp]
theorem toReal_pi : (π : AngValue).toReal = π :=
  Angle.toReal_pi

@[simp]
theorem toReal_eq_pi_iff {θ : AngValue} : θ.toReal = π ↔ θ = π :=
  Angle.toReal_eq_pi_iff

theorem pi_ne_zero : (π : AngValue) ≠ 0 :=
  Angle.pi_ne_zero

@[simp]
theorem toReal_pi_div_two : ((π / 2 : ℝ) : AngValue).toReal = π / 2 :=
  Angle.toReal_pi_div_two

@[simp]
theorem toReal_eq_pi_div_two_iff {θ : AngValue} : θ.toReal = π / 2 ↔ θ = (π / 2 : ℝ) :=
  Angle.toReal_eq_pi_div_two_iff

@[simp]
theorem toReal_neg_pi_div_two : ((-π / 2 : ℝ) : AngValue).toReal = -π / 2 :=
  Angle.toReal_neg_pi_div_two

@[simp]
theorem toReal_eq_neg_pi_div_two_iff {θ : AngValue} : θ.toReal = -π / 2 ↔ θ = (-π / 2 : ℝ) :=
  Angle.toReal_eq_neg_pi_div_two_iff

theorem pi_div_two_ne_zero : ((π / 2 : ℝ) : AngValue) ≠ 0 :=
  Angle.pi_div_two_ne_zero

theorem neg_pi_div_two_ne_zero : ((-π / 2 : ℝ) : AngValue) ≠ 0 :=
  Angle.neg_pi_div_two_ne_zero

theorem abs_toReal_coe_eq_self_iff {θ : ℝ} : |(θ : AngValue).toReal| = θ ↔ 0 ≤ θ ∧ θ ≤ π :=
  Angle.abs_toReal_coe_eq_self_iff

theorem abs_toReal_neg_coe_eq_self_iff {θ : ℝ} : |(-θ : AngValue).toReal| = θ ↔ 0 ≤ θ ∧ θ ≤ π :=
  Angle.abs_toReal_neg_coe_eq_self_iff

theorem abs_toReal_eq_pi_div_two_iff {θ : AngValue} :
    |θ.toReal| = π / 2 ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) :=
  Angle.abs_toReal_eq_pi_div_two_iff

theorem nsmul_toReal_eq_mul {n : ℕ} (h : n ≠ 0) {θ : AngValue} :
    (n • θ).toReal = n * θ.toReal ↔ θ.toReal ∈ Set.Ioc (-π / n) (π / n) :=
  Angle.nsmul_toReal_eq_mul h

theorem two_nsmul_toReal_eq_two_mul {θ : AngValue} :
    ((2 : ℕ) • θ).toReal = 2 * θ.toReal ↔ θ.toReal ∈ Set.Ioc (-π / 2) (π / 2) :=
  Angle.two_nsmul_toReal_eq_two_mul

theorem two_zsmul_toReal_eq_two_mul {θ : AngValue} :
    ((2 : ℤ) • θ).toReal = 2 * θ.toReal ↔ θ.toReal ∈ Set.Ioc (-π / 2) (π / 2) :=
  Angle.two_zsmul_toReal_eq_two_mul

theorem toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff {θ : ℝ} {k : ℤ} :
    (θ : AngValue).toReal = θ - 2 * k * π ↔ θ ∈ Set.Ioc ((2 * k - 1 : ℝ) * π) ((2 * k + 1) * π) :=
  Angle.toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff

theorem toReal_coe_eq_self_sub_two_pi_iff {θ : ℝ} :
    (θ : AngValue).toReal = θ - 2 * π ↔ θ ∈ Set.Ioc π (3 * π) :=
  Angle.toReal_coe_eq_self_sub_two_pi_iff

theorem toReal_coe_eq_self_add_two_pi_iff {θ : ℝ} :
    (θ : AngValue).toReal = θ + 2 * π ↔ θ ∈ Set.Ioc (-3 * π) (-π) :=
  Angle.toReal_coe_eq_self_add_two_pi_iff

theorem two_nsmul_toReal_eq_two_mul_sub_two_pi {θ : AngValue} :
    ((2 : ℕ) • θ).toReal = 2 * θ.toReal - 2 * π ↔ π / 2 < θ.toReal :=
  Angle.two_nsmul_toReal_eq_two_mul_sub_two_pi

theorem two_zsmul_toReal_eq_two_mul_sub_two_pi {θ : AngValue} :
    ((2 : ℤ) • θ).toReal = 2 * θ.toReal - 2 * π ↔ π / 2 < θ.toReal :=
  Angle.two_zsmul_toReal_eq_two_mul_sub_two_pi

theorem two_nsmul_toReal_eq_two_mul_add_two_pi {θ : AngValue} :
    ((2 : ℕ) • θ).toReal = 2 * θ.toReal + 2 * π ↔ θ.toReal ≤ -π / 2 :=
  Angle.two_nsmul_toReal_eq_two_mul_add_two_pi

theorem two_zsmul_toReal_eq_two_mul_add_two_pi {θ : AngValue} :
    ((2 : ℤ) • θ).toReal = 2 * θ.toReal + 2 * π ↔ θ.toReal ≤ -π / 2 :=
  Angle.two_zsmul_toReal_eq_two_mul_add_two_pi

@[simp]
theorem sin_toReal (θ : AngValue) : Real.sin θ.toReal = sin θ :=
  Angle.sin_toReal _

@[simp]
theorem cos_toReal (θ : AngValue) : Real.cos θ.toReal = cos θ :=
  Angle.cos_toReal _

theorem cos_nonneg_iff_abs_toReal_le_pi_div_two {θ : AngValue} : 0 ≤ cos θ ↔ |θ.toReal| ≤ π / 2 :=
  Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two

theorem cos_pos_iff_abs_toReal_lt_pi_div_two {θ : AngValue} : 0 < cos θ ↔ |θ.toReal| < π / 2 :=
  Angle.cos_pos_iff_abs_toReal_lt_pi_div_two

theorem cos_neg_iff_pi_div_two_lt_abs_toReal {θ : AngValue} : cos θ < 0 ↔ π / 2 < |θ.toReal| :=
  Angle.cos_neg_iff_pi_div_two_lt_abs_toReal

theorem abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : AngValue}
    (h : (2 : ℕ) • θ + (2 : ℕ) • ψ = π) : |cos θ| = |sin ψ| :=
  Angle.abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi h

theorem abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : AngValue}
    (h : (2 : ℤ) • θ + (2 : ℤ) • ψ = π) : |cos θ| = |sin ψ| :=
  Angle.abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi h

/-- The tangent of a `AngValue`. -/
def tan (θ : AngValue) : ℝ :=
  Angle.tan θ

theorem tan_eq_sin_div_cos (θ : AngValue) : tan θ = sin θ / cos θ :=
  rfl

@[simp]
theorem tan_coe (x : ℝ) : tan (x : AngValue) = Real.tan x :=
  Angle.tan_coe _

@[simp]
theorem tan_zero : tan (0 : AngValue) = 0 :=
  Angle.tan_zero

-- Porting note: @[simp] can now prove it
theorem tan_coe_pi : tan (π : AngValue) = 0 :=
  Angle.tan_coe_pi

theorem tan_periodic : Function.Periodic tan (π : AngValue) :=
  Angle.tan_periodic

@[simp]
theorem tan_add_pi (θ : AngValue) : tan (θ + π) = tan θ :=
  Angle.tan_add_pi _

@[simp]
theorem tan_sub_pi (θ : AngValue) : tan (θ - π) = tan θ :=
  Angle.tan_sub_pi _

@[simp]
theorem tan_toReal (θ : AngValue) : Real.tan θ.toReal = tan θ :=
  Angle.tan_toReal _

theorem tan_eq_of_two_nsmul_eq {θ ψ : AngValue} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) : tan θ = tan ψ :=
  Angle.tan_eq_of_two_nsmul_eq h

theorem tan_eq_of_two_zsmul_eq {θ ψ : AngValue} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) : tan θ = tan ψ :=
  Angle.tan_eq_of_two_zsmul_eq h

theorem tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : AngValue}
    (h : (2 : ℕ) • θ + (2 : ℕ) • ψ = π) : tan ψ = (tan θ)⁻¹ :=
  Angle.tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi h

theorem tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : AngValue}
    (h : (2 : ℤ) • θ + (2 : ℤ) • ψ = π) : tan ψ = (tan θ)⁻¹ :=
  Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi h

/-- The sign of a `AngValue` is `0` if the angle is `0` or `π`, `1` if the angle is strictly
between `0` and `π` and `-1` is the angle is strictly between `-π` and `0`. It is defined as the
sign of the sine of the angle. -/
def sign (θ : AngValue) : SignType :=
  Angle.sign θ

@[simp]
theorem sign_zero : (0 : AngValue).sign = 0 :=
  Angle.sign_zero

@[simp]
theorem sign_coe_pi : (π : AngValue).sign = 0 :=
  Angle.sign_coe_pi

@[simp]
theorem sign_neg (θ : AngValue) : (-θ).sign = -θ.sign :=
  Angle.sign_neg _

theorem sign_antiperiodic : Function.Antiperiodic sign (π : AngValue) :=
  Angle.sign_antiperiodic

@[simp]
theorem sign_add_pi (θ : AngValue) : (θ + π).sign = -θ.sign :=
  Angle.sign_add_pi _

@[simp]
theorem sign_pi_add (θ : AngValue) : ((π : AngValue) + θ).sign = -θ.sign :=
  Angle.sign_pi_add _

@[simp]
theorem sign_sub_pi (θ : AngValue) : (θ - π).sign = -θ.sign :=
  Angle.sign_sub_pi _

@[simp]
theorem sign_pi_sub (θ : AngValue) : ((π : AngValue) - θ).sign = θ.sign :=
  Angle.sign_pi_sub _

theorem sign_eq_zero_iff {θ : AngValue} : θ.sign = 0 ↔ θ = 0 ∨ θ = π :=
  Angle.sign_eq_zero_iff

theorem sign_ne_zero_iff {θ : AngValue} : θ.sign ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π :=
  Angle.sign_ne_zero_iff

theorem toReal_neg_iff_sign_neg {θ : AngValue} : θ.toReal < 0 ↔ θ.sign = -1 :=
  Angle.toReal_neg_iff_sign_neg

theorem toReal_nonneg_iff_sign_nonneg {θ : AngValue} : 0 ≤ θ.toReal ↔ 0 ≤ θ.sign :=
  Angle.toReal_nonneg_iff_sign_nonneg

@[simp]
theorem sign_toReal {θ : AngValue} (h : θ ≠ π) : SignType.sign θ.toReal = θ.sign :=
  Angle.sign_toReal h

theorem coe_abs_toReal_of_sign_nonneg {θ : AngValue} (h : 0 ≤ θ.sign) : ↑|θ.toReal| = θ :=
  Angle.coe_abs_toReal_of_sign_nonneg h

theorem neg_coe_abs_toReal_of_sign_nonpos {θ : AngValue} (h : θ.sign ≤ 0) : -↑|θ.toReal| = θ :=
  Angle.neg_coe_abs_toReal_of_sign_nonpos h

theorem eq_iff_sign_eq_and_abs_toReal_eq {θ ψ : AngValue} :
    θ = ψ ↔ θ.sign = ψ.sign ∧ |θ.toReal| = |ψ.toReal| :=
  Angle.eq_iff_sign_eq_and_abs_toReal_eq

theorem eq_iff_abs_toReal_eq_of_sign_eq {θ ψ : AngValue} (h : θ.sign = ψ.sign) :
    θ = ψ ↔ |θ.toReal| = |ψ.toReal| :=
  Angle.eq_iff_abs_toReal_eq_of_sign_eq h

@[simp]
theorem sign_coe_pi_div_two : (↑(π / 2) : AngValue).sign = 1 :=
  Angle.sign_coe_pi_div_two

@[simp]
theorem sign_coe_neg_pi_div_two : (↑(-π / 2) : AngValue).sign = -1 :=
  Angle.sign_coe_neg_pi_div_two

theorem sign_coe_nonneg_of_nonneg_of_le_pi {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
    0 ≤ (θ : AngValue).sign :=
  Angle.sign_coe_nonneg_of_nonneg_of_le_pi h0 hpi

theorem sign_neg_coe_nonpos_of_nonneg_of_le_pi {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
    (-θ : AngValue).sign ≤ 0 :=
  Angle.sign_neg_coe_nonpos_of_nonneg_of_le_pi h0 hpi

theorem sign_two_nsmul_eq_sign_iff {θ : AngValue} :
    ((2 : ℕ) • θ).sign = θ.sign ↔ θ = π ∨ |θ.toReal| < π / 2 :=
  Angle.sign_two_nsmul_eq_sign_iff

theorem sign_two_zsmul_eq_sign_iff {θ : AngValue} :
    ((2 : ℤ) • θ).sign = θ.sign ↔ θ = π ∨ |θ.toReal| < π / 2 :=
  Angle.sign_two_zsmul_eq_sign_iff

theorem continuousAt_sign {θ : AngValue} (h0 : θ ≠ 0) (hpi : θ ≠ π) : ContinuousAt sign θ :=
  Angle.continuousAt_sign h0 hpi

theorem _root_.ContinuousOn.angValue_sign_comp {α : Type*} [TopologicalSpace α] {f : α → AngValue}
    {s : Set α} (hf : ContinuousOn f s) (hs : ∀ z ∈ s, f z ≠ 0 ∧ f z ≠ π) :
    ContinuousOn (sign ∘ f) s :=
  ContinuousOn.angle_sign_comp hf hs

/-- Suppose a function to angles is continuous on a connected set and never takes the values `0`
or `π` on that set. Then the values of the function on that set all have the same sign. -/
theorem sign_eq_of_continuousOn {α : Type*} [TopologicalSpace α] {f : α → AngValue} {s : Set α}
    {x y : α} (hc : IsConnected s) (hf : ContinuousOn f s) (hs : ∀ z ∈ s, f z ≠ 0 ∧ f z ≠ π)
    (hx : x ∈ s) (hy : y ∈ s) : (f y).sign = (f x).sign :=
  Angle.sign_eq_of_continuousOn hc hf hs hx hy

end AngValue

end EuclidGeom

end Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

section Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace Complex

open ComplexConjugate EuclidGeom

@[simp]
theorem arg_conj_coe_angValue (x : ℂ) : (arg (conj x) : AngValue) = -arg x :=
  arg_conj_coe_angle _

@[simp]
theorem arg_inv_coe_angValue (x : ℂ) : (arg x⁻¹ : AngValue) = -arg x :=
  arg_inv_coe_angle _

theorem arg_neg_coe_angValue {x : ℂ} (hx : x ≠ 0) : (arg (-x) : AngValue) = arg x + π :=
  arg_neg_coe_angle hx

theorem arg_mul_cos_add_sin_mul_I_coe_angValue {r : ℝ} (hr : 0 < r) (θ : AngValue) :
    (arg (r * (AngValue.cos θ + AngValue.sin θ * I)) : AngValue) = θ :=
  arg_mul_cos_add_sin_mul_I_coe_angle hr _

@[simp]
theorem arg_cos_add_sin_mul_I_coe_angValue (θ : AngValue) :
    (arg (AngValue.cos θ + AngValue.sin θ * I) : AngValue) = θ :=
  arg_cos_add_sin_mul_I_coe_angle _

theorem arg_mul_coe_angValue {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (arg (x * y) : AngValue) = arg x + arg y :=
  arg_mul_coe_angle hx hy

theorem arg_div_coe_angValue {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (arg (x / y) : AngValue) = arg x - arg y :=
  arg_div_coe_angle hx hy

@[simp]
theorem arg_coe_angValue_toReal_eq_arg (z : ℂ) : (arg z : AngValue).toReal = arg z :=
  arg_coe_angle_toReal_eq_arg _

theorem arg_coe_angValue_eq_iff_eq_toReal {z : ℂ} {θ : AngValue} :
    (arg z : AngValue) = θ ↔ arg z = θ.toReal :=
  arg_coe_angle_eq_iff_eq_toReal

@[simp]
theorem arg_coe_angValue_eq_iff {x y : ℂ} : (arg x : AngValue) = arg y ↔ arg x = arg y :=
  arg_coe_angle_eq_iff

theorem continuousAt_arg_coe_angValue (h : x ≠ 0) : ContinuousAt ((↑) ∘ arg : ℂ → AngValue) x :=
  continuousAt_arg_coe_angle h

end Complex

end Mathlib.Analysis.SpecialFunctions.Complex.Arg

section Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace EuclidGeom

open Complex

/-- `expMapCircle`, applied to a `AngValue`. -/
noncomputable def AngValue.expMapCircle (θ : AngValue) : circle :=
  Angle.expMapCircle θ

@[simp]
theorem AngValue.expMapCircle_coe (x : ℝ) : AngValue.expMapCircle x = _root_.expMapCircle x :=
  rfl

theorem AngValue.coe_expMapCircle (θ : AngValue) :
    (θ.expMapCircle : ℂ) = θ.cos + θ.sin * I :=
  Angle.coe_expMapCircle θ

@[simp]
theorem AngValue.expMapCircle_zero : AngValue.expMapCircle 0 = 1 :=
  Angle.expMapCircle_zero

@[simp]
theorem AngValue.expMapCircle_neg (θ : AngValue) :
    AngValue.expMapCircle (-θ) = (AngValue.expMapCircle θ)⁻¹ :=
  Angle.expMapCircle_neg θ

@[simp]
theorem AngValue.expMapCircle_add (θ₁ θ₂ : AngValue) : AngValue.expMapCircle (θ₁ + θ₂) =
    AngValue.expMapCircle θ₁ * AngValue.expMapCircle θ₂ :=
  Angle.expMapCircle_add θ₁ θ₂

@[simp]
theorem AngValue.arg_expMapCircle (θ : AngValue) :
    (arg (AngValue.expMapCircle θ) : AngValue) = θ :=
  Angle.arg_expMapCircle θ

end EuclidGeom

end Mathlib.Analysis.SpecialFunctions.Complex.Circle
