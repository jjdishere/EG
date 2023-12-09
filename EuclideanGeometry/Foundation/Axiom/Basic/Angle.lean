import EuclideanGeometry.Foundation.Axiom.Basic.Angle.FromMathlib
/-!
# Angle Conversions

Recall in Euclidean Geometry, the measure of angle is subtle. The measure of an angle can be treated as a number in `ℝ⧸2π`, `(-π, π]`, `[0, 2π)`, `ℝ⧸π`, or even `[0, π]` (after taking abs). Each of them has their own suitable applications.
* `ℝ⧸2π` : add and sub of angles, angle between dirrcted object;
* `(-π, π]` : measure of oriented angle, angles of a triangle, positions;
* `[0, 2π)` : length of arc, central angle;
* `ℝ⧸π` : measure of directed angle when discussing four points concyclic, angle between lines
* `[0, π]` : cosine theorem, undirected angles.

In this file, we define suitable coversion function between `ℝ⧸2π`,`ℝ⧸π` and `(-π, π]`. Starting from `Dir.toAngValue`, we convert `Dir` to `AngValue`. We shall primarily use `ℝ/2π`, and gives coercion and compatibility theorems with respect to `ℝ⧸π` and `(-π, π]`.

-/
open Real.Angle Classical

noncomputable section

namespace EuclidGeom

section Notation -- no need to open Real when using `π`
open Lean

syntax (name := piNotation) (priority := high) "π" : term

@[macro piNotation] def piNotationImpl : Macro
  | `(π) => `(Real.pi)
  | _ => Macro.throwUnsupported

end Notation

open Real

def AngDValue := AddCircle π

namespace AngDValue

instance : NormedAddCommGroup AngDValue :=
  inferInstanceAs (NormedAddCommGroup (AddCircle π))

instance : Inhabited AngDValue :=
  inferInstanceAs (Inhabited (AddCircle π))

@[coe]
def _root_.EuclidGeom.AngValue.toAngDValue' : AngValue → AngDValue :=
  Quotient.map' id (by
    rintro _ _ ⟨⟨v, ⟨k, hv⟩⟩, h⟩
    exact ⟨⟨v, ⟨k * 2, by simpa [mul_assoc] using hv⟩⟩, h⟩)

instance : Coe AngValue AngDValue where
  coe := AngValue.toAngDValue'

def _root_.EuclidGeom.AngValue.toAngDValue : AngValue →+ AngDValue where
  toFun := (↑)
  map_zero' := rfl
  map_add' θ ψ := by
    induction θ using AngValue.induction_on
    induction ψ using AngValue.induction_on
    rfl

instance : CircularOrder AngDValue :=
  QuotientAddGroup.circularOrder (hp' := ⟨by norm_num [pi_pos]⟩)

theorem coe_def (x : ℝ) : (x : AngDValue) = QuotientAddGroup.mk x :=
  rfl

@[continuity]
theorem continuous_coe : Continuous ((↑) : ℝ → AngDValue) :=
  continuous_quotient_mk'

/-- Coercion `ℝ → AngDValue` as an additive homomorphism. -/
def coeHom : ℝ →+ AngDValue :=
  QuotientAddGroup.mk' _

@[simp]
theorem coe_coeHom : (coeHom : ℝ → AngDValue) = ((↑) : ℝ → AngDValue) :=
  rfl

/-- An induction principle to deduce results for `AngDValue` from those for `ℝ`, used with
`induction θ using AngDValue.induction_on`. -/
@[elab_as_elim]
protected theorem induction_on {p : AngDValue → Prop} (θ : AngDValue) (h : ∀ x : AngValue, p x) : p θ :=
  Quotient.inductionOn' θ (fun x ↦ h x)

@[simp, norm_cast]
theorem coe_zero : ↑(0 : AngValue) = (0 : AngDValue) :=
  rfl

section dsimp

@[simp, nolint simpNF]
theorem coe_add_coe (x y : ℝ) : ↑(x + y : AngValue) = (↑x + ↑y : AngDValue) :=
  rfl

@[simp, nolint simpNF]
theorem coe_neg_coe (x : ℝ) : ↑(-x : AngValue) = -(↑x : AngDValue) :=
  rfl

@[simp, nolint simpNF]
theorem coe_sub_coe (x y : ℝ) : ↑(x - y : AngValue) = (↑x - ↑y : AngDValue) :=
  rfl

@[simp, nolint simpNF]
theorem coe_nsmul_coe (n : ℕ) (x : ℝ) : ↑(n • x : AngValue) = n • (↑x : AngDValue) :=
  rfl

@[simp, nolint simpNF]
theorem coe_zsmul_coe (z : ℤ) (x : ℝ) : ↑(z • x : AngValue) = z • (↑x : AngDValue) :=
  rfl

end dsimp

@[simp, norm_cast]
theorem coe_add (x y : AngValue) : ↑(x + y : AngValue) = (↑x + ↑y : AngDValue) := by
  induction x using AngValue.induction_on
  induction y using AngValue.induction_on
  rfl

@[simp, norm_cast]
theorem coe_neg (x : AngValue) : ↑(-x : AngValue) = -(↑x : AngDValue) := by
  induction x using AngValue.induction_on
  rfl

@[simp, norm_cast]
theorem coe_sub (x y : AngValue) : ↑(x - y : AngValue) = (↑x - ↑y : AngDValue) := by
  induction x using AngValue.induction_on
  induction y using AngValue.induction_on
  rfl

@[simp, norm_cast]
theorem coe_nsmul (n : ℕ) (x : AngValue) : ↑(n • x : AngValue) = n • (↑x : AngDValue) := by
  induction x using AngValue.induction_on
  rfl

@[simp, norm_cast]
theorem coe_zsmul (z : ℤ) (x : AngValue) : ↑(z • x : AngValue) = z • (↑x : AngDValue) := by
  induction x using AngValue.induction_on
  rfl

theorem eq_iff_pi_dvd_sub {ψ θ : ℝ} : (θ : AngDValue) = ψ ↔ ∃ k : ℤ, θ - ψ = π * k := by
  simp only [QuotientAddGroup.eq, AddSubgroup.zmultiples_eq_closure,
    AddSubgroup.mem_closure_singleton, zsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]
  -- Porting note: added `rw`, `simp [Angle.coe, QuotientAddGroup.eq]` doesn't fire otherwise
  rw [AngDValue.coe_def, AngDValue.coe_def, QuotientAddGroup.eq]
  simp only [AddSubgroup.zmultiples_eq_closure,
    AddSubgroup.mem_closure_singleton, zsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]

@[simp]
theorem coe_pi : ↑(π : ℝ) = (0 : AngDValue) :=
  eq_iff_pi_dvd_sub.2 ⟨1, by rw [sub_zero, Int.cast_one, mul_one]⟩

@[simp]
theorem neg_coe_pi_div_two : -((π / 2 : ℝ) : AngDValue) = ↑(π / 2 : ℝ) := by
  rw [← coe_neg, ← AngValue.coe_neg, eq_iff_pi_dvd_sub]
  use -1
  simp [two_mul, sub_eq_add_neg, ← neg_div]

@[simp]
theorem two_nsmul_coe_div_two (θ : ℝ) : (2 : ℕ) • (↑(θ / 2) : AngDValue) = θ := by
  rw [← coe_nsmul, two_nsmul, ← AngValue.coe_add, add_halves]

@[simp]
theorem two_zsmul_coe_div_two (θ : ℝ) : (2 : ℤ) • (↑(θ / 2) : AngDValue) = θ := by
  rw [← coe_zsmul, two_zsmul, ← AngValue.coe_add, add_halves]

theorem coe_eq_coe_iff {θ₁ θ₂ : AngValue} :
    (θ₁ : AngDValue) = (θ₂ : AngDValue) ↔ θ₁ = θ₂ ∨ θ₁ = θ₂ + π := by
  induction' θ₁ using AngValue.induction_on with x₁
  induction' θ₂ using AngValue.induction_on with x₂
  rw [eq_iff_pi_dvd_sub, AngValue.eq_iff_two_pi_dvd_sub, ← AngValue.coe_add, AngValue.eq_iff_two_pi_dvd_sub]
  constructor
  · rintro ⟨x, h⟩
    simp_rw [← sub_sub, h]
    obtain ⟨x, (rfl | rfl)⟩ := x.even_or_odd'
    · exact .inl ⟨x, by push_cast; ring⟩
    · exact .inr ⟨x, by push_cast; ring⟩
  · rintro (⟨x, h⟩ | ⟨x, h⟩)
    · simp_rw [h]
      exact ⟨2 * x, by push_cast; ring⟩
    · rw [← sub_sub, sub_eq_iff_eq_add] at h
      simp_rw [h]
      exact ⟨2 * x + 1, by push_cast; ring⟩

@[simp]
lemma coe_add_pi (v : AngValue) : ↑(v + π) = (v : AngDValue) := by
  rw [coe_eq_coe_iff]
  exact .inr rfl

protected abbrev lift {α : Sort*} (f : AngValue → α) (hf : ∀ θ, f (θ + π) = f θ) : AngDValue → α :=
  Quotient.lift (fun v : ℝ ↦ f v) fun (v₁ v₂ : ℝ) h ↦ (by
    replace h : (v₁ : AngDValue) = (v₂ : AngDValue)
    · simpa using Quotient.sound h
    obtain (h | h) := coe_eq_coe_iff.mp h <;>
      simp [h, hf])

def _root_.Real.toAngDValue : ℝ →+ AngDValue :=
  AngValue.toAngDValue.comp AngValue.coeHom

end AngDValue


namespace AngValue

section pos_neg_isnd

@[pp_dot]
def IsPos (θ : AngValue) : Prop := sbtw 0 θ π

@[pp_dot]
def IsNeg (θ : AngValue) : Prop := sbtw (π : AngValue) θ 0

@[pp_dot]
structure IsND (θ : AngValue) : Prop where intro ::
  ne_zero : θ ≠ 0
  ne_pi : θ ≠ π

section special_value

theorem zero_not_isPos : ¬ (0 : AngValue).IsPos := sbtw_irrefl_left

theorem zero_not_isNeg : ¬ (0 : AngValue).IsNeg := sbtw_irrefl_right

theorem zero_not_isnd : ¬ (0 : AngValue).IsND := fun nd ↦ nd.1 rfl

theorem not_isPos_of_eq_zero {θ : AngValue} (h : θ = 0) : ¬ θ.IsPos := by
  rw [h]
  exact zero_not_isPos

theorem ne_zero_of_isPos {θ : AngValue} (h : θ.IsPos) : θ ≠ 0 := fun hs ↦ not_isPos_of_eq_zero hs h

theorem not_isNeg_of_eq_zero {θ : AngValue} (h : θ = 0) : ¬ θ.IsNeg :=  by
  rw [h]
  exact zero_not_isNeg

theorem ne_zero_of_isNeg {θ : AngValue} (h : θ.IsNeg) : θ ≠ 0 := fun hs ↦ not_isNeg_of_eq_zero hs h

theorem not_isnd_of_eq_zero {θ : AngValue} (h : θ = 0) : ¬ θ.IsND := fun nd ↦ nd.1 h

theorem pi_not_isPos : ¬ (π : AngValue).IsPos := sbtw_irrefl_right

theorem pi_not_isNeg : ¬ (π : AngValue).IsNeg := sbtw_irrefl_left

theorem pi_not_isnd : ¬ (π : AngValue).IsND := fun nd ↦ nd.2 rfl

theorem not_isPos_of_eq_pi {θ : AngValue} (h : θ = π) : ¬ θ.IsPos :=  by
  rw [h]
  exact pi_not_isPos

theorem ne_pi_of_isPos {θ : AngValue} (h : θ.IsPos) : θ ≠ π := fun hs ↦ not_isPos_of_eq_pi hs h

theorem not_isNeg_of_eq_pi {θ : AngValue} (h : θ = π) : ¬ θ.IsNeg :=  by
  rw [h]
  exact pi_not_isNeg

theorem ne_pi_of_isNeg {θ : AngValue} (h : θ.IsNeg) : θ ≠ π := fun hs ↦ not_isNeg_of_eq_pi hs h

theorem not_isnd_of_eq_pi {θ : AngValue} (h : θ = π) : ¬ θ.IsND := fun nd ↦ nd.2 h

theorem isnd_iff {θ : AngValue} : θ.IsND ↔ θ ≠ 0 ∧ θ ≠ π :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

theorem not_isnd_iff {θ : AngValue} : ¬ θ.IsND ↔ (θ = 0 ∨ θ = π) :=
  (not_iff_not.mpr θ.isnd_iff).trans or_iff_not_and_not.symm

theorem isnd_iff_two_nsmul_ne_zero {θ : AngValue} : θ.IsND ↔ 2 • θ ≠ 0 :=
  (θ.isnd_iff).trans (θ.two_nsmul_ne_zero_iff).symm

theorem not_isnd_iff_two_nsmul_eq_zero {θ : AngValue} : ¬ θ.IsND ↔ 2 • θ = 0 :=
  (θ.not_isnd_iff).trans (θ.two_nsmul_eq_zero_iff).symm

end special_value

section trichotomy

theorem not_isNeg_of_isPos {θ : AngValue} (h : θ.IsPos) : ¬ θ.IsNeg := sbtw_asymm h

theorem isnd_of_isPos {θ : AngValue} (h : θ.IsPos) : θ.IsND where
  ne_zero hs := not_isPos_of_eq_zero hs h
  ne_pi hs := not_isPos_of_eq_pi hs h

theorem not_isPos_of_isNeg {θ : AngValue} (h : θ.IsNeg) : ¬ θ.IsPos := sbtw_asymm h

theorem isnd_of_isNeg {θ : AngValue} (h : θ.IsNeg) : θ.IsND where
  ne_zero hs := not_isNeg_of_eq_zero hs h
  ne_pi hs := not_isNeg_of_eq_pi hs h

theorem not_isPos_of_not_isnd {θ : AngValue} (h : ¬ θ.IsND) : ¬ θ.IsPos := fun hs ↦ h (isnd_of_isPos hs)

theorem not_isNeg_of_not_isnd {θ : AngValue} (h : ¬ θ.IsND) : ¬ θ.IsNeg := fun hs ↦ h (isnd_of_isNeg hs)

theorem isPos_or_isNeg_of_isnd {θ : AngValue} (h : θ.IsND) : θ.IsPos ∨ θ.IsNeg := by
  contrapose! h
  have h := (and_congr btw_iff_not_sbtw btw_iff_not_sbtw).mpr h
  rcases btw_antisymm (btw_cyclic_right h.1) (btw_cyclic_left h.2) with h | h
  · exact (pi_ne_zero h.symm).elim
  · exact not_isnd_iff.mpr (Or.comm.mp ((or_congr_left eq_comm).mp h))

theorem not_isnd_or_isPos_or_isNeg {θ : AngValue} : ¬ θ.IsND ∨ θ.IsPos ∨ θ.IsNeg :=
  if h : θ.IsND then .inr (isPos_or_isNeg_of_isnd h) else .inl h

end trichotomy

section toReal


theorem zero_le_toReal_iff {θ : AngValue} : 0 ≤ θ.toReal ↔ btw 0 θ π := by
  have hp : Fact (0 < 2 * π) := { out := Real.two_pi_pos }
  rw [← neg_coe_pi, ← θ.coe_toReal]
  refine' Iff.trans _ btw_cyclic.symm
  refine' (Eq.to_iff _).trans QuotientAddGroup.btw_coe_iff.symm
  congr
  refine' ((toIcoMod_eq_self hp.1).mpr _).symm
  rw [neg_add_eq_of_eq_add (two_mul π)]
  exact ⟨neg_nonpos.mpr (le_of_lt Real.pi_pos), Real.pi_pos⟩

theorem zero_le_toReal_of_isPos {θ : AngValue} (h : θ.IsPos) : 0 ≤ θ.toReal :=
  zero_le_toReal_iff.mpr (btw_of_sbtw h)

theorem zero_lt_toReal_of_isPos {θ : AngValue} (h : θ.IsPos) : 0 < θ.toReal :=
  (Ne.symm <| toReal_eq_zero_iff.not.mpr (ne_zero_of_isPos h)).lt_of_le (zero_le_toReal_of_isPos h)

theorem toReal_lt_pi_of_isPos {θ : AngValue} (h : θ.IsPos) : θ.toReal < π :=
  lt_of_le_of_ne (toReal_le_pi _) (toReal_eq_pi_iff.not.mpr (ne_pi_of_isPos h))

theorem toReal_lt_zero_of_isNeg {θ : AngValue} (h : θ.IsNeg) : θ.toReal < 0 := by
  contrapose! h
  exact not_sbtw_of_btw (zero_le_toReal_iff.mp h)

theorem toReal_le_zero_of_isNeg {θ : AngValue} (h : θ.IsNeg) : θ.toReal ≤ 0 :=
  le_of_lt (toReal_lt_zero_of_isNeg h)

theorem isPos_of_zero_lt_toReal_of_ne_pi {θ : AngValue} (h : 0 < θ.toReal) (hn : θ ≠ π) : θ.IsPos :=
  Or.casesOn (isPos_or_isNeg_of_isnd ⟨toReal_eq_zero_iff.not.mp (ne_of_gt h), hn⟩)
    id (fun hp ↦ (not_lt_of_ge (toReal_le_zero_of_isNeg hp) h).elim)

theorem isNeg_of_toReal_lt_zero {θ : AngValue} (h : θ.toReal < 0) : θ.IsNeg := by
  contrapose! h
  exact zero_le_toReal_iff.mpr (btw_iff_not_sbtw.mpr h)

theorem isPos_iff {θ : AngValue} : θ.IsPos ↔ (0 < θ.toReal ∧ (θ.toReal < π)) := ⟨
  fun h ↦ ⟨zero_lt_toReal_of_isPos h, toReal_lt_pi_of_isPos h⟩,
  fun h ↦ isPos_of_zero_lt_toReal_of_ne_pi h.1 (toReal_eq_pi_iff.not.mp (ne_of_lt h.2))⟩

theorem not_isPos_iff {θ : AngValue} : ¬ θ.IsPos ↔ (θ.toReal ≤ 0 ∨ θ.toReal = π) :=
  (θ.isPos_iff).not.trans (by simp only [not_and_or, not_lt, ge_iff_le, (θ.toReal_le_pi).ge_iff_eq])

theorem isNeg_iff {θ : AngValue} : θ.IsNeg ↔ (θ.toReal < 0) :=
  ⟨toReal_lt_zero_of_isNeg, isNeg_of_toReal_lt_zero⟩

theorem not_isNeg_iff {θ : AngValue} : ¬ θ.IsNeg ↔ (0 ≤ θ.toReal) := (θ.isNeg_iff).not.trans not_lt

theorem isnd_iff' {θ : AngValue} : θ.IsND ↔ (θ.toReal ≠ 0 ∧ θ.toReal ≠ π) := ⟨
  fun h ↦ ⟨toReal_eq_zero_iff.not.mpr h.1, toReal_eq_pi_iff.not.mpr h.2⟩,
  fun h ↦ ⟨toReal_eq_zero_iff.not.mp h.1 ,toReal_eq_pi_iff.not.mp h.2⟩⟩

theorem not_isnd_iff' {θ : AngValue} : ¬ θ.IsND ↔ (θ.toReal = 0 ∨ θ.toReal = π) :=
  isnd_iff'.not.trans (not_and_or.trans (or_congr not_ne_iff not_ne_iff))

end toReal

section sin

theorem zero_lt_sin_of_isPos {θ : AngValue} (h : θ.IsPos) : 0 < sin θ := sorry

theorem isPos_of_zero_lt_sin {θ : AngValue} (h : 0 < sin θ) : θ.IsPos := sorry

theorem zero_lt_sin_iff_isPos {θ : AngValue} : θ.IsPos ↔ 0 < sin θ :=
  ⟨zero_lt_sin_of_isPos, isPos_of_zero_lt_sin⟩

theorem sin_lt_zero_of_isNeg {θ : AngValue} (h : θ.IsNeg) : sin θ < 0 := sorry

theorem isNeg_of_sin_lt_zero {θ : AngValue} (h : sin θ < 0) : θ.IsNeg := sorry

theorem zero_lt_sin_iff_isNeg {θ : AngValue} : θ.IsNeg ↔ sin θ < 0 :=
  ⟨sin_lt_zero_of_isNeg, isNeg_of_sin_lt_zero⟩

theorem isnd_iff_sin_ne_zero {θ : AngValue} : θ.IsND ↔ sin θ ≠ 0 := sorry

theorem not_isnd_iff_sin_eq_zero {θ : AngValue} : ¬ θ.IsND ↔ sin θ = 0 := sorry

end sin

section neg

theorem neg_isNeg_of_isPos {θ : AngValue} (h : θ.IsPos) : (-θ).IsNeg := sorry

theorem neg_isPos_of_isNeg {θ : AngValue} (h : θ.IsNeg) : (-θ).IsPos := sorry

theorem neg_isnd_of_isnd {θ : AngValue} (h : θ.IsND) : (-θ).IsND := sorry

theorem isNeg_of_neg_isPos {θ : AngValue} (h : (-θ).IsPos) : θ.IsNeg := sorry

theorem isPos_of_neg_isNeg {θ : AngValue} (h : (-θ).IsNeg) : θ.IsPos := sorry

theorem isnd_of_neg_isnd {θ : AngValue} (h : (-θ).IsND) : θ.IsND := sorry

@[simp]
theorem neg_isPos_iff_isNeg {θ : AngValue} : (-θ).IsPos ↔ θ.IsNeg := sorry

@[simp]
theorem neg_isNeg_iff_isPos {θ : AngValue} : (-θ).IsNeg ↔ θ.IsPos := sorry

@[simp]
theorem neg_isnd_iff_isnd {θ : AngValue} : (-θ).IsND ↔ θ.IsND := sorry

end neg

end pos_neg_isnd

-- `Do we prepare is acute, is right, ... here?` `To be added`
section acute_obtuse_right

@[pp_dot]
def IsAcu (θ : AngValue) : Prop := sbtw ((- π / 2 : ℝ) : AngValue) θ  (π / 2 : ℝ)

@[pp_dot]
def IsObt (θ : AngValue) : Prop := sbtw ((π / 2 : ℝ) : AngValue) θ (- π / 2 : ℝ)

@[pp_dot]
def IsRight (θ : AngValue) : Prop := θ = ((- π / 2 : ℝ) : AngValue) ∨ θ = ((π / 2 : ℝ) : AngValue)

section special_value

-- Special values for 0, π, π / 2 and - π / 2

end special_value

section trichotomy

theorem not_isobt_of_isacu {θ : AngValue} (h : θ.IsAcu) : ¬ θ.IsObt := sbtw_asymm h

theorem isright_of_isacu {θ : AngValue} (h : θ.IsAcu) : ¬ θ.IsRight := sorry

theorem not_isacu_of_isNeg {θ : AngValue} (h : θ.IsObt) : ¬ θ.IsAcu := sbtw_asymm h

theorem isright_of_isNeg {θ : AngValue} (h : θ.IsObt) : ¬ θ.IsRight := sorry

theorem not_isacu_of_not_isright {θ : AngValue} (h : θ.IsRight) : ¬ θ.IsAcu :=
  fun hs ↦ (isright_of_isacu hs) h

theorem not_isNeg_of_not_isright {θ : AngValue} (h : θ.IsRight) : ¬ θ.IsObt :=
  fun hs ↦ (isright_of_isNeg hs) h

theorem isacu_or_isNeg_of_isright {θ : AngValue} (h : ¬ θ.IsRight) : θ.IsAcu ∨ θ.IsObt := sorry

theorem not_isright_or_isacu_or_isNeg {θ : AngValue} : θ.IsRight ∨ θ.IsAcu ∨ θ.IsObt :=
  if h : θ.IsRight then .inl h else .inr (isacu_or_isNeg_of_isright h)

end trichotomy

section toReal

theorem isacu_iff {θ : AngValue} : θ.IsAcu ↔ - π / 2 < θ.toReal ∧ θ.toReal < π / 2 := sorry

theorem isobt_iff {θ : AngValue} : θ.IsObt ↔  θ.toReal < - π / 2 ∨ π / 2 < θ.toReal := sorry

theorem isright_iff' {θ : AngValue} : θ.IsRight ↔ θ.toReal = - π / 2 ∨ θ.toReal = π / 2 := sorry

theorem not_isright_iff' {θ : AngValue} : ¬ θ.IsRight ↔ θ.toReal ≠ - π / 2 ∧ θ.toReal ≠ π / 2 := sorry

end toReal

section cos

theorem zero_lt_cos_iff_isacu {θ : AngValue} : θ.IsAcu ↔ 0 < cos θ := sorry

theorem zero_lt_cos_iff_isobt {θ : AngValue} : θ.IsObt ↔ sin θ < 0 := sorry

theorem isright_iff_sin_eq_zero {θ : AngValue} : θ.IsRight ↔ cos θ = 0 := sorry

theorem not_isright_iff_cos_ne_zero {θ : AngValue} : ¬ θ.IsRight ↔ cos θ ≠ 0 := sorry

end cos

section neg

@[simp]
theorem neg_isacu_iff_isacu {θ : AngValue} : (-θ).IsAcu ↔ θ.IsAcu := sorry

@[simp]
theorem neg_isobt_iff_isobt {θ : AngValue} : (-θ).IsObt ↔ θ.IsObt := sorry

@[simp]
theorem neg_isright_iff_isright {θ : AngValue} : (-θ).IsRight ↔ θ.IsRight := sorry

end neg

end acute_obtuse_right

end AngValue
-- `a section discussing cos sin, uniqueness with pos neg`
-- `sin >0 implies angle > 0, cos >0 implies ..., sin = 0 implies ...`
-- `acute, ... also implies uniqueness`
-- sin cos of special values is already at simp


section trigonometric

theorem pos_angle_eq_angle_iff_cos_eq_cos (ang₁ ang₂ : AngValue) (hang₁ : ang₁.IsPos) (hang₂ : ang₂.IsPos) : cos ang₁ = cos ang₂ ↔ ang₁ = ang₂ := by
  rw [Real.Angle.cos_eq_iff_eq_or_eq_neg]
  constructor
  intro e
  rcases e with e₁ | e₂
  · exact e₁
  · exfalso
    exact AngValue.not_isNeg_of_isPos hang₁ (e₂ ▸ AngValue.neg_isNeg_of_isPos hang₂)
  exact .inl

theorem neg_angle_eq_angle_iff_cos_eq_cos (ang₁ ang₂ : AngValue) (hang₁ : ang₁.IsNeg) (hang₂ : ang₂.IsNeg) : cos ang₁ = cos ang₂ ↔ ang₁ = ang₂ := by
  rw [Real.Angle.cos_eq_iff_eq_or_eq_neg]
  constructor
  intro e
  rcases e with e₁ | e₂
  · exact e₁
  · exfalso
    exact AngValue.not_isPos_of_isNeg hang₁ (e₂ ▸ AngValue.neg_isPos_of_isNeg hang₂)
  exact .inl

end trigonometric

section angdvalue

-- `Choose one to use.`
def AngDValue.Double : AngDValue → AngValue := AddCircle.equivAddCircle π (2 * π) (Real.pi_ne_zero) (by norm_num [Real.pi_ne_zero])
-- def AngDValue.Double : AngDValue → AngValue := Quotient.lift (fun x : ℝ => Real.toAngValue (2 * x)) sorry

-- `Do we need a AngValue.Halve function?`

section angvalue_angdvalue_compatibility
-- `This section needs following theorems @[simp] direction is always to target`
-- AngValue.toAngDValue special value 0 pi/2 pi -pi/2
-- AngValue.toAngDValue is group hom (add neg sub nsmul zsmul), ↑x = ↑y iff x = y or x = y + pi
-- AngDValue.Double special value
-- AngDValue.Double is group hom (add neg sub nsmul zsmul) (use AddCircle.equivAddCircle)
-- composites of these two map

end angvalue_angdvalue_compatibility

section real_angdvalue_compatibility
-- `see section real_angvalue_compatibility, but we do not allow a function from AngDValue to Real`
end real_angdvalue_compatibility

/-
--This is not needed, only a diagram commute is needed
def AddDir.toAngDValue : Additive Dir →+ AngDValue where
  toFun := fun d => AngValue.toAngDValue (Complex.arg (d : Dir).1 : Real.Angle)
  map_zero' := by
    have : (1 : Dir) = (0 : Additive Dir) := rfl
    simp only [this ▸ Dir.one_eq_one_toComplex, Complex.arg_one, coe_zero]
    rfl
  map_add' _ _:= by sorry

def Dir.toAngDValue : Dir → AngDValue := fun d => AddDir.toAngDValue d
-/

end angdvalue


namespace AngValue

section half

def half (θ : AngValue) : AngValue := (2⁻¹ : ℝ) * θ.toReal

theorem smul_two_half {θ : AngValue} : 2 • θ.half = θ := by
  unfold half
  norm_cast
  simp

theorem sub_half_eq_half {θ : AngValue} : θ - θ.half = θ.half :=
  sub_eq_of_eq_add (smul_two_half.symm.trans (two_nsmul θ.half))

theorem half_toReal {θ : AngValue} : θ.half.toReal = 2⁻¹ * θ.toReal := by
  rw [half, toReal_coe, toIocMod_eq_self]
  simp
  have := θ.neg_pi_lt_toReal
  have := θ.toReal_le_pi
  constructor <;>
  · field_simp
    linarith

theorem half_toReal_le_two_inv_mul_pi {θ : AngValue} : θ.half.toReal ≤ 2⁻¹ * π := by
  rw [θ.half_toReal]
  exact (mul_le_mul_left (by norm_num)).mpr θ.toReal_le_pi

theorem neg_two_inv_mul_pi_lt_half_toReal {θ : AngValue} : - 2⁻¹ * π < θ.half.toReal := by
  rw [θ.half_toReal, neg_mul_comm]
  exact (mul_lt_mul_left (by norm_num)).mpr θ.neg_pi_lt_toReal

end half

section abs

def abs (θ : AngValue) : ℝ := |θ.toReal|

theorem zero_le_abs {θ : AngValue} : 0 ≤ θ.abs := abs_nonneg θ.toReal

theorem abs_le_pi {θ : AngValue} : θ.abs ≤ π := abs_toReal_le_pi θ

theorem abs_eq_toReal_of_not_isNeg {θ : AngValue} (h : ¬ θ.IsNeg) : θ.abs = θ.toReal :=
  abs_eq_self.mpr (not_isNeg_iff.mp h)

theorem abs_eq_toReal_of_isPos {θ : AngValue} (h : θ.IsPos) : θ.abs = θ.toReal :=
  abs_eq_toReal_of_not_isNeg (not_isNeg_of_isPos h)

theorem abs_eq_toReal_of_isnd {θ : AngValue} (h : ¬ θ.IsND) : θ.abs = θ.toReal :=
  abs_eq_toReal_of_not_isNeg (not_isNeg_of_not_isnd h)

theorem abs_eq_neg_toReal_of_isNeg {θ : AngValue} (h : θ.IsNeg) : θ.abs = - θ.toReal :=
  abs_of_neg (isNeg_iff.mp h)

theorem not_isNeg_of_abs_eq_toReal {θ : AngValue} (h : θ.abs = θ.toReal) : ¬ θ.IsNeg :=
  not_isNeg_iff.mpr (abs_eq_self.mp h)

theorem abs_eq_toReal_iff {θ : AngValue} : θ.abs = θ.toReal ↔ ¬ θ.IsNeg :=
  ⟨not_isNeg_of_abs_eq_toReal, abs_eq_toReal_of_not_isNeg⟩

theorem abs_ne_toReal_iff {θ : AngValue} : θ.abs ≠ θ.toReal ↔ θ.IsNeg :=
  (θ.abs_eq_toReal_iff).not.trans not_not

end abs

end AngValue

end EuclidGeom
