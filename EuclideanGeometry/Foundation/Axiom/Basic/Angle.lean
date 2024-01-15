import EuclideanGeometry.Foundation.Axiom.Basic.Angle.AddToMathlib
import Mathlib.Data.Int.Parity
/-!
# Angle Conversions

Recall in Euclidean Geometry, the measure of angle is subtle. The measure of an angle can be treated as a number in `ℝ⧸2π`, `(- π, π]`, `[0, 2π)`, `ℝ⧸π`, or even `[0, π]` (after taking abs). Each of them has their own suitable applications.
* `ℝ⧸2π` : add and sub of angles, angle between dirrcted object;
* `(- π, π]` : measure of oriented angle, angles of a triangle, positions;
* `[0, 2π)` : length of arc, central angle;
* `ℝ⧸π` : measure of directed angle when discussing four points concyclic, angle between lines
* `[0, π]` : cosine theorem, undirected angles.

In this file, we define suitable coversion function between `ℝ⧸2π`,`ℝ⧸π` and `(- π, π]`. Starting from `Dir.toAngValue`, we convert `Dir` to `AngValue`. We shall primarily use `ℝ/2π`, and gives coercion and compatibility theorems with respect to `ℝ⧸π` and `(- π, π]`.

-/

noncomputable section

attribute [ext] Complex.ext

namespace EuclidGeom

open AngValue Classical Real

attribute [pp_dot] AngValue.toReal

def AngDValue := AddCircle π

namespace AngDValue

instance : NormedAddCommGroup AngDValue :=
  inferInstanceAs (NormedAddCommGroup (AddCircle π))

instance : Inhabited AngDValue :=
  inferInstanceAs (Inhabited (AddCircle π))

instance instCircularOrderedAddCommGroup : CircularOrderedAddCommGroup AngDValue :=
  haveI hp : Fact (0 < π) := ⟨pi_pos⟩
  QuotientAddGroup.instCircularOrderedAddCommGroup ℝ

@[coe]
def _root_.EuclidGeom.AngValue.toAngDValue : AngValue → AngDValue :=
  Quotient.map' id (by
    rintro _ _ ⟨⟨v, ⟨k, hv⟩⟩, h⟩
    exact ⟨⟨v, ⟨k * 2, by simpa [mul_assoc] using hv⟩⟩, h⟩)

instance : Coe AngValue AngDValue where
  coe := AngValue.toAngDValue

def _root_.EuclidGeom.AngValue.toAngDValueHom : AngValue →+ AngDValue where
  toFun := (↑)
  map_zero' := rfl
  map_add' θ ψ := by
    induction θ using AngValue.induction_on
    induction ψ using AngValue.induction_on
    rfl

instance : CircularOrder AngDValue :=
  QuotientAddGroup.circularOrder (hp' := ⟨by positivity⟩)

theorem coe_def (x : ℝ) : (x : AngDValue) = QuotientAddGroup.mk x :=
  rfl

@[continuity]
theorem continuous_coe : Continuous ((↑) : ℝ → AngDValue) :=
  continuous_quotient_mk'

/-- Coercion `ℝ → AngDValue` as an additive homomorphism. -/
def _root_.Real.toAngDValueHom : ℝ →+ AngDValue :=
  AngValue.toAngDValueHom.comp AngValue.coeHom

@[simp]
theorem coe_toAngDValueHom : (toAngDValueHom : ℝ → AngDValue) = ((↑) : ℝ → AngDValue) :=
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
theorem coe_neg_pi_div_two : ((- π / 2 : ℝ) : AngDValue) = ↑(π / 2 : ℝ) := by
  refine' eq_iff_pi_dvd_sub.mpr ⟨- 1, _⟩
  rw [sub_eq_add_neg, ← neg_div, add_halves', Int.cast_neg, Int.cast_one, mul_neg, mul_one]

@[simp]
theorem neg_coe_pi_div_two : -((π / 2 : ℝ) : AngDValue) = ↑(π / 2 : ℝ) := by
  rw [← coe_neg, ← AngValue.coe_neg, neg_div']
  exact coe_neg_pi_div_two

@[simp]
theorem two_nsmul_coe_div_two (θ : ℝ) : (2 : ℕ) • (↑(θ / 2) : AngDValue) = θ := by
  rw [← coe_nsmul, two_nsmul, ← AngValue.coe_add, add_halves]

@[simp]
theorem two_zsmul_coe_div_two (θ : ℝ) : (2 : ℤ) • (↑(θ / 2) : AngDValue) = θ := by
  rw [← coe_zsmul, two_zsmul, ← AngValue.coe_add, add_halves]

end AngDValue

open AngDValue

namespace AngValue

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

theorem coe_eq_coe_iff_two_nsmul_eq {θ₁ θ₂ : AngValue} : (θ₁ : AngDValue) = (θ₂ : AngDValue) ↔ 2 • θ₁ = 2 • θ₂ :=
  coe_eq_coe_iff.trans two_nsmul_eq_iff.symm

@[simp]
theorem coe_add_pi {θ : AngValue} : ↑(θ + π) = (θ : AngDValue) := by
  rw [coe_eq_coe_iff]
  exact .inr rfl

theorem coe_eq_zero_iff {θ : AngValue} : θ = (0 : AngDValue) ↔ θ = 0 ∨ θ = π := by
  rw [← AngDValue.coe_zero, coe_eq_coe_iff, zero_add]

theorem coe_eq_pi_div_two_iff {θ : AngValue} : (θ : AngDValue) = (π / 2 : ℝ) ↔ θ = (π / 2 : ℝ) ∨ θ = (- π / 2 : ℝ) := by
  rw [coe_eq_coe_iff, ← eq_iff_iff]
  congr
  exact eq_iff_two_pi_dvd_sub.mpr ⟨1, by ring⟩

end AngValue

protected abbrev AngDValue.lift {α : Sort*} (f : AngValue → α) (hf : ∀ θ, f (θ + π) = f θ) : AngDValue → α :=
  Quotient.lift (fun v : ℝ ↦ f v) fun (v₁ v₂ : ℝ) h ↦ (by
    replace h : (v₁ : AngDValue) = (v₂ : AngDValue)
    · exact Quotient.sound h
    obtain (h | h) := coe_eq_coe_iff.mp h <;>
      simp only [h, hf])



section Notations
open Lean

section pi -- no need to open Real when using `π`
syntax (name := piNotation) (priority := high) "π" : term

@[macro piNotation] def piNotationImpl : Macro
  | `(π) => `(Real.pi)
  | _ => Macro.throwUnsupported

end pi

@[inherit_doc] notation "∠[" x "]" => AngValue.coe x

open PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `AngValue.coe` -/
@[delab app.EuclidGeom.AngValue.coe]
def delabAngValueCoe : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``AngValue.coe 1
  let x ← withNaryArg 0 delab
  `(∠[$x])

-- we do not make a delaborator for this notation
-- because we want everyone to be aware that it's two coercions
notation "∡[" x "]" => AngValue.toAngDValue (AngValue.coe x)

end Notations



variable {θ ψ : AngValue}

namespace AngValue

section
-- some supplementary lemma not explicitly written in mathlib

theorem toReal_lt_pi_of_ne_pi (h : θ ≠ π) : θ.toReal < π := by
  contrapose! h
  exact toReal_eq_pi_iff.mp (le_antisymm θ.toReal_le_pi h)

-- to make those unfamiliar with Ioc easy to use
theorem neg_pi_lt_toReal_le_pi : - π < θ.toReal ∧ θ.toReal ≤ π :=
  AngValue.toReal_mem_Ioc _

theorem eq_coe_of_toReal_eq {x : ℝ} (h : θ.toReal = x) : θ = ∠[x] :=
  (θ.coe_toReal).symm.trans (congrArg AngValue.coe h)

theorem neg_pi_le_toReal : - π ≤ θ.toReal := le_of_lt θ.neg_pi_lt_toReal

instance instCircularOrderedAddCommGroup : CircularOrderedAddCommGroup AngValue :=
  haveI hp : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  QuotientAddGroup.instCircularOrderedAddCommGroup ℝ

end

section composite

@[simp]
theorem toReal_coe_eq_self {r : ℝ} (h₁ : - π < r) (h₂ : r ≤ π) : ∠[r].toReal = r :=
  toReal_coe_eq_self_iff.mpr ⟨h₁, h₂⟩

-- a variant of `AngValue.eq_iff_two_pi_dvd_sub`
theorem coe_eq_iff {r s : ℝ} : ∠[r] = ∠[s] ↔ ∃ k : ℤ, r - s = k * (2 * π) :=
  Iff.trans eq_iff_two_pi_dvd_sub <|
    exists_congr (fun _ => by rw [mul_comm])

theorem toReal_coe_eq_self_add_two_mul_int_mul_pi (r : ℝ) : ∃ k : ℤ, ∠[r].toReal = r + k * (2 * π) := by
  rcases coe_eq_iff.mp ∠[r].coe_toReal with ⟨k, h⟩
  exact ⟨k, eq_add_of_sub_eq' h⟩

theorem coe_eq_of_add_two_mul_int_mul_pi {r₁ r₂ : ℝ} (k : ℤ) (h : r₁ = r₂ + k * (2 * π)) : ∠[r₁] = ∠[r₂] :=
  coe_eq_iff.mpr ⟨k, sub_eq_of_eq_add' h⟩

@[simp]
theorem add_two_pi (x : ℝ) : ∠[x + 2 * π] = ∠[x] :=
  coe_eq_of_add_two_mul_int_mul_pi 1 (by rw [Int.cast_one, one_mul])

@[simp]
theorem sub_two_pi (x : ℝ) : ∠[x - 2 * π] = ∠[x] := by
  refine' coe_eq_of_add_two_mul_int_mul_pi (- 1) _
  rw [Int.cast_neg, Int.cast_one, neg_mul, one_mul]
  rfl

@[simp]
theorem neg_toReal (h : θ ≠ π) : (- θ).toReal = - θ.toReal := by
  nth_rw 1 [← θ.coe_toReal]
  exact toReal_coe_eq_self
    (neg_lt_neg_iff.mpr (toReal_lt_pi_of_ne_pi h)) (neg_le.mp (le_of_lt θ.neg_pi_lt_toReal))

end composite

section special_value

theorem pi_div_two_ne_neg_pi_div_two : ∠[π / 2] ≠ ∠[- π / 2] := by
  apply sub_ne_zero.mp
  norm_cast
  field_simp
  exact pi_ne_zero

theorem pi_div_two_ne_pi : ∠[π / 2] ≠ ∠[π] := by
  apply sub_ne_zero.mp
  norm_cast
  apply ne_of_eq_of_ne (b := ∠[- π / 2])
  congr
  ring
  exact neg_pi_div_two_ne_zero

theorem neg_pi_div_two_ne_pi : ∠[- π / 2] ≠ ∠[π] := by
  rw [← neg_coe_pi]
  apply sub_ne_zero.mp
  norm_cast
  apply ne_of_eq_of_ne (b := ∠[π / 2])
  congr
  ring
  exact pi_div_two_ne_zero

theorem neg_coe_pi_div_two : - ∠[π / 2] = ∠[- π / 2] := by rw [neg_div, coe_neg]

end special_value

section group_hom

@[simp]
theorem two_nsmul_toReal_div_two : 2 • ∠[θ.toReal / 2] = θ := by
  nth_rw 2 [← θ.coe_toReal]
  exact two_nsmul_coe_div_two θ.toReal

@[simp]
theorem two_zsmul_toReal_div_two : (2 : ℤ) • ∠[θ.toReal / 2] = θ :=
  θ.two_nsmul_toReal_div_two

end group_hom

section pos_neg_isND

-- variant of `AngValue.sign`,
-- `Maybe this section should be rewrite using AngValue.sign to have more complete api's`
-- `Or just check Real.Angle.sign to write more api's, IsPos IsNeg is more similar to human language than sign`

/-- An angle is positive if it is strictly between `0` and `π`. -/
@[pp_dot]
def IsPos (θ : AngValue) : Prop := sbtw 0 θ π

/-- An angle is negative if it is strictly between `- π` and `0`. -/
@[pp_dot]
def IsNeg (θ : AngValue) : Prop := sbtw ∠[π] θ 0

/-- An angle is non-degenerate if it is not `0` or `π`. -/
@[pp_dot]
structure IsND (θ : AngValue) : Prop where
  ne_zero : θ ≠ 0
  ne_pi : θ ≠ π

section special_value

theorem not_zero_isPos : ¬ ∠[0].IsPos := sbtw_irrefl_left

theorem not_zero_isNeg : ¬ ∠[0].IsNeg := sbtw_irrefl_right

theorem not_zero_isND : ¬ ∠[0].IsND := fun nd ↦ nd.1 rfl

theorem not_isPos_of_eq_zero (h : θ = 0) : ¬ θ.IsPos := by
  rw [h]
  exact not_zero_isPos

theorem ne_zero_of_isPos (h : θ.IsPos) : θ ≠ 0 := fun hs ↦ not_isPos_of_eq_zero hs h

theorem not_isNeg_of_eq_zero (h : θ = 0) : ¬ θ.IsNeg := by
  rw [h]
  exact not_zero_isNeg

theorem ne_zero_of_isNeg (h : θ.IsNeg) : θ ≠ 0 := fun hs ↦ not_isNeg_of_eq_zero hs h

theorem not_isND_of_eq_zero (h : θ = 0) : ¬ θ.IsND := fun nd ↦ nd.1 h

theorem not_pi_isPos : ¬ ∠[π].IsPos := sbtw_irrefl_right

theorem not_pi_isNeg : ¬ ∠[π].IsNeg := sbtw_irrefl_left

theorem not_pi_isND : ¬ ∠[π].IsND := fun nd ↦ nd.2 rfl

theorem not_isPos_of_eq_pi (h : θ = π) : ¬ θ.IsPos := by
  rw [h]
  exact not_pi_isPos

theorem ne_pi_of_isPos (h : θ.IsPos) : θ ≠ π := fun hs ↦ not_isPos_of_eq_pi hs h

theorem not_isNeg_of_eq_pi (h : θ = π) : ¬ θ.IsNeg := by
  rw [h]
  exact not_pi_isNeg

theorem ne_pi_of_isNeg (h : θ.IsNeg) : θ ≠ π := fun hs ↦ not_isNeg_of_eq_pi hs h

theorem not_isND_of_eq_pi (h : θ = π) : ¬ θ.IsND := fun nd ↦ nd.2 h

theorem isND_iff : θ.IsND ↔ θ ≠ 0 ∧ θ ≠ π :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

theorem not_isND_iff : ¬ θ.IsND ↔ (θ = 0 ∨ θ = π) :=
  (not_iff_not.mpr θ.isND_iff).trans or_iff_not_and_not.symm

theorem two_nsmul_ne_zero_iff_isND : 2 • θ ≠ 0 ↔ θ.IsND :=
  (θ.two_nsmul_ne_zero_iff).trans (θ.isND_iff).symm

theorem two_nsmul_eq_zero_iff_not_isND : 2 • θ = 0 ↔ ¬ θ.IsND :=
  (θ.two_nsmul_eq_zero_iff).trans (θ.not_isND_iff).symm

theorem ne_neg_self_iff_isND : θ ≠ - θ ↔ θ.IsND := sorry

theorem eq_neg_self_iff_not_isND : θ = - θ ↔ ¬ θ.IsND := sorry

theorem not_isND_iff_coe : ¬ θ.IsND ↔ θ = (0 : AngDValue) :=
  not_isND_iff.trans (θ.coe_eq_zero_iff).symm

theorem isND_iff_coe : θ.IsND ↔ (θ : AngDValue) ≠ 0 :=
  not_not.symm.trans (θ.not_isND_iff_coe).not

end special_value

section trichotomy

theorem not_isNeg_of_isPos (h : θ.IsPos) : ¬ θ.IsNeg := sbtw_asymm h

theorem isND_of_isPos (h : θ.IsPos) : θ.IsND where
  ne_zero hs := not_isPos_of_eq_zero hs h
  ne_pi hs := not_isPos_of_eq_pi hs h

theorem not_isPos_of_isNeg (h : θ.IsNeg) : ¬ θ.IsPos := sbtw_asymm h

theorem isND_of_isNeg (h : θ.IsNeg) : θ.IsND where
  ne_zero hs := not_isNeg_of_eq_zero hs h
  ne_pi hs := not_isNeg_of_eq_pi hs h

theorem not_isPos_of_not_isND (h : ¬ θ.IsND) : ¬ θ.IsPos := fun hs ↦ h (isND_of_isPos hs)

theorem not_isNeg_of_not_isND (h : ¬ θ.IsND) : ¬ θ.IsNeg := fun hs ↦ h (isND_of_isNeg hs)

theorem isND_iff_isPos_or_isNeg : θ.IsND ↔ θ.IsPos ∨ θ.IsNeg := by
  constructor
  · intro h
    contrapose! h
    have h := (and_congr btw_iff_not_sbtw btw_iff_not_sbtw).mpr h.symm
    rcases btw_antisymm (btw_cyclic_right h.1) (btw_cyclic_left h.2) with h | h
    · exact (pi_ne_zero h).elim
    · exact not_isND_iff.mpr ((or_congr_left eq_comm).mp h)
  · exact fun h ↦ h.elim isND_of_isPos isND_of_isNeg

theorem not_isND_or_isPos_or_isNeg : ¬ θ.IsND ∨ θ.IsPos ∨ θ.IsNeg :=
  if h : θ.IsND then .inr (isND_iff_isPos_or_isNeg.mp h) else .inl h

theorem not_isPos_iff_not_isND_or_isNeg : ¬ θ.IsPos ↔ ¬ θ.IsND ∨ θ.IsNeg := by
  constructor
  · have _ := θ.not_isND_or_isPos_or_isNeg
    tauto
  · exact Or.elim (left := not_isPos_of_not_isND) (right := not_isPos_of_isNeg)

theorem not_isNeg_iff_not_isND_or_isPos : ¬ θ.IsNeg ↔ ¬ θ.IsND ∨ θ.IsPos := by
  constructor
  · have _ := θ.not_isND_or_isPos_or_isNeg
    tauto
  · exact Or.elim (left := not_isNeg_of_not_isND) (right := not_isNeg_of_isPos)

end trichotomy

section toReal

theorem zero_le_toReal_iff : 0 ≤ θ.toReal ↔ btw 0 θ π := by
  haveI hp : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  rw [← neg_coe_pi, ← θ.coe_toReal]
  refine' Iff.trans _ btw_cyclic.symm
  refine' (Eq.to_iff _).trans QuotientAddGroup.btw_coe_iff.symm
  congr
  refine' ((toIcoMod_eq_self hp.1).mpr _).symm
  rw [neg_add_eq_of_eq_add (two_mul π)]
  exact ⟨neg_nonpos.mpr (le_of_lt Real.pi_pos), Real.pi_pos⟩

theorem zero_le_toReal_of_isPos (h : θ.IsPos) : 0 ≤ θ.toReal :=
  zero_le_toReal_iff.mpr (btw_of_sbtw h)

theorem zero_lt_toReal_of_isPos (h : θ.IsPos) : 0 < θ.toReal :=
  (Ne.symm <| toReal_eq_zero_iff.not.mpr <| ne_zero_of_isPos h).lt_of_le (zero_le_toReal_of_isPos h)

theorem toReal_lt_pi_of_isPos (h : θ.IsPos) : θ.toReal < π :=
  (Ne.lt_of_le <| toReal_eq_pi_iff.not.mpr <| ne_pi_of_isPos h) θ.toReal_le_pi

theorem toReal_lt_zero_of_isNeg (h : θ.IsNeg) : θ.toReal < 0 := by
  contrapose! h
  exact not_sbtw_of_btw (zero_le_toReal_iff.mp h)

theorem toReal_le_zero_of_isNeg (h : θ.IsNeg) : θ.toReal ≤ 0 :=
  le_of_lt (toReal_lt_zero_of_isNeg h)

theorem isPos_of_zero_lt_toReal_of_ne_pi (h : 0 < θ.toReal) (hn : θ ≠ π) : θ.IsPos :=
  Or.casesOn (isND_iff_isPos_or_isNeg.mp ⟨toReal_eq_zero_iff.not.mp (ne_of_gt h), hn⟩)
    id (fun hp ↦ (not_lt_of_ge (toReal_le_zero_of_isNeg hp) h).elim)

theorem isNeg_of_toReal_lt_zero (h : θ.toReal < 0) : θ.IsNeg := by
  contrapose! h
  exact zero_le_toReal_iff.mpr (btw_iff_not_sbtw.mpr h)

theorem isPos_iff : θ.IsPos ↔ (0 < θ.toReal ∧ (θ.toReal < π)) := ⟨
  fun h ↦ ⟨zero_lt_toReal_of_isPos h, toReal_lt_pi_of_isPos h⟩,
  fun h ↦ isPos_of_zero_lt_toReal_of_ne_pi h.1 (toReal_eq_pi_iff.not.mp (ne_of_lt h.2))⟩

theorem not_isPos_iff : ¬ θ.IsPos ↔ (θ.toReal ≤ 0 ∨ θ.toReal = π) :=
  (θ.isPos_iff).not.trans (by simp only [not_and_or, not_lt, ge_iff_le, (θ.toReal_le_pi).ge_iff_eq])

theorem isNeg_iff : θ.IsNeg ↔ (θ.toReal < 0) :=
  ⟨toReal_lt_zero_of_isNeg, isNeg_of_toReal_lt_zero⟩

theorem not_isNeg_iff : ¬ θ.IsNeg ↔ (0 ≤ θ.toReal) := (θ.isNeg_iff).not.trans not_lt

theorem isND_iff' : θ.IsND ↔ (θ.toReal ≠ 0 ∧ θ.toReal ≠ π) := ⟨
  fun h ↦ ⟨toReal_eq_zero_iff.not.mpr h.1, toReal_eq_pi_iff.not.mpr h.2⟩,
  fun h ↦ ⟨toReal_eq_zero_iff.not.mp h.1 ,toReal_eq_pi_iff.not.mp h.2⟩⟩

theorem not_isND_iff' : ¬ θ.IsND ↔ (θ.toReal = 0 ∨ θ.toReal = π) :=
  isND_iff'.not.trans (not_and_or.trans (or_congr not_ne_iff not_ne_iff))

end toReal

section sin

theorem isNeg_iff_sin_lt_zero : θ.IsNeg ↔ sin θ < 0 :=
  isNeg_iff.trans (toReal_neg_iff_sign_neg.trans sign_eq_neg_one_iff)

theorem isND_iff_sin_ne_zero : θ.IsND ↔ sin θ ≠ 0 :=
  isND_iff.trans (sign_ne_zero_iff.symm.trans sign_ne_zero)

theorem not_isND_iff_sin_eq_zero : ¬ θ.IsND ↔ sin θ = 0 :=
  not_isND_iff.trans (Real.Angle.sign_eq_zero_iff.symm.trans _root_.sign_eq_zero_iff)

theorem sin_lt_zero_of_isNeg (h : θ.IsNeg) : sin θ < 0 := isNeg_iff_sin_lt_zero.mp h

theorem isNeg_of_sin_lt_zero (h : sin θ < 0) : θ.IsNeg := isNeg_iff_sin_lt_zero.mpr h

theorem sin_eq_zero_of_not_isND (h : ¬ θ.IsND) : sin θ = 0 := not_isND_iff_sin_eq_zero.mp h

theorem not_isND_of_sin_eq_zero (h : sin θ = 0) : ¬ θ.IsND := not_isND_iff_sin_eq_zero.mpr h

theorem sin_ne_zero_of_isND (h : θ.IsND) : sin θ ≠ 0 := isND_iff_sin_ne_zero.mp h

theorem isND_of_sin_eq_zero (h : sin θ ≠ 0) : θ.IsND := isND_iff_sin_ne_zero.mpr h

theorem zero_lt_sin_of_isPos (h : θ.IsPos) : 0 < sin θ :=
  zero_lt_sin_of_zero_lt_toReal_lt_pi (zero_lt_toReal_of_isPos h) (toReal_lt_pi_of_isPos h)

theorem isPos_of_zero_lt_sin (h : 0 < sin θ) : θ.IsPos := by
  contrapose! h
  exact Or.casesOn (not_isPos_iff_not_isND_or_isNeg.mp h)
    (fun h ↦ (sin_eq_zero_of_not_isND h).symm.ge) (fun h ↦ le_of_lt (sin_lt_zero_of_isNeg h))

theorem isPos_iff_zero_lt_sin : θ.IsPos ↔ 0 < sin θ :=
  ⟨zero_lt_sin_of_isPos, isPos_of_zero_lt_sin⟩

theorem not_isNeg_iff_zero_le_sin : ¬ θ.IsNeg ↔ 0 ≤ sin θ  := isNeg_iff_sin_lt_zero.not.trans not_lt

theorem not_isPos_iff_sin_le_zero : ¬ θ.IsPos ↔ sin θ ≤ 0 := isPos_iff_zero_lt_sin.not.trans not_lt


end sin

section pi_div_two

theorem pi_div_two_isPos : ∠[π / 2].IsPos :=
  isPos_of_zero_lt_sin (sign_eq_one_iff.mp sign_coe_pi_div_two)

theorem pi_div_two_not_isNeg : ¬ ∠[π / 2].IsNeg := not_isNeg_of_isPos pi_div_two_isPos

theorem pi_div_two_isND : ∠[π / 2].IsND := isND_of_isPos pi_div_two_isPos

theorem isPos_of_eq_pi_div_two (h : θ = ∠[π / 2]) : θ.IsPos := by
  rw [h]
  exact pi_div_two_isPos

theorem not_isNeg_of_eq_pi_div_two (h : θ = ∠[π / 2]) : ¬ θ.IsNeg := by
  rw [h]
  exact pi_div_two_not_isNeg

theorem isND_of_eq_pi_div_two (h : θ = ∠[π / 2]) : θ.IsND := by
  rw [h]
  exact pi_div_two_isND

theorem neg_pi_div_two_isNeg : ∠[- π / 2].IsNeg :=
  isNeg_of_sin_lt_zero (sign_eq_neg_one_iff.mp sign_coe_neg_pi_div_two)

theorem neg_pi_div_two_not_isPos : ¬ ∠[- π / 2].IsPos := not_isPos_of_isNeg neg_pi_div_two_isNeg

theorem neg_pi_div_two_isND : ∠[- π / 2].IsND := isND_of_isNeg neg_pi_div_two_isNeg

theorem isNeg_of_eq_neg_pi_div_two (h : θ = ∠[- π / 2]) : θ.IsNeg := by
  rw [h]
  exact neg_pi_div_two_isNeg

theorem not_isPos_of_eq_neg_pi_div_two (h : θ = ∠[- π / 2]) : ¬ θ.IsPos := by
  rw [h]
  exact neg_pi_div_two_not_isPos

theorem isND_of_eq_neg_pi_div_two (h : θ = ∠[- π / 2]) : θ.IsND := by
  rw [h]
  exact neg_pi_div_two_isND

end pi_div_two

section neg

@[simp]
theorem neg_isPos_iff_isNeg : (- θ).IsPos ↔ θ.IsNeg :=
  isPos_iff_zero_lt_sin.trans (Iff.trans (by rw [sin_neg, Left.neg_pos_iff]) isNeg_iff_sin_lt_zero.symm)

@[simp]
theorem neg_isNeg_iff_isPos : (- θ).IsNeg ↔ θ.IsPos :=
  isNeg_iff_sin_lt_zero.trans (Iff.trans (by rw [sin_neg, Left.neg_neg_iff]) isPos_iff_zero_lt_sin.symm)

@[simp]
theorem neg_isND_iff_isND : (- θ).IsND ↔ θ.IsND :=
  isND_iff_sin_ne_zero.trans (Iff.trans (by rw [sin_neg, ne_eq, neg_eq_zero]) isND_iff_sin_ne_zero.symm)

theorem ne_neg_of_isPos (hs : θ.IsPos) (hp : ψ.IsPos) : θ ≠ - ψ :=
  fun h ↦ not_isNeg_of_isPos hp (neg_isPos_iff_isNeg.mp (cast (congrArg IsPos h) hs))

theorem ne_neg_of_isNeg (hs : θ.IsNeg) (hp : ψ.IsNeg) : θ ≠ - ψ :=
  fun h ↦ not_isPos_of_isNeg hp (neg_isNeg_iff_isPos.mp (cast (congrArg IsNeg h) hs))

end neg

section coe

theorem coe_isPos_of_zero_lt_self_lt_pi {x : ℝ} (h0 : 0 < x) (hp : x < π) : ∠[x].IsPos := by
  apply AngValue.isPos_iff.mpr
  rw [toReal_coe_eq_self (gt_trans h0 (by linarith)) (le_of_lt hp)]
  exact ⟨h0, hp⟩

theorem coe_isNeg_of_neg_pi_lt_self_lt_zero {x : ℝ} (hp : - π < x) (h0 : x < 0) : ∠[x].IsNeg :=
  AngValue.isNeg_iff.mpr ((toReal_coe_eq_self hp (le_of_lt (h0.trans pi_pos))).trans_lt h0)

theorem coe_not_isNeg_of_zero_le_self_le_pi {x : ℝ} (h0 : 0 ≤ x) (hp : x ≤ π) : ¬ ∠[x].IsNeg :=
  AngValue.not_isNeg_iff.mpr <|
    (toReal_coe_eq_self (LT.lt.trans_le (by linarith [pi_pos]) h0) hp).symm.trans_ge h0

end coe

section add_pi

@[simp]
theorem add_pi_isPos_iff_isNeg : (θ + π).IsPos ↔ θ.IsNeg :=
  isPos_iff_zero_lt_sin.trans (Iff.trans (by rw [θ.sin_add_pi, neg_pos]) isNeg_iff_sin_lt_zero.symm)

@[simp]
theorem add_pi_isNeg_iff_isPos : (θ + π).IsNeg ↔ θ.IsPos :=
  isNeg_iff_sin_lt_zero.trans (Iff.trans (by rw [θ.sin_add_pi, neg_lt_zero]) isPos_iff_zero_lt_sin.symm)

@[simp]
theorem add_pi_isND_iff_isND : (θ + π).IsND ↔ θ.IsND :=
  isND_iff_sin_ne_zero.trans (Iff.trans (by rw [θ.sin_add_pi, neg_ne_zero]) isND_iff_sin_ne_zero.symm)

theorem ne_add_pi_of_isPos (hs : θ.IsPos) (hp : ψ.IsPos) : θ ≠ ψ + π :=
  fun h ↦ not_isNeg_of_isPos hp (add_pi_isPos_iff_isNeg.mp (cast (congrArg IsPos h) hs))

theorem eq_of_isPos_of_two_nsmul_eq (hs : θ.IsPos) (hp : ψ.IsPos) (h : 2 • θ = 2 • ψ) : θ = ψ :=
  (or_iff_left (ne_add_pi_of_isPos hs hp)).mp (two_nsmul_eq_iff.mp h)

theorem eq_of_isPos_of_coe_eq (hs : θ.IsPos) (hp : ψ.IsPos) (h : (θ : AngDValue) = ψ) : θ = ψ :=
  (or_iff_left (ne_add_pi_of_isPos hs hp)).mp (coe_eq_coe_iff.mp h)

theorem ne_add_pi_of_isNeg (hs : θ.IsNeg) (hp : ψ.IsNeg) : θ ≠ ψ + π :=
  fun h ↦ not_isPos_of_isNeg hp (add_pi_isNeg_iff_isPos.mp (cast (congrArg IsNeg h) hs))

theorem eq_of_isNeg_of_two_nsmul_eq (hs : θ.IsNeg) (hp : ψ.IsNeg) (h : 2 • θ = 2 • ψ) : θ = ψ :=
  (or_iff_left (ne_add_pi_of_isNeg hs hp)).mp (two_nsmul_eq_iff.mp h)

theorem eq_of_isNeg_of_coe_eq (hs : θ.IsNeg) (hp : ψ.IsNeg) (h : (θ : AngDValue) = ψ) : θ = ψ :=
  (or_iff_left (ne_add_pi_of_isNeg hs hp)).mp (coe_eq_coe_iff.mp h)

end add_pi

section pi_sub

@[simp]
theorem pi_sub_isPos_iff_isPos : (π - θ).IsPos ↔ θ.IsPos := by
  simp only [isPos_iff_zero_lt_sin, sin_pi_sub]

@[simp]
theorem pi_sub_isNeg_iff_isNeg : (π - θ).IsNeg ↔ θ.IsNeg := by
  simp only [isNeg_iff_sin_lt_zero, sin_pi_sub]

@[simp]
theorem pi_sub_isND_iff_isND : (π - θ).IsND ↔ θ.IsND := by
  simp only [isND_iff_sin_ne_zero, sin_pi_sub]

end pi_sub

-- Do we need to realize `IsPos` as a `SignType`?

end pos_neg_isND

section acute_obtuse_right

/-- An angle is acute if it is strictly between `- π / 2` and `π / 2`. -/
@[pp_dot]
def IsAcu (θ : AngValue) : Prop := sbtw ∠[- π / 2] θ ∠[π / 2]

/-- An angle is obtuse if it is strictly between `π / 2` and `- π / 2`. -/
@[pp_dot]
def IsObt (θ : AngValue) : Prop := sbtw ∠[π / 2] θ ∠[- π / 2]

/-- An angle is right if it is `- π / 2` or `π / 2`. -/
@[pp_dot]
def IsRight (θ : AngValue) : Prop := θ = ∠[- π / 2] ∨ θ = ∠[π / 2]

section special_value
-- Special values for π / 2 and - π / 2.

theorem pi_div_two_not_isAcu : ¬ ∠[π / 2].IsAcu := sbtw_irrefl_right

theorem not_isAcu_of_eq_pi_div_two (h : θ = ∠[π / 2]) : ¬ θ.IsAcu :=
  (congrArg IsAcu h).mpr_not pi_div_two_not_isAcu

theorem pi_div_two_not_isObt : ¬ ∠[π / 2].IsObt := sbtw_irrefl_left

theorem not_isObt_of_eq_pi_div_two (h : θ = ∠[π / 2]) : ¬ θ.IsObt :=
  (congrArg IsObt h).mpr_not pi_div_two_not_isObt

theorem pi_div_two_isRight : ∠[π / 2].IsRight := .inr rfl

theorem isRight_of_eq_pi_div_two (h : θ = ∠[π / 2]) : θ.IsRight := .inr h

theorem neg_pi_div_two_not_isAcu : ¬ ∠[- π / 2].IsAcu := sbtw_irrefl_left

theorem not_isAcu_of_eq_neg_pi_div_two (h : θ = ∠[- π / 2]) : ¬ θ.IsAcu :=
  (congrArg IsAcu h).mpr_not neg_pi_div_two_not_isAcu

theorem neg_pi_div_two_not_isObt : ¬ ∠[- π / 2].IsObt := sbtw_irrefl_right

theorem not_isObt_of_eq_neg_pi_div_two (h : θ = ∠[- π / 2]) : ¬ θ.IsObt :=
  (congrArg IsObt h).mpr_not neg_pi_div_two_not_isObt

theorem neg_pi_div_two_isRight : ∠[- π / 2].IsRight := .inl rfl

theorem isRight_of_eq_neg_pi_div_two (h : θ = ∠[- π / 2]) : θ.IsRight := .inl h

theorem isRight_iff : θ.IsRight ↔ θ = ∠[π / 2] ∨ θ = ∠[- π / 2] := or_comm

theorem not_isRight_iff : ¬ θ.IsRight ↔ θ ≠ ∠[- π / 2] ∧ θ ≠ ∠[π / 2] := not_or

theorem isRight_iff_coe : θ.IsRight ↔ (θ : AngDValue) = ∡[π / 2] :=
  isRight_iff.trans (θ.coe_eq_pi_div_two_iff).symm

end special_value

section trichotomy

theorem not_isObt_of_isAcu (h : θ.IsAcu) : ¬ θ.IsObt := sbtw_asymm h

theorem not_isAcu_of_isObt (h : θ.IsObt) : ¬ θ.IsAcu := sbtw_asymm h

theorem not_isAcu_of_not_isRight (h : θ.IsRight) : ¬ θ.IsAcu :=
  Or.casesOn h (fun h ↦ not_isAcu_of_eq_neg_pi_div_two h) (fun h ↦ not_isAcu_of_eq_pi_div_two h)

theorem not_isObt_of_not_isRight (h : θ.IsRight) : ¬ θ.IsObt :=
  Or.casesOn h (fun h ↦ not_isObt_of_eq_neg_pi_div_two h) (fun h ↦ not_isObt_of_eq_pi_div_two h)

theorem not_isRight_of_isAcu (h : θ.IsAcu) : ¬ θ.IsRight :=
  fun hr ↦ (not_isAcu_of_not_isRight hr) h

theorem not_isRight_of_isObt (h : θ.IsObt) : ¬ θ.IsRight :=
  fun hr ↦ (not_isObt_of_not_isRight hr) h

theorem isAcu_or_isNeg_of_isRight (h : ¬ θ.IsRight) : θ.IsAcu ∨ θ.IsObt := by
  contrapose! h
  have h := (and_congr btw_iff_not_sbtw btw_iff_not_sbtw).mpr h.symm
  rcases btw_antisymm (btw_cyclic_right h.1) (btw_cyclic_left h.2) with h | h
  · exact (pi_div_two_ne_neg_pi_div_two h).elim
  · exact (or_congr_left eq_comm).mp h

theorem not_isRight_or_isAcu_or_isNeg : θ.IsRight ∨ θ.IsAcu ∨ θ.IsObt :=
  if h : θ.IsRight then .inl h else .inr (isAcu_or_isNeg_of_isRight h)

theorem isRight_or_isObt_of_not_isAcu (h : ¬ θ.IsAcu) : θ.IsRight ∨ θ.IsObt :=
  Or.casesOn not_isRight_or_isAcu_or_isNeg (fun h ↦ .inl h) fun hn ↦
    Or.casesOn hn (fun hp ↦ (h hp).elim) (fun h ↦ .inr h)

theorem isRight_or_isAcu_of_not_isObt (h : ¬ θ.IsObt) : θ.IsRight ∨ θ.IsAcu :=
  Or.casesOn not_isRight_or_isAcu_or_isNeg (fun h ↦ .inl h) fun hn ↦
    Or.casesOn hn (fun h ↦ .inr h) (fun hp ↦ (h hp).elim)

end trichotomy

section toReal

theorem neg_pi_div_two_le_toReal_le_pi_div_two_iff_btw : - π / 2 ≤ θ.toReal ∧ θ.toReal ≤ π / 2 ↔ btw ∠[- π / 2] θ ∠[π / 2] := by
  haveI hp : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  nth_rw 3 [← θ.coe_toReal]
  refine' Iff.trans _ QuotientAddGroup.btw_coe_iff.symm
  rw [(toIocMod_eq_self hp.1).mpr ⟨by linarith [pi_pos], by linarith [pi_pos]⟩]
  by_cases h : θ.toReal < - π / 2
  · refine' iff_of_false (not_and_of_not_left _ (not_le.mpr h)) (not_le.mpr _)
    rw [← toIcoMod_add_right, (toIcoMod_eq_self hp.1).mpr ⟨by linarith [θ.neg_pi_lt_toReal], by linarith⟩]
    linarith [θ.neg_pi_lt_toReal]
  · rw [(toIcoMod_eq_self hp.1).mpr ⟨not_lt.mp h, by linarith [θ.toReal_le_pi, pi_pos]⟩]
    exact and_iff_right (not_lt.mp h)

theorem not_isObt_iff : ¬ θ.IsObt ↔ - π / 2 ≤ θ.toReal ∧ θ.toReal ≤ π / 2 :=
  ((θ.neg_pi_div_two_le_toReal_le_pi_div_two_iff_btw).trans btw_iff_not_sbtw).symm

theorem neg_pi_div_two_le_toReal_of_isObt (h : ¬ θ.IsObt) : - π / 2 ≤ θ.toReal :=
  ((θ.not_isObt_iff).mp h).1

theorem toReal_le_pi_div_two_of_isObt (h : ¬ θ.IsObt) : θ.toReal ≤ π / 2 := ((θ.not_isObt_iff).mp h).2

theorem isObt_iff : θ.IsObt ↔ θ.toReal < - π / 2 ∨ π / 2 < θ.toReal :=
  (iff_not_comm.mpr (not_isObt_iff).symm).trans (not_and_or.trans (or_congr not_le not_le))

theorem isObt_of_toReal_lt_neg_pi_div_two (h : θ.toReal < - π / 2) : θ.IsObt := (θ.isObt_iff).mpr (.inl h)

theorem isObt_of_pi_div_two_lt_toReal (h : π / 2 < θ.toReal) : θ.IsObt := (θ.isObt_iff).mpr (.inr h)

theorem isRight_iff' : θ.IsRight ↔ θ.toReal = - π / 2 ∨ θ.toReal = π / 2 :=
  or_congr (θ.toReal_eq_neg_pi_div_two_iff).symm (θ.toReal_eq_pi_div_two_iff).symm

theorem not_isRight_iff' : ¬ θ.IsRight ↔ θ.toReal ≠ - π / 2 ∧ θ.toReal ≠ π / 2 :=
  (θ.isRight_iff').not.trans (not_or.trans Iff.rfl)

theorem neg_pi_div_two_le_toReal_of_isAcu (h : θ.IsAcu) : - π / 2 ≤ θ.toReal :=
  (neg_pi_div_two_le_toReal_le_pi_div_two_iff_btw.mpr (btw_of_sbtw h)).1

theorem neg_pi_div_two_lt_toReal_of_isAcu (h : θ.IsAcu) : - π / 2 < θ.toReal :=
  if hs : θ.toReal = - π / 2 then (not_isAcu_of_eq_neg_pi_div_two (eq_coe_of_toReal_eq hs) h).elim
  else Ne.lt_of_le' hs (neg_pi_div_two_le_toReal_of_isAcu h)

theorem toReal_le_pi_div_two_of_isAcu (h : θ.IsAcu) : θ.toReal ≤ π / 2 :=
  (neg_pi_div_two_le_toReal_le_pi_div_two_iff_btw.mpr (btw_of_sbtw h)).2

theorem toReal_lt_pi_div_two_of_isAcu (h : θ.IsAcu) : θ.toReal < π / 2 :=
  if hs : θ.toReal = π / 2 then (not_isAcu_of_eq_pi_div_two (eq_coe_of_toReal_eq hs) h).elim
  else Ne.lt_of_le' (Ne.symm hs) (toReal_le_pi_div_two_of_isAcu h)

theorem isAcu_iff : θ.IsAcu ↔ - π / 2 < θ.toReal ∧ θ.toReal < π / 2 := ⟨
  fun h ↦ ⟨neg_pi_div_two_lt_toReal_of_isAcu h, toReal_lt_pi_div_two_of_isAcu h⟩,
  fun ⟨hn, hp⟩ ↦ (isRight_or_isAcu_of_not_isObt (not_isObt_iff.mpr ⟨le_of_lt hn, le_of_lt hp⟩)).casesOn
    (fun h ↦ (not_isRight_iff'.mpr ⟨ne_of_gt hn, LT.lt.ne hp⟩ h).elim) id⟩

theorem not_isAcu_iff : ¬ θ.IsAcu ↔ θ.toReal ≤ - π / 2 ∨ π / 2 ≤ θ.toReal :=
  (θ.isAcu_iff).not.trans (not_and_or.trans (or_congr not_lt not_lt))

end toReal

section cos

theorem isAcu_iff_zero_lt_cos : θ.IsAcu ↔ 0 < cos θ :=
  (θ.isAcu_iff).trans (θ.zero_lt_cos_iff).symm

theorem isObt_iff_cos_lt_zero : θ.IsObt ↔ cos θ < 0 :=
  (θ.isObt_iff).trans (θ.cos_lt_zero_iff).symm

theorem isRight_iff_cos_eq_zero : θ.IsRight ↔ cos θ = 0 :=
  (θ.isRight_iff).trans (θ.cos_eq_zero_iff).symm

theorem not_isRight_iff_cos_ne_zero : ¬ θ.IsRight ↔ cos θ ≠ 0 :=
  (θ.isRight_iff_cos_eq_zero).not

end cos

section zero_pi

theorem zero_isAcu : (0 : AngValue).IsAcu := by
  simp only [isAcu_iff_zero_lt_cos, cos_zero, zero_lt_one]

theorem zero_not_isObt : ¬ (0 : AngValue).IsObt := not_isObt_of_isAcu zero_isAcu

theorem zero_not_isRight : ¬ (0 : AngValue).IsRight := not_isRight_of_isAcu zero_isAcu

theorem isAcu_of_eq_zero (h : θ = 0) : θ.IsAcu := by
  rw [h]
  exact zero_isAcu

theorem not_isObt_of_eq_zero (h : θ = 0) : ¬ θ.IsObt := by
  rw [h]
  exact zero_not_isObt

theorem not_isRight_of_eq_zero (h : θ = 0) : ¬ θ.IsRight := by
  rw [h]
  exact zero_not_isRight

theorem pi_isObt : ∠[π].IsObt := by
  simp only [isObt_iff_cos_lt_zero, cos_coe, cos_pi, Left.neg_neg_iff, zero_lt_one]

theorem pi_not_isAcu : ¬ ∠[π].IsAcu := not_isAcu_of_isObt pi_isObt

theorem pi_not_isRight : ¬ ∠[π].IsRight := not_isRight_of_isObt pi_isObt

theorem isAcu_of_eq_pi (h : θ = π) : θ.IsObt := by
  rw [h]
  exact pi_isObt

theorem not_isAcu_of_eq_pi (h : θ = π) : ¬ θ.IsAcu := by
  rw [h]
  exact pi_not_isAcu

theorem not_isRight_of_eq_pi (h : θ = π) : ¬ θ.IsRight := by
  rw [h]
  exact pi_not_isRight

end zero_pi

section neg

@[simp]
theorem neg_isAcu_iff_isAcu : (- θ).IsAcu ↔ θ.IsAcu := by
  simp only [isAcu_iff_zero_lt_cos, cos_neg]

@[simp]
theorem neg_isObt_iff_isObt : (- θ).IsObt ↔ θ.IsObt := by
  simp only [isObt_iff_cos_lt_zero, cos_neg]

@[simp]
theorem neg_isRight_iff_isRight : (- θ).IsRight ↔ θ.IsRight := by
  simp only [isRight_iff_cos_eq_zero, cos_neg]

end neg

section add_pi

@[simp]
theorem add_pi_isAcu_iff_isObt : (θ + π).IsAcu ↔ θ.IsObt := by
  rw [isAcu_iff_zero_lt_cos, cos_add_pi, Left.neg_pos_iff, isObt_iff_cos_lt_zero]

@[simp]
theorem add_pi_isObt_iff_isAcu : (θ + π).IsObt ↔ θ.IsAcu := by
  rw [isAcu_iff_zero_lt_cos, isObt_iff_cos_lt_zero, cos_add_pi, Left.neg_neg_iff]

@[simp]
theorem add_pi_isRight_iff_isRight : (θ + π).IsRight ↔ θ.IsRight := by
  simp only [isRight_iff_cos_eq_zero, cos_add_pi, neg_eq_zero]

theorem ne_add_pi_of_isAcu (hs : θ.IsAcu) (hp : ψ.IsAcu) : θ ≠ ψ + π :=
  fun h ↦ not_isObt_of_isAcu hp (add_pi_isAcu_iff_isObt.mp (cast (congrArg IsAcu h) hs))

theorem eq_of_isAcu_of_two_nsmul_eq (hs : θ.IsAcu) (hp : ψ.IsAcu) (h : 2 • θ = 2 • ψ) : θ = ψ :=
  (or_iff_left (ne_add_pi_of_isAcu hs hp)).mp (two_nsmul_eq_iff.mp h)

theorem eq_of_isAcu_of_coe_eq (hs : θ.IsAcu) (hp : ψ.IsAcu) (h : (θ : AngDValue) = ψ) : θ = ψ :=
  (or_iff_left (ne_add_pi_of_isAcu hs hp)).mp (coe_eq_coe_iff.mp h)

theorem ne_add_pi_of_isObt (hs : θ.IsObt) (hp : ψ.IsObt) : θ ≠ ψ + π :=
  fun h ↦ not_isAcu_of_isObt hp (add_pi_isObt_iff_isAcu.mp (cast (congrArg IsObt h) hs))

theorem eq_of_isObt_of_two_nsmul_eq (hs : θ.IsObt) (hp : ψ.IsObt) (h : 2 • θ = 2 • ψ) : θ = ψ :=
  (or_iff_left (ne_add_pi_of_isObt hs hp)).mp (two_nsmul_eq_iff.mp h)

theorem eq_of_isObt_of_coe_eq (hs : θ.IsObt) (hp : ψ.IsObt) (h : (θ : AngDValue) = ψ) : θ = ψ :=
  (or_iff_left (ne_add_pi_of_isObt hs hp)).mp (coe_eq_coe_iff.mp h)

end add_pi

section pi_sub

@[simp]
theorem pi_sub_isAcu_iff_isObt : (π - θ).IsAcu ↔ θ.IsObt := by
  rw [isAcu_iff_zero_lt_cos, cos_pi_sub, Left.neg_pos_iff, isObt_iff_cos_lt_zero]

@[simp]
theorem pi_sub_isObt_iff_isAcu : (π - θ).IsObt ↔ θ.IsAcu := by
  rw [isAcu_iff_zero_lt_cos, isObt_iff_cos_lt_zero, cos_pi_sub, Left.neg_neg_iff]

@[simp]
theorem pi_sub_isRight_iff_isRight : (π - θ).IsRight ↔ θ.IsRight := by
  rw [isRight_iff_cos_eq_zero, isRight_iff_cos_eq_zero, cos_pi_sub, neg_eq_zero]

theorem add_ne_pi_of_isAcu (hs : θ.IsAcu) (hp : ψ.IsAcu) : θ + ψ ≠ π :=
  fun h ↦ not_isObt_of_isAcu hp (pi_sub_isAcu_iff_isObt.mp (cast (congrArg IsAcu (eq_sub_of_add_eq h)) hs))

theorem add_ne_pi_of_isObt (hs : θ.IsObt) (hp : ψ.IsObt) : θ + ψ ≠ π :=
  fun h ↦ not_isAcu_of_isObt hp (pi_sub_isObt_iff_isAcu.mp (cast (congrArg IsObt (eq_sub_of_add_eq h)) hs))

end pi_sub

section pos_neg_nd

theorem add_pi_div_two_isPos_iff_isAcu : (θ + ∠[π / 2]).IsPos ↔ θ.IsAcu := by
  rw [isPos_iff_zero_lt_sin, isAcu_iff_zero_lt_cos, sin_add_pi_div_two]

theorem add_pi_div_two_isNeg_iff_isObt : (θ + ∠[π / 2]).IsNeg ↔ θ.IsObt := by
  rw [isNeg_iff_sin_lt_zero, isObt_iff_cos_lt_zero, sin_add_pi_div_two]

theorem add_pi_div_two_not_isND_iff_isRight : ¬ (θ + ∠[π / 2]).IsND ↔ θ.IsRight := by
  rw [not_isND_iff_sin_eq_zero, isRight_iff_cos_eq_zero, sin_add_pi_div_two]

theorem add_pi_div_two_isND_iff_not_isRight : (θ + ∠[π / 2]).IsND ↔ ¬ θ.IsRight := by
  rw [isND_iff_sin_ne_zero, isRight_iff_cos_eq_zero, sin_add_pi_div_two]

theorem add_pi_div_two_isAcu_iff_isNeg : (θ + ∠[π / 2]).IsAcu ↔ θ.IsNeg := by
  rw [isNeg_iff_sin_lt_zero, isAcu_iff_zero_lt_cos, cos_add_pi_div_two, Left.neg_pos_iff]

theorem add_pi_div_two_isObt_iff_isPos : (θ + ∠[π / 2]).IsObt ↔ θ.IsPos := by
  rw [isPos_iff_zero_lt_sin, isObt_iff_cos_lt_zero, cos_add_pi_div_two, Left.neg_neg_iff]

theorem add_pi_div_two_isRight_iff_not_isND : (θ + ∠[π / 2]).IsRight ↔ ¬ θ.IsND := by
  rw [not_isND_iff_sin_eq_zero, isRight_iff_cos_eq_zero, cos_add_pi_div_two, neg_eq_zero]

theorem add_pi_div_two_not_isRight_iff_isND : ¬ (θ + ∠[π / 2]).IsRight ↔ θ.IsND := by
  rw [isND_iff_sin_ne_zero, isRight_iff_cos_eq_zero, cos_add_pi_div_two, neg_eq_zero]

theorem sub_pi_div_two_isPos_iff_isObt : (θ - ∠[π / 2]).IsPos ↔ θ.IsObt := by
  rw [isPos_iff_zero_lt_sin, isObt_iff_cos_lt_zero, sin_sub_pi_div_two, Left.neg_pos_iff]

theorem sub_pi_div_two_isNeg_iff_isAcu : (θ - ∠[π / 2]).IsNeg ↔ θ.IsAcu := by
  rw [isNeg_iff_sin_lt_zero, isAcu_iff_zero_lt_cos, sin_sub_pi_div_two, Left.neg_neg_iff]

theorem sub_pi_div_two_not_isND_iff_isRight : ¬ (θ - ∠[π / 2]).IsND ↔ θ.IsRight := by
  rw [not_isND_iff_sin_eq_zero, isRight_iff_cos_eq_zero, sin_sub_pi_div_two, neg_eq_zero]

theorem sub_pi_div_two_isND_iff_not_isRight : (θ - ∠[π / 2]).IsND ↔ ¬ θ.IsRight := by
  rw [isND_iff_sin_ne_zero, not_isRight_iff_cos_ne_zero, sin_sub_pi_div_two, ne_eq, neg_eq_zero]

theorem sub_pi_div_two_isAcu_iff_isPos : (θ - ∠[π / 2]).IsAcu ↔ θ.IsPos := by
  rw [isPos_iff_zero_lt_sin, isAcu_iff_zero_lt_cos, cos_sub_pi_div_two]

theorem sub_pi_div_two_isObt_iff_isNeg : (θ - ∠[π / 2]).IsObt ↔ θ.IsNeg := by
  rw [isNeg_iff_sin_lt_zero, isObt_iff_cos_lt_zero, cos_sub_pi_div_two]

theorem sub_pi_div_two_isRight_iff_not_isND : (θ - ∠[π / 2]).IsRight ↔ ¬ θ.IsND := by
  rw [not_isND_iff_sin_eq_zero, isRight_iff_cos_eq_zero, cos_sub_pi_div_two]

theorem sub_pi_div_two_not_isRight_iff_isND : ¬ (θ - ∠[π / 2]).IsRight ↔ θ.IsND := by
  rw [isND_iff_sin_ne_zero, isRight_iff_cos_eq_zero, cos_sub_pi_div_two]

theorem pi_div_two_sub_isPos_iff_isAcu : (∠[π / 2] - θ).IsPos ↔ θ.IsAcu := by
  rw [isPos_iff_zero_lt_sin, isAcu_iff_zero_lt_cos, sin_pi_div_two_sub]

theorem pi_div_two_sub_isNeg_iff_isAcu : (∠[π / 2] - θ).IsNeg ↔ θ.IsObt := by
  rw [isNeg_iff_sin_lt_zero, isObt_iff_cos_lt_zero, sin_pi_div_two_sub]

theorem pi_div_two_sub_not_isND_iff_isRight : ¬ (∠[π / 2] - θ).IsND ↔ θ.IsRight := by
  rw [not_isND_iff_sin_eq_zero, isRight_iff_cos_eq_zero, sin_pi_div_two_sub]

theorem pi_div_two_sub_isND_iff_not_isRight : (∠[π / 2] - θ).IsND ↔ ¬ θ.IsRight := by
  rw [isND_iff_sin_ne_zero, isRight_iff_cos_eq_zero, sin_pi_div_two_sub]

theorem pi_div_two_sub_isAcu_iff_isPos : (∠[π / 2] - θ).IsAcu ↔ θ.IsPos := by
  rw [isPos_iff_zero_lt_sin, isAcu_iff_zero_lt_cos, cos_pi_div_two_sub]

theorem pi_div_two_sub_isObt_iff_isNeg : (∠[π / 2] - θ).IsObt ↔ θ.IsNeg := by
  rw [isNeg_iff_sin_lt_zero, isObt_iff_cos_lt_zero, cos_pi_div_two_sub]

theorem pi_div_two_sub_isRight_iff_not_isND : (∠[π / 2] - θ).IsRight ↔ ¬ θ.IsND := by
  rw [not_isND_iff_sin_eq_zero, isRight_iff_cos_eq_zero, cos_pi_div_two_sub]

theorem pi_div_two_sub_not_isRight_iff_isND : ¬ (∠[π / 2] - θ).IsRight ↔ θ.IsND := by
  rw [isND_iff_sin_ne_zero, isRight_iff_cos_eq_zero, cos_pi_div_two_sub]

theorem eq_pi_div_two_of_isRight_of_isPos (hr : θ.IsRight) (h : ¬ θ.IsNeg) : θ = ∠[π / 2] :=
  hr.casesOn (fun hr ↦ (h (isNeg_of_eq_neg_pi_div_two hr)).elim) id

theorem eq_neg_pi_div_two_of_isRight_of_isNeg (hr : θ.IsRight) (h : ¬ θ.IsPos) : θ = ∠[- π / 2] :=
  hr.casesOn id (fun hr ↦ (h (isPos_of_eq_pi_div_two hr)).elim)

theorem eq_zero_of_not_isND_of_isAcu (hr : ¬ θ.IsND) (h : θ.IsAcu) : θ = 0 :=
  (not_isND_iff.mp hr).casesOn id (fun hr ↦ (not_isAcu_of_eq_pi hr h).elim)

theorem eq_pi_of_not_isND_of_isObt (hr : ¬ θ.IsND) (h : θ.IsObt) : θ = π :=
  (not_isND_iff.mp hr).casesOn (fun hr ↦ (not_isObt_of_eq_zero hr h).elim) id

end pos_neg_nd

end acute_obtuse_right



section trigonometric

theorem cos_eq_iff_eq_of_isPos (hs : θ.IsPos) (hp : ψ.IsPos) : cos θ = cos ψ ↔ θ = ψ :=
  cos_eq_iff_eq_or_eq_neg.trans (or_iff_left (ne_neg_of_isPos hs hp))

theorem cos_eq_iff_eq_of_isNeg (hs : θ.IsNeg) (hp : ψ.IsNeg) : cos θ = cos ψ ↔ θ = ψ :=
  cos_eq_iff_eq_or_eq_neg.trans (or_iff_left (ne_neg_of_isNeg hs hp))

theorem sin_eq_iff_eq_of_isAcu (hs : θ.IsAcu) (hp : ψ.IsAcu) : sin θ = sin ψ ↔ θ = ψ :=
  sin_eq_iff_eq_or_add_eq_pi.trans (or_iff_left (add_ne_pi_of_isAcu hs hp))

theorem sin_eq_iff_eq_of_isObt (hs : θ.IsObt) (hp : ψ.IsObt) : sin θ = sin ψ ↔ θ = ψ :=
  sin_eq_iff_eq_or_add_eq_pi.trans (or_iff_left (add_ne_pi_of_isObt hs hp))

end trigonometric

end AngValue



namespace AngDValue

section double

def Double : AngDValue → AngValue :=
  (AddCircle.equivAddCircle π (2 * π) pi_ne_zero (ne_of_gt two_pi_pos)).toFun
-- def AngDValue.Double : AngDValue → AngValue := Quotient.lift (fun x : ℝ => Real.toAngValue (2 * x)) sorry

def DoubleHom : AngDValue →+ AngValue :=
  (AddCircle.equivAddCircle π (2 * π) pi_ne_zero (ne_of_gt two_pi_pos)).toAddMonoidHom

@[simp]
theorem doubleHom_toFun_eq_double : DoubleHom.toFun = Double := rfl

-- `Do we need a AngValue.Halve function?`

-- `This section needs following theorems @[simp] direction is always to target`

section special_value
-- AngDValue.Double special value
-- composites of these two map

@[simp]
theorem zero_double : (0 : AngDValue).Double = 0 := map_zero DoubleHom

theorem double_coe_coe_eq_coe_mul_two (x : ℝ) : ∡[x].Double = ∠[x * 2] := by
  refine' (AddCircle.equivAddCircle_apply_mk π (2 * π) pi_ne_zero _ x).trans _
  field_simp
  rfl

theorem real_div_two_double (x : ℝ) : ∡[x / 2].Double = x := by
  rw [double_coe_coe_eq_coe_mul_two, div_mul_cancel x two_ne_zero]

theorem pi_div_two_double : ∡[π / 2].Double = π := real_div_two_double π

theorem _root_.AngValue.double_coe_eq_two_nsmul : (θ : AngDValue).Double = 2 • θ := by
  rw [← θ.coe_toReal, double_coe_coe_eq_coe_mul_two, ← AngValue.coe_nsmul, mul_comm, nsmul_eq_mul, Nat.cast_ofNat]

theorem coe_double_eq_two_nsmul {θ : AngDValue} : θ.Double = 2 • θ := by
  induction θ using AngDValue.induction_on
  rw [AngValue.double_coe_eq_two_nsmul, coe_nsmul]

end special_value

section group_hom
-- AngDValue.Double is group hom (add neg sub nsmul zsmul) (use AddCircle.equivAddCircle)

@[simp]
theorem double_add {x y : AngDValue} : (x + y).Double = x.Double + y.Double :=
  map_add DoubleHom x y

@[simp]
theorem double_neg {x : AngDValue} : (- x).Double = - x.Double := map_neg DoubleHom x

@[simp]
theorem double_sub {x y : AngDValue} : (x - y).Double = x.Double - y.Double :=
  map_sub DoubleHom x y

@[simp]
theorem double_nsmul (n : ℕ) {x : AngDValue} : (n • x).Double = n • x.Double := map_nsmul DoubleHom n x

@[simp]
theorem double_zsmul (n : ℤ) {x : AngDValue} : (n • x).Double = n • x.Double := map_zsmul DoubleHom n x

@[simp]
theorem double_inj {x y : AngDValue} : x.Double = y.Double ↔ x = y :=
  (AddCircle.equivAddCircle π (2 * π) pi_ne_zero (ne_of_gt two_pi_pos)).injective.eq_iff

end group_hom

end double

end AngDValue



lemma _root_.Real.div_nat_le_self_of_nonnneg {a : ℝ} (n : ℕ) (h : 0 ≤ a) : a / n ≤ a := by
  show a * (↑n)⁻¹ ≤ a
  refine' mul_le_of_le_one_right h _
  by_cases h : n = 0
  · simp only [h, CharP.cast_eq_zero, inv_zero, zero_le_one]
  exact inv_le_one (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr h))

lemma _root_.Real.div_nat_le_self_of_pos {a : ℝ} (n : ℕ) (h : 0 < a) : a / n ≤ a :=
  a.div_nat_le_self_of_nonnneg n (le_of_lt h)

lemma _root_.Real.div_nat_lt_self_of_pos_of_two_le {a : ℝ} {n : ℕ} (h : 0 < a) (hn : 2 ≤ n) : a / n < a :=
  mul_lt_of_lt_one_right h (inv_lt_one (Nat.one_lt_cast.mpr hn))

lemma _root_.Real.pi_div_nat_nonneg (n : ℕ) : 0 ≤ π / n :=
  div_nonneg (le_of_lt pi_pos) (Nat.cast_nonneg n)



namespace AngValue

section abs
/-
-- Is this definition useful?
instance AngValue.instAbs : Abs AngValue where
  abs θ := ∠[|θ.toReal|]
variable (θ : AngValue)
#check |θ|
-- `We shall wait and see what congruence will become`
-/

/-- The absolute value of an angle $θ$ is the absolute value of $θ.toReal$. -/
def abs (θ : AngValue) : ℝ := |θ.toReal|

theorem zero_le_abs : 0 ≤ θ.abs := abs_nonneg θ.toReal

theorem abs_le_pi : θ.abs ≤ π := abs_toReal_le_pi θ

theorem neg_pi_lt_abs : - π < θ.abs :=
  LT.lt.trans_le (by linarith [pi_pos]) θ.zero_le_abs

theorem coe_abs_eq_abs {x : ℝ} (hn : - π < x) (h : x ≤ π) : ∠[x].abs = |x| :=
  congrArg Abs.abs (toReal_coe_eq_self hn h)

theorem coe_abs_eq_abs_of_abs_le_pi {x : ℝ} (h : |x| ≤ π) : ∠[x].abs = |x| :=
  if hp : x = - π then by
    rw [hp, abs_neg, coe_neg, AngValue.neg_coe_pi]
    exact coe_abs_eq_abs (by linarith [pi_pos]) (Eq.ge rfl)
  else coe_abs_eq_abs (Ne.lt_of_le' hp (neg_le_of_abs_le h)) (le_of_abs_le h)

theorem coe_abs_le_abs (x : ℝ) : ∠[x].abs ≤ |x| :=
  if h : |x| ≤ π then (coe_abs_eq_abs_of_abs_le_pi h).le
  else (∠[x].abs_le_pi).trans (le_of_not_le h)

theorem abs_min {x : ℝ} (h : θ = ∠[x]) : θ.abs ≤ |x| := by
  rw [h]
  exact coe_abs_le_abs x

theorem eq_coe_or_neg_coe_of_abs_eq {x : ℝ} (h : θ.abs = x) : θ = ∠[x] ∨ θ = - ∠[x] := by
  rcases eq_or_eq_neg_of_abs_eq h with h | h
  · rw [← h]
    exact .inl θ.coe_toReal.symm
  · rw [← coe_neg, ← h]
    exact .inr θ.coe_toReal.symm

theorem abs_eq_toReal_or_neg_toeal : θ.abs = θ.toReal ∨ θ.abs = - θ.toReal :=
  abs_choice θ.toReal

theorem coe_abs_eq_self_or_neg : ∠[θ.abs] = θ ∨ ∠[θ.abs] = - θ := by
  rcases θ.abs_eq_toReal_or_neg_toeal with h | h
  · rw [h]
    exact .inl θ.coe_toReal
  · rw [h, coe_neg]
    exact .inr (neg_inj.mpr θ.coe_toReal)

section special_value

theorem zero_abs : (0 : AngValue).abs = 0 := by
  rw [abs, toReal_zero, abs_zero]

theorem abs_eq_zero_iff_eq_zero : θ.abs = 0 ↔ θ = 0 :=
  abs_eq_zero.trans toReal_eq_zero_iff

theorem abs_ne_zero_iff_ne_zero : θ.abs ≠ 0 ↔ θ ≠ 0 := abs_eq_zero_iff_eq_zero.not

theorem zero_lt_abs_iff_ne_zero : 0 < θ.abs ↔ θ ≠ 0 :=
  ((θ.zero_le_abs).gt_iff_ne).trans abs_ne_zero_iff_ne_zero

theorem pi_abs : (π : AngValue).abs = π := by
  rw [abs, toReal_pi, abs_eq_self.mpr (le_of_lt Real.pi_pos)]

theorem eq_pi_of_abs_eq_pi (h : θ.abs = π) : θ = π :=
  toReal_eq_pi_iff.mp ((or_iff_left (ne_of_gt θ.neg_pi_lt_toReal)).mp (eq_or_eq_neg_of_abs_eq h))

theorem abs_eq_pi_iff_eq_pi : θ.abs = π ↔ θ = π :=
  ⟨eq_pi_of_abs_eq_pi, fun h ↦ (congrArg abs h).trans pi_abs⟩

theorem abs_ne_pi_iff_ne_pi : θ.abs ≠ π ↔ θ ≠ π := abs_eq_pi_iff_eq_pi.not

theorem abs_lt_pi_iff_ne_pi : θ.abs < π ↔ θ ≠ π :=
  ((θ.abs_le_pi).lt_iff_ne).trans abs_ne_pi_iff_ne_pi

theorem pi_div_two_abs : ∠[π / 2].abs = π / 2 := by
  rw [abs, toReal_pi_div_two]
  exact abs_eq_self.mpr (pi_div_nat_nonneg 2)

theorem abs_eq_pi_div_two_of_eq_pi_div_two (h : θ = ∠[π / 2]) : θ.abs = π / 2 :=
  (congrArg abs h).trans pi_div_two_abs

theorem neg_pi_div_two_abs : ∠[- π / 2].abs = π / 2 := by
  rw [abs, toReal_neg_pi_div_two, ← neg_neg (π / 2), neg_div 2 π, abs_neg, neg_neg, abs_eq_self]
  exact pi_div_nat_nonneg 2

theorem abs_eq_pi_div_two_of_eq_neg_pi_div_two (h : θ = ∠[- π / 2]) : θ.abs = π / 2 :=
  (congrArg abs h).trans neg_pi_div_two_abs

end special_value

section abs_eq_iff

theorem abs_eq_iff {α β : AngValue} : α.abs = β.abs ↔ α = β ∨ α = - β :=
  if h : β = π then by
    rw [h, pi_abs]
    exact abs_eq_pi_iff_eq_pi.trans (or_iff_left_of_imp (fun h ↦ h.trans neg_coe_pi)).symm
  else abs_eq_abs.trans (or_congr toReal_inj ((neg_toReal h).congr_right.symm.trans toReal_inj))

theorem abs_congr {α β : AngValue} (h : α = β) : α.abs = β.abs := abs_eq_iff.mpr (.inl h)

end abs_eq_iff

section pos_neg_nd

theorem zero_lt_abs_lt_pi_iff_isND : 0 < θ.abs ∧ θ.abs < π ↔ θ.IsND :=
  ((θ.zero_lt_abs_iff_ne_zero).and θ.abs_lt_pi_iff_ne_pi).trans (θ.isND_iff).symm

theorem coe_abs_not_isNeg : ¬ ∠[θ.abs].IsNeg :=
  coe_not_isNeg_of_zero_le_self_le_pi zero_le_abs abs_le_pi

theorem coe_abs_isPos_iff_isND : ∠[θ.abs].IsPos ↔ θ.IsND := by
  rw [isPos_iff, toReal_coe_eq_self neg_pi_lt_abs abs_le_pi, zero_lt_abs_lt_pi_iff_isND]

theorem coe_abs_isPos_of_isPos (h : θ.IsPos) : ∠[θ.abs].IsPos :=
  coe_abs_isPos_iff_isND.mpr (isND_of_isPos h)

theorem abs_eq_toReal_of_not_isNeg (h : ¬ θ.IsNeg) : θ.abs = θ.toReal :=
  abs_eq_self.mpr (not_isNeg_iff.mp h)

theorem coe_abs_eq_self_of_not_isNeg (h : ¬ θ.IsNeg) : ∠[θ.abs] = θ := by
  rw [abs_eq_toReal_of_not_isNeg h, coe_toReal]

theorem abs_eq_toReal_of_isPos (h : θ.IsPos) : θ.abs = θ.toReal :=
  abs_eq_toReal_of_not_isNeg (not_isNeg_of_isPos h)

theorem coe_abs_eq_self_of_isPos (h : θ.IsPos) : ∠[θ.abs] = θ :=
  coe_abs_eq_self_of_not_isNeg (not_isNeg_of_isPos h)

theorem abs_eq_toReal_of_isND (h : ¬ θ.IsND) : θ.abs = θ.toReal :=
  abs_eq_toReal_of_not_isNeg (not_isNeg_of_not_isND h)

theorem coe_abs_eq_self_of_isND (h : ¬ θ.IsND) : ∠[θ.abs] = θ :=
  coe_abs_eq_self_of_not_isNeg (not_isNeg_of_not_isND h)

theorem abs_eq_neg_toReal_of_isNeg (h : θ.IsNeg) : θ.abs = - θ.toReal :=
  abs_of_neg (isNeg_iff.mp h)

theorem coe_abs_eq_neg_of_isNeg (h : θ.IsNeg) : ∠[θ.abs] = - θ := by
  rw [abs_eq_neg_toReal_of_isNeg h, coe_neg, coe_toReal]

theorem not_isNeg_of_abs_eq_toReal (h : θ.abs = θ.toReal) : ¬ θ.IsNeg :=
  not_isNeg_iff.mpr (abs_eq_self.mp h)

theorem not_isNeg_of_coe_abs_eq_self (h : ∠[θ.abs] = θ) : ¬ θ.IsNeg := by
  apply not_isNeg_of_abs_eq_toReal
  rw [← toReal_coe_eq_self neg_pi_lt_abs abs_le_pi, h]

theorem abs_eq_toReal_iff : θ.abs = θ.toReal ↔ ¬ θ.IsNeg :=
  ⟨not_isNeg_of_abs_eq_toReal, abs_eq_toReal_of_not_isNeg⟩

theorem abs_ne_toReal_iff : θ.abs ≠ θ.toReal ↔ θ.IsNeg :=
  (θ.abs_eq_toReal_iff).not.trans not_not

theorem coe_abs_eq_neg_iff_isNeg : ∠[θ.abs] = θ ↔ ¬ θ.IsNeg :=
  ⟨not_isNeg_of_coe_abs_eq_self, coe_abs_eq_self_of_not_isNeg⟩

theorem coe_abs_ne_neg_iff_not_isNeg : ∠[θ.abs] ≠ θ ↔ θ.IsNeg :=
  coe_abs_eq_neg_iff_isNeg.not.trans not_not

theorem eq_of_isPos_of_abs_eq (hs : θ.IsPos) (hp : ψ.IsPos) (h : θ.abs = ψ.abs) : θ = ψ :=
  (or_iff_left (ne_neg_of_isPos hs hp)).mp (abs_eq_iff.mp h)

theorem eq_of_isNeg_of_abs_eq (hs : θ.IsNeg) (hp : ψ.IsNeg) (h : θ.abs = ψ.abs) : θ = ψ :=
  (or_iff_left (ne_neg_of_isNeg hs hp)).mp (abs_eq_iff.mp h)

end pos_neg_nd

section acute_obtuse

theorem coe_abs_isAcu_iff_isAcu : ∠[θ.abs].IsAcu ↔ θ.IsAcu := by
  refine' Or.casesOn coe_abs_eq_self_or_neg (fun h ↦ iff_of_eq (congrArg IsAcu h)) fun h ↦ _
  rw [h]
  exact neg_isAcu_iff_isAcu

theorem coe_abs_isObt_iff_isObt : ∠[θ.abs].IsObt ↔ θ.IsObt := by
  refine' Or.casesOn coe_abs_eq_self_or_neg (fun h ↦ iff_of_eq (congrArg IsObt h)) fun h ↦ _
  rw [h]
  exact neg_isObt_iff_isObt

theorem coe_abs_isRight_iff_isRight : ∠[θ.abs].IsRight ↔ θ.IsRight :=  by
  refine' Or.casesOn coe_abs_eq_self_or_neg (fun h ↦ iff_of_eq (congrArg IsRight h)) fun h ↦ _
  rw [h]
  exact neg_isRight_iff_isRight

theorem isRight_iff_abs_eq_pi_div_two : θ.IsRight ↔ θ.abs = π / 2 := by
  refine' ⟨fun h ↦ h.casesOn (fun h ↦ abs_eq_pi_div_two_of_eq_neg_pi_div_two h)
    (fun h ↦ abs_eq_pi_div_two_of_eq_pi_div_two h),
    fun h ↦ (eq_coe_or_neg_coe_of_abs_eq h).casesOn (fun h ↦ isRight_of_eq_pi_div_two h) fun h ↦ _⟩
  rw [neg_coe_pi_div_two] at h
  exact isRight_of_eq_neg_pi_div_two h

theorem isAcu_iff_abs_lt_pi_div_two : θ.IsAcu ↔ θ.abs < π / 2 := by
  refine' (θ.isAcu_iff).trans _
  rw [neg_div]
  exact abs_lt.symm

theorem not_isAcu_iff_pi_div_two_le_abs : ¬ θ.IsAcu ↔ π / 2 ≤ θ.abs := by
  refine' (θ.not_isAcu_iff).trans _
  rw [neg_div]
  exact le_abs'.symm

theorem isObt_iff_pi_div_two_lt_abs : θ.IsObt ↔ π / 2 < θ.abs := by
  refine' (θ.isObt_iff).trans (or_comm.trans _)
  rw [neg_div, lt_neg]
  exact lt_abs.symm

theorem not_isObt_iff_abs_le_pi_div_two : ¬ θ.IsObt ↔ θ.abs ≤ π / 2 := by
  refine' (θ.not_isObt_iff).trans _
  rw [neg_div]
  exact abs_le.symm

theorem abs_lt_of_isAcu_of_isObt (hs : θ.IsAcu) (hp : ψ.IsObt) : θ.abs < ψ.abs :=
  (isAcu_iff_abs_lt_pi_div_two.mp hs).trans (isObt_iff_pi_div_two_lt_abs.mp hp)

theorem abs_le_of_not_isObt_of_not_isAcu (hs : ¬ θ.IsObt) (hp : ¬ ψ.IsAcu) : θ.abs ≤ ψ.abs :=
  (not_isObt_iff_abs_le_pi_div_two.mp hs).trans (not_isAcu_iff_pi_div_two_le_abs.mp hp)

end acute_obtuse

section norm

/-- The absolute value of an angle is equal to its norm. -/
theorem abs_eq_norm : θ.abs = ‖θ‖ := by
  apply le_antisymm
  · refine' le_csInf ⟨θ.abs, θ.toReal, θ.coe_toReal, rfl⟩ (fun a h ↦ _)
    rcases h with ⟨_, h, hn⟩
    exact (abs_min h.symm).trans_eq hn
  · refine' csInf_le ⟨0, fun a h ↦ _⟩ ⟨θ.toReal, θ.coe_toReal, rfl⟩
    rcases h with ⟨x, _, h⟩
    exact (norm_nonneg x).trans_eq h

@[simp]
theorem abs_neg : (- θ).abs = θ.abs := by rw [abs_eq_norm, abs_eq_norm, norm_neg]

theorem abs_add_le : (θ + ψ).abs ≤ θ.abs + ψ.abs := by simp only [abs_eq_norm, norm_add_le θ ψ]

end norm

end abs



section half

/-- Half of an angle. Note that there are two possible values when dividing by two in `AngValue`
(their difference is `π`). We choose the acute angle as the canonical value for half of an angle
for angles not equal to `π`, and the half of `π` is defined as `π / 2`. -/
def half (θ : AngValue) : AngValue := ∠[θ.toReal / 2]
-- Do we need the other value obatined by dividing by two, i.e., `θ.half + π`?
-- Do we need a class `IsHalf`?

theorem coe_half {x : ℝ} (hn : - π < x) (h : x ≤ π) : ∠[x].half = ∠[x / 2] :=
  congrArg AngValue.coe (congrFun (congrArg HDiv.hDiv (toReal_coe_eq_self hn h)) 2)

@[simp]
theorem two_nsmul_half : 2 • θ.half = θ := θ.two_nsmul_toReal_div_two

theorem two_nsmul_eq_iff_eq_half_or_eq_half_add_pi : 2 • ψ = θ ↔ ψ = θ.half ∨ ψ = θ.half + π := by
  nth_rw 1 [← θ.two_nsmul_half]
  exact two_nsmul_eq_iff

theorem two_nsmul_half_add_pi : 2 • (θ.half + π) = θ := by
  rw [smul_add, two_nsmul_coe_pi, add_zero, two_nsmul_half]

theorem sub_half_eq_half : θ - θ.half = θ.half :=
  sub_eq_of_eq_add (two_nsmul_half.symm.trans (two_nsmul θ.half))

@[simp]
theorem half_toReal : θ.half.toReal = θ.toReal / 2 :=
  toReal_coe_eq_self (by linarith [θ.neg_pi_lt_toReal, pi_pos]) (by linarith [θ.toReal_le_pi, pi_pos])

theorem half_toReal_le_two_inv_mul_pi : θ.half.toReal ≤ π / 2 :=
  (θ.half_toReal).trans_le ((div_le_div_right (by norm_num)).mpr θ.toReal_le_pi)

theorem half_toReal_lt_two_inv_mul_pi_of_ne_pi (h : θ ≠ π) : θ.half.toReal < π / 2 :=
  (θ.half_toReal).trans_lt ((div_lt_div_right (by norm_num)).mpr (toReal_lt_pi_of_ne_pi h))

theorem neg_two_inv_mul_pi_lt_half_toReal : - π / 2 < θ.half.toReal :=
  ((div_lt_div_right (by norm_num)).mpr θ.neg_pi_lt_toReal).trans_eq (θ.half_toReal).symm

theorem half_toReal_lt_pi : θ.half.toReal < π :=
  (θ.half_toReal_le_two_inv_mul_pi).trans_lt (by linarith [pi_pos])

theorem eq_two_mul_coe_of_half_toReal_eq {x : ℝ} (h : θ.half.toReal = x) : θ = ∠[2 * x] := by
  rw [← h, half_toReal, mul_div_cancel' θ.toReal two_ne_zero, θ.coe_toReal]

theorem half_inj {α β : AngValue} (h : α.half = β.half) : α = β :=
  toReal_inj.mp ((div_left_inj' (by norm_num)).mp <|
    ((α.half_toReal).symm.trans (congrArg toReal h)).trans β.half_toReal)

@[simp]
theorem half_congr {α β : AngValue} : α.half = β.half ↔ α = β := ⟨half_inj, congrArg half⟩

theorem half_neg (h : θ ≠ π) : (- θ).half = - θ.half := by
  rw [half, half, neg_toReal h, ← coe_neg, neg_div]

theorem half_neg_of_isND (h : θ.IsND) : (- θ).half = - θ.half := half_neg h.2

section special_value

@[simp]
theorem zero_half : (0 : AngValue).half = 0 := by
  rw [half, toReal_zero, zero_div, coe_zero]

theorem eq_zero_of_half_eq_zero (h : θ.half = 0) : θ = 0 := half_inj (h.trans zero_half.symm)

@[simp]
theorem half_eq_zero_iff_eq_zero : θ.half = 0 ↔ θ = 0 :=
  ⟨eq_zero_of_half_eq_zero, fun h ↦ (half_congr.mpr h).trans zero_half⟩

@[simp]
theorem pi_half : ∠[π].half = ∠[π / 2] := coe_half (by norm_num [pi_pos]) (Eq.ge rfl)

theorem eq_pi_of_half_eq_pi (h : θ.half = ∠[π / 2]) : θ = π :=
  half_inj (h.trans pi_half.symm)

@[simp]
theorem half_eq_pi_iff_eq_pi : θ.half = ∠[π / 2] ↔ θ = π :=
  ⟨eq_pi_of_half_eq_pi, fun h ↦ (half_congr.mpr h).trans pi_half⟩

theorem half_pi_div_nat (n : ℕ) : ∠[π / n].half = ∠[π / (n * 2)] :=
  (coe_half ((neg_lt_zero.2 pi_pos).trans_le (pi_div_nat_nonneg n))
    (div_nat_le_self_of_pos n pi_pos)).trans (by field_simp)

theorem pi_div_two_half : ∠[π / 2].half = ∠[π / 4] :=
  (half_pi_div_nat 2).trans (by norm_num)

theorem pi_div_three_half : ∠[π / 3].half = ∠[π / 6] :=
  (half_pi_div_nat 3).trans (by norm_num)

theorem half_neg_pi_div_nat {n : ℕ} (h : 2 ≤ n) : ∠[- π / n].half = ∠[- π / (n * 2)] := by
  rw [neg_div]
  exact (coe_half (neg_lt_neg (div_nat_lt_self_of_pos_of_two_le pi_pos h))
    ((neg_nonpos.mpr (pi_div_nat_nonneg n)).trans (le_of_lt pi_pos))).trans (by field_simp)

theorem neg_pi_div_two_half : ∠[- π / 2].half = ∠[- π / 4] :=
  (half_neg_pi_div_nat (le_of_eq rfl)).trans (by norm_num)

theorem neg_pi_div_three_half : ∠[- π / 3].half = ∠[- π / 6] :=
  (half_neg_pi_div_nat Nat.AtLeastTwo.prop).trans (by norm_num)

end special_value

section pos_neg

theorem half_isPos_of_isPos (h : θ.IsPos) : θ.half.IsPos := by
  refine' isPos_iff.mpr ⟨_, θ.half_toReal_lt_pi⟩
  rw [half_toReal]
  linarith [zero_lt_toReal_of_isPos h]

theorem half_isNeg_iff_isNeg : θ.half.IsNeg ↔ θ.IsNeg := by
  refine' isNeg_iff.trans (Iff.trans _ isNeg_iff.symm)
  nth_rw 1 [half_toReal, ← zero_div (2 : ℝ), div_lt_div_right (by norm_num)]

end pos_neg

section acute_obtuse

theorem half_not_isObt : ¬ θ.half.IsObt :=
  not_isObt_iff.mpr ⟨le_of_lt θ.neg_two_inv_mul_pi_lt_half_toReal, θ.half_toReal_le_two_inv_mul_pi⟩

theorem half_isAcu_of_ne_pi (h : θ ≠ π) : θ.half.IsAcu :=
  isAcu_iff.mpr ⟨θ.neg_two_inv_mul_pi_lt_half_toReal, half_toReal_lt_two_inv_mul_pi_of_ne_pi h⟩

theorem half_add_pi_not_isAcu : ¬ (θ.half + π).IsAcu :=
  add_pi_isAcu_iff_isObt.not.mpr (θ.half_not_isObt)

theorem half_add_pi_isObt_of_ne_pi (h : θ ≠ π) : (θ.half + π).IsObt :=
  add_pi_isObt_iff_isAcu.mpr (half_isAcu_of_ne_pi h)

end acute_obtuse

section sin_cos

theorem abs_sin_half : |sin θ.half| = sqrt ((1 - cos θ) / 2) :=
  (Real.abs_sin_half θ.toReal).trans (by rw [θ.cos_toReal])

theorem sin_half_of_not_isNeg (h : ¬ θ.IsNeg) : sin θ.half = sqrt ((1 - cos θ) / 2) :=
  (abs_of_nonneg (not_isNeg_iff_zero_le_sin.mp (half_isNeg_iff_isNeg.not.mpr h))).symm.trans θ.abs_sin_half

theorem sin_half_of_isPos (h : θ.IsPos) : sin θ.half = sqrt ((1 - cos θ) / 2) :=
  sin_half_of_not_isNeg (not_isNeg_of_isPos h)

theorem sin_half_of_isNeg (h : θ.IsNeg) : sin θ.half = - sqrt ((1 - cos θ) / 2) :=
  neg_eq_iff_eq_neg.mp <|
    (abs_of_neg (sin_lt_zero_of_isNeg (half_isNeg_iff_isNeg.mpr h))).symm.trans θ.abs_sin_half

theorem cos_half : cos θ.half = sqrt ((1 + cos θ) / 2) :=
  (Real.cos_half θ.neg_pi_le_toReal θ.toReal_le_pi).trans (by rw [θ.cos_toReal])

-- Do we need tangent half-angle formulas (such as formulas in https://en.wikipedia.org/wiki/Tangent_half-angle_formula)?

end sin_cos

section sum_to_product
-- The sum-to-product formulas should be put here since they involve half of angles.

variable (ψ : AngValue)

theorem sin_sub_sin : sin θ - sin ψ = 2 * (sin (θ.half - ψ.half) * cos (θ.half + ψ.half)) := by
  rw [← mul_assoc, ← sin_toReal, ← sin_toReal, half, half, ← coe_add, ← coe_sub, ← sub_div, ← add_div]
  exact (θ.toReal).sin_sub_sin ψ.toReal

theorem cos_half_mul_sin_half : 2 * (cos θ.half * sin θ.half) = sin θ := by
  have h := θ.sin_sub_sin π
  simp only [sin_coe, sin_pi, sub_zero, pi_half, sin_sub_pi_div_two, cos_add_pi_div_two, mul_neg,
    neg_mul, neg_neg] at h
  exact h.symm

theorem sin_half_mul_cos_half : 2 * (sin θ.half * cos θ.half) = sin θ := by
  rw [mul_comm (sin (half θ)) (cos (half θ))]
  exact θ.cos_half_mul_sin_half

theorem sin_add_sin : sin θ + sin ψ = 2 * (sin (θ.half + ψ.half) * cos (θ.half - ψ.half)) := by
  by_cases h : ψ = π
  · simp only [h, sin_coe, sin_pi, add_zero, pi_half, sin_add_pi_div_two, cos_sub_pi_div_two]
    exact (θ.cos_half_mul_sin_half).symm
  · have eq := θ.sin_sub_sin (- ψ)
    simp only [sin_neg, sub_neg_eq_add, half_neg h] at eq
    exact eq

theorem cos_sub_cos : cos θ - cos ψ = - 2 * (sin (θ.half + ψ.half) * sin (θ.half - ψ.half)) := by
  rw [← mul_assoc, ← cos_toReal, ← cos_toReal, half, half, ← coe_add, ← coe_sub, ← sub_div, ← add_div]
  exact (θ.toReal).cos_sub_cos ψ.toReal

theorem cos_add_cos : cos θ + cos ψ = 2 * (cos (θ.half + ψ.half) * cos (θ.half - ψ.half)) := by
  rw [← mul_assoc, ← cos_toReal, ← cos_toReal, half, half, ← coe_add, ← coe_sub, ← sub_div, ← add_div]
  exact (θ.toReal).cos_add_cos ψ.toReal

end sum_to_product

section abs

theorem half_abs : θ.half.abs = θ.abs / 2 :=
  (congrArg Abs.abs θ.half_toReal).trans <| (abs_mul θ.toReal 2⁻¹).trans <|
    congrArg (HMul.hMul θ.abs) (abs_of_pos (by norm_num))

theorem half_abs_le_pi_div_two : θ.half.abs ≤ π / 2 :=
  not_isObt_iff_abs_le_pi_div_two.mp θ.half_not_isObt

theorem half_abs_lt_pi_div_two_of_ne_pi (h : θ ≠ π) : θ.half.abs < π / 2 :=
  isAcu_iff_abs_lt_pi_div_two.mp (half_isAcu_of_ne_pi h)

theorem half_abs_le_half_add_pi_abs : θ.half.abs ≤ (θ.half + π).abs :=
  abs_le_of_not_isObt_of_not_isAcu θ.half_not_isObt θ.half_add_pi_not_isAcu

theorem half_abs_min (h : 2 • ψ = θ) : θ.half.abs ≤ ψ.abs :=
  (two_nsmul_eq_iff_eq_half_or_eq_half_add_pi.mp h).casesOn (fun h ↦ Eq.ge (congrArg abs h)) <| by
  intro h
  rw [h]
  exact half_abs_le_half_add_pi_abs

end abs

end half

end AngValue

end EuclidGeom
