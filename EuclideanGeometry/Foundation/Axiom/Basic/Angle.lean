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
open Real.Angle Classical Real

noncomputable section
namespace EuclidGeom

attribute [pp_dot] AngValue.toReal

def AngDValue := AddCircle π

namespace AngDValue

instance : NormedAddCommGroup AngDValue :=
  inferInstanceAs (NormedAddCommGroup (AddCircle π))

instance : Inhabited AngDValue :=
  inferInstanceAs (Inhabited (AddCircle π))

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
  QuotientAddGroup.circularOrder (hp' := ⟨by norm_num [pi_pos]⟩)

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

end AngDValue

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


namespace AngValue

section
-- some supplementary lemma not explicitly written in mathlib

theorem toReal_lt_pi_of_ne_pi {θ : AngValue} (h : θ ≠ π) : θ.toReal < π := by
  contrapose! h
  exact toReal_eq_pi_iff.mp (le_antisymm θ.toReal_le_pi h)

theorem neg_pi_lt_toReal_le_pi {θ : AngValue} : -π < θ.toReal ∧ θ.toReal ≤ π :=
  AngValue.toReal_mem_Ioc _ -- to make those unfamiliar with Ioc easy to use
  -- ⟨θ.neg_pi_lt_toReal, θ.toReal_le_pi⟩

end

section composite

@[simp]
theorem toReal_coe_eq_self {r : ℝ} (h₁ : -π < r) (h₂ : r ≤ π) : ∠[r].toReal = r :=
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
theorem neg_toReal {θ : AngValue} (h : θ ≠ π) : (-θ).toReal = - θ.toReal := by
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
  apply ne_of_eq_of_ne (b := ∠[-π / 2])
  congr
  ring
  exact neg_pi_div_two_ne_zero

theorem neg_pi_div_two_ne_pi : ∠[-π / 2] ≠ ∠[π] := by
  rw [← neg_coe_pi]
  apply sub_ne_zero.mp
  norm_cast
  apply ne_of_eq_of_ne (b := ∠[π / 2])
  congr
  ring
  exact pi_div_two_ne_zero

end special_value

section group_hom

@[simp]
theorem two_nsmul_toReal_div_two {θ : AngValue} : 2 • ∠[θ.toReal / 2] = θ := by
  nth_rw 2 [← θ.coe_toReal]
  exact two_nsmul_coe_div_two θ.toReal

@[simp]
theorem two_nsmul_toReal_two_inv_mul {θ : AngValue} : 2 • ∠[θ.toReal / 2] = θ := by
  nth_rw 2 [← θ.coe_toReal]
  exact two_nsmul_coe_div_two θ.toReal

@[simp]
theorem two_zsmul_toReal_div_two {θ : AngValue} : (2 : ℤ) • ∠[θ.toReal / 2] = θ :=
  θ.two_nsmul_toReal_div_two

end group_hom

section pos_neg_isND

-- variant of `AngValue.sign`,
-- `Maybe this section should be rewrite using AngValue.sign to have more complete api's`
-- `Or just check Real.Angle.sign to write more api's, IsPos IsNeg is more similar to human language than sign`

@[pp_dot]
def IsPos (θ : AngValue) : Prop := sbtw 0 θ π

@[pp_dot]
def IsNeg (θ : AngValue) : Prop := sbtw ∠[π] θ 0

@[pp_dot]
structure IsND (θ : AngValue) : Prop where intro ::
  ne_zero : θ ≠ 0
  ne_pi : θ ≠ π

section special_value

theorem not_zero_isPos : ¬ ∠[0].IsPos := sbtw_irrefl_left

theorem not_zero_isNeg : ¬ ∠[0].IsNeg := sbtw_irrefl_right

theorem not_zero_isND : ¬ ∠[0].IsND := fun nd ↦ nd.1 rfl

theorem not_isPos_of_eq_zero {θ : AngValue} (h : θ = 0) : ¬ θ.IsPos := by
  rw [h]
  exact not_zero_isPos

theorem ne_zero_of_isPos {θ : AngValue} (h : θ.IsPos) : θ ≠ 0 := fun hs ↦ not_isPos_of_eq_zero hs h

theorem not_isNeg_of_eq_zero {θ : AngValue} (h : θ = 0) : ¬ θ.IsNeg :=  by
  rw [h]
  exact not_zero_isNeg

theorem ne_zero_of_isNeg {θ : AngValue} (h : θ.IsNeg) : θ ≠ 0 := fun hs ↦ not_isNeg_of_eq_zero hs h

theorem not_isND_of_eq_zero {θ : AngValue} (h : θ = 0) : ¬ θ.IsND := fun nd ↦ nd.1 h

theorem not_pi_isPos : ¬ ∠[π].IsPos := sbtw_irrefl_right

theorem not_pi_isNeg : ¬ ∠[π].IsNeg := sbtw_irrefl_left

theorem not_pi_isND : ¬ ∠[π].IsND := fun nd ↦ nd.2 rfl

theorem not_isPos_of_eq_pi {θ : AngValue} (h : θ = π) : ¬ θ.IsPos :=  by
  rw [h]
  exact not_pi_isPos

theorem ne_pi_of_isPos {θ : AngValue} (h : θ.IsPos) : θ ≠ π := fun hs ↦ not_isPos_of_eq_pi hs h

theorem not_isNeg_of_eq_pi {θ : AngValue} (h : θ = π) : ¬ θ.IsNeg :=  by
  rw [h]
  exact not_pi_isNeg

theorem ne_pi_of_isNeg {θ : AngValue} (h : θ.IsNeg) : θ ≠ π := fun hs ↦ not_isNeg_of_eq_pi hs h

theorem not_isND_of_eq_pi {θ : AngValue} (h : θ = π) : ¬ θ.IsND := fun nd ↦ nd.2 h

theorem isND_iff {θ : AngValue} : θ.IsND ↔ θ ≠ 0 ∧ θ ≠ π :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

theorem not_isND_iff {θ : AngValue} : ¬ θ.IsND ↔ (θ = 0 ∨ θ = π) :=
  (not_iff_not.mpr θ.isND_iff).trans or_iff_not_and_not.symm

theorem isND_iff_two_nsmul_ne_zero {θ : AngValue} : θ.IsND ↔ 2 • θ ≠ 0 :=
  (θ.isND_iff).trans (θ.two_nsmul_ne_zero_iff).symm

theorem not_isND_iff_two_nsmul_eq_zero {θ : AngValue} : ¬ θ.IsND ↔ 2 • θ = 0 :=
  (θ.not_isND_iff).trans (θ.two_nsmul_eq_zero_iff).symm

end special_value

section trichotomy

theorem not_isNeg_of_isPos {θ : AngValue} (h : θ.IsPos) : ¬ θ.IsNeg := sbtw_asymm h

theorem isND_of_isPos {θ : AngValue} (h : θ.IsPos) : θ.IsND where
  ne_zero hs := not_isPos_of_eq_zero hs h
  ne_pi hs := not_isPos_of_eq_pi hs h

theorem not_isPos_of_isNeg {θ : AngValue} (h : θ.IsNeg) : ¬ θ.IsPos := sbtw_asymm h

theorem isND_of_isNeg {θ : AngValue} (h : θ.IsNeg) : θ.IsND where
  ne_zero hs := not_isNeg_of_eq_zero hs h
  ne_pi hs := not_isNeg_of_eq_pi hs h

theorem not_isPos_of_not_isND {θ : AngValue} (h : ¬ θ.IsND) : ¬ θ.IsPos := fun hs ↦ h (isND_of_isPos hs)

theorem not_isNeg_of_not_isND {θ : AngValue} (h : ¬ θ.IsND) : ¬ θ.IsNeg := fun hs ↦ h (isND_of_isNeg hs)

theorem isND_iff_isPos_or_isNeg {θ : AngValue} : θ.IsND ↔ θ.IsPos ∨ θ.IsNeg := by
  constructor
  · intro h
    contrapose! h
    have h := (and_congr btw_iff_not_sbtw btw_iff_not_sbtw).mpr h.symm
    rcases btw_antisymm (btw_cyclic_right h.1) (btw_cyclic_left h.2) with h | h
    · exact (pi_ne_zero h).elim
    · exact not_isND_iff.mpr ((or_congr_left eq_comm).mp h)
  · exact Or.elim (left := isND_of_isPos)  (right := isND_of_isNeg)


theorem not_isND_or_isPos_or_isNeg {θ : AngValue} : ¬ θ.IsND ∨ θ.IsPos ∨ θ.IsNeg :=
  if h : θ.IsND then .inr (isND_iff_isPos_or_isNeg.mp h) else .inl h

theorem not_isPos_iff_not_isND_or_isNeg {θ : AngValue} : ¬ θ.IsPos ↔ ¬ θ.IsND ∨ θ.IsNeg := by
  constructor
  · have _ := θ.not_isND_or_isPos_or_isNeg
    tauto
  · exact Or.elim (left := not_isPos_of_not_isND) (right := not_isPos_of_isNeg)

theorem not_isNeg_iff_not_isND_or_isPos {θ : AngValue} : ¬ θ.IsNeg ↔ ¬ θ.IsND ∨ θ.IsPos := by
  constructor
  · have _ := θ.not_isND_or_isPos_or_isNeg
    tauto
  · exact Or.elim (left := not_isNeg_of_not_isND) (right := not_isNeg_of_isPos)

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
  (Ne.symm <| toReal_eq_zero_iff.not.mpr <| ne_zero_of_isPos h).lt_of_le (zero_le_toReal_of_isPos h)

theorem toReal_lt_pi_of_isPos {θ : AngValue} (h : θ.IsPos) : θ.toReal < π :=
  (Ne.lt_of_le <| toReal_eq_pi_iff.not.mpr <| ne_pi_of_isPos h) θ.toReal_le_pi

theorem toReal_lt_zero_of_isNeg {θ : AngValue} (h : θ.IsNeg) : θ.toReal < 0 := by
  contrapose! h
  exact not_sbtw_of_btw (zero_le_toReal_iff.mp h)

theorem toReal_le_zero_of_isNeg {θ : AngValue} (h : θ.IsNeg) : θ.toReal ≤ 0 :=
  le_of_lt (toReal_lt_zero_of_isNeg h)

theorem isPos_of_zero_lt_toReal_of_ne_pi {θ : AngValue} (h : 0 < θ.toReal) (hn : θ ≠ π) : θ.IsPos :=
  Or.casesOn (isND_iff_isPos_or_isNeg.mp ⟨toReal_eq_zero_iff.not.mp (ne_of_gt h), hn⟩)
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

theorem isND_iff' {θ : AngValue} : θ.IsND ↔ (θ.toReal ≠ 0 ∧ θ.toReal ≠ π) := ⟨
  fun h ↦ ⟨toReal_eq_zero_iff.not.mpr h.1, toReal_eq_pi_iff.not.mpr h.2⟩,
  fun h ↦ ⟨toReal_eq_zero_iff.not.mp h.1 ,toReal_eq_pi_iff.not.mp h.2⟩⟩

theorem not_isND_iff' {θ : AngValue} : ¬ θ.IsND ↔ (θ.toReal = 0 ∨ θ.toReal = π) :=
  isND_iff'.not.trans (not_and_or.trans (or_congr not_ne_iff not_ne_iff))

end toReal

section sin

theorem zero_lt_sin_iff_isNeg {θ : AngValue} : θ.IsNeg ↔ sin θ < 0 :=
  isNeg_iff.trans (toReal_neg_iff_sign_neg.trans sign_eq_neg_one_iff)

theorem isND_iff_sin_ne_zero {θ : AngValue} : θ.IsND ↔ sin θ ≠ 0 :=
  isND_iff.trans (sign_ne_zero_iff.symm.trans sign_ne_zero)

theorem not_isND_iff_sin_eq_zero {θ : AngValue} : ¬ θ.IsND ↔ sin θ = 0 :=
  not_isND_iff.trans (Real.Angle.sign_eq_zero_iff.symm.trans _root_.sign_eq_zero_iff)

theorem sin_lt_zero_of_isNeg {θ : AngValue} (h : θ.IsNeg) : sin θ < 0 := zero_lt_sin_iff_isNeg.mp h

theorem isNeg_of_sin_lt_zero {θ : AngValue} (h : sin θ < 0) : θ.IsNeg := zero_lt_sin_iff_isNeg.mpr h

theorem sin_eq_zero_of_not_isND {θ : AngValue} (h : ¬ θ.IsND) : sin θ = 0 := not_isND_iff_sin_eq_zero.mp h

theorem not_isND_of_sin_eq_zero {θ : AngValue} (h : sin θ = 0) : ¬ θ.IsND := not_isND_iff_sin_eq_zero.mpr h

theorem sin_ne_zero_of_isND {θ : AngValue} (h : θ.IsND) : sin θ ≠ 0 := isND_iff_sin_ne_zero.mp h

theorem isND_of_sin_eq_zero {θ : AngValue} (h : sin θ ≠ 0) : θ.IsND := isND_iff_sin_ne_zero.mpr h

theorem zero_lt_sin_of_isPos {θ : AngValue} (h : θ.IsPos) : 0 < sin θ := by
  rw [← θ.coe_toReal]
  exact Real.sin_pos_of_pos_of_lt_pi (zero_lt_toReal_of_isPos h) (toReal_lt_pi_of_isPos h)

theorem isPos_of_zero_lt_sin {θ : AngValue} (h : 0 < sin θ) : θ.IsPos := by
  contrapose! h
  exact Or.casesOn (not_isPos_iff_not_isND_or_isNeg.mp h)
    (fun h ↦ (sin_eq_zero_of_not_isND h).symm.ge) (fun h ↦ le_of_lt (sin_lt_zero_of_isNeg h))

theorem zero_lt_sin_iff_isPos {θ : AngValue} : θ.IsPos ↔ 0 < sin θ :=
  ⟨zero_lt_sin_of_isPos, isPos_of_zero_lt_sin⟩

end sin

section pi_div_two

theorem pi_div_two_isPos : ∠[π / 2].IsPos :=
  isPos_of_zero_lt_sin (sign_eq_one_iff.mp sign_coe_pi_div_two)

theorem neg_pi_div_two_isNeg : ∠[- π / 2].IsNeg :=
  isNeg_of_sin_lt_zero (sign_eq_neg_one_iff.mp sign_coe_neg_pi_div_two)

end pi_div_two

section neg

@[simp]
theorem neg_isPos_iff_isNeg {θ : AngValue} : (-θ).IsPos ↔ θ.IsNeg :=
  zero_lt_sin_iff_isPos.trans (Iff.trans (by rw [sin_neg, Left.neg_pos_iff]) zero_lt_sin_iff_isNeg.symm)

@[simp]
theorem neg_isNeg_iff_isPos {θ : AngValue} : (-θ).IsNeg ↔ θ.IsPos :=
  zero_lt_sin_iff_isNeg.trans (Iff.trans (by rw [sin_neg, Left.neg_neg_iff]) zero_lt_sin_iff_isPos.symm)

@[simp]
theorem neg_isND_iff_isND {θ : AngValue} : (-θ).IsND ↔ θ.IsND :=
  isND_iff_sin_ne_zero.trans (Iff.trans (by rw [sin_neg, ne_eq, neg_eq_zero]) isND_iff_sin_ne_zero.symm)

end neg

section coe

theorem coe_isPos_of_zero_lt_self_lt_pi {x : ℝ} (h0 : 0 < x) (hp : x < π) : ∠[x].IsPos := by
  apply AngValue.isPos_iff.mpr
  rw [toReal_coe_eq_self (gt_trans h0 (by linarith)) (le_of_lt hp)]
  exact ⟨h0, hp⟩

theorem coe_isNeg_of_neg_pi_lt_self_lt_zero {x : ℝ} (hp : - π < x) (h0 : x < 0) : ∠[x].IsNeg :=
  AngValue.isNeg_iff.mpr ((toReal_coe_eq_self hp (le_of_lt (h0.trans Real.pi_pos))).trans_lt h0)

theorem coe_not_isNeg_of_zero_le_self_le_pi {x : ℝ} (h0 : 0 ≤ x) (hp : x ≤ π) : ¬ ∠[x].IsNeg :=
  AngValue.not_isNeg_iff.mpr <|
    (toReal_coe_eq_self (LT.lt.trans_le (by linarith [Real.pi_pos]) h0) hp).symm.trans_ge h0

end coe

end pos_neg_isND

section acute_obtuse_right

@[pp_dot]
def IsAcu (θ : AngValue) : Prop := sbtw ∠[-π / 2] θ ∠[π / 2]

@[pp_dot]
def IsObt (θ : AngValue) : Prop := sbtw ∠[π / 2] θ ∠[-π / 2]

@[pp_dot]
def IsRight (θ : AngValue) : Prop := θ = ∠[-π / 2] ∨ θ = ∠[π / 2]

section special_value
-- Special values for π / 2 and - π / 2.
-- The section related to 0 and π may need to be placed later.
-- theorem zero_isAcu : (0 : AngValue).IsAcu := sorry

theorem pi_div_two_not_isAcu : ¬ ∠[π / 2].IsAcu := sbtw_irrefl_right

theorem not_isAcu_of_eq_pi_div_two {θ : AngValue} (h : θ = ∠[π / 2]) : ¬ θ.IsAcu := by
  rw [h]
  exact pi_div_two_not_isAcu

theorem pi_div_two_not_isObt : ¬ ∠[π / 2].IsObt := sbtw_irrefl_left

theorem not_isObt_of_eq_pi_div_two {θ : AngValue} (h : θ = ∠[π / 2]) : ¬ θ.IsObt := by
  rw [h]
  exact pi_div_two_not_isObt

theorem neg_pi_div_two_not_isAcu : ¬ ∠[- π / 2].IsAcu := sbtw_irrefl_left

theorem not_isAcu_of_eq_neg_pi_div_two {θ : AngValue} (h : θ = ∠[- π / 2]) : ¬ θ.IsAcu := by
  rw [h]
  exact neg_pi_div_two_not_isAcu

theorem neg_pi_div_two_not_isObt : ¬ ∠[- π / 2].IsObt := sbtw_irrefl_right

theorem not_isObt_of_eq_neg_pi_div_two {θ : AngValue} (h : θ = ∠[- π / 2]) : ¬ θ.IsObt := by
  rw [h]
  exact neg_pi_div_two_not_isObt

theorem not_isRight_iff {θ : AngValue} : ¬ θ.IsRight ↔ θ ≠ ∠[- π / 2] ∧ θ ≠ ∠[π / 2] :=
  not_or

end special_value

section trichotomy

theorem not_isObt_of_isAcu {θ : AngValue} (h : θ.IsAcu) : ¬ θ.IsObt := sbtw_asymm h

theorem not_isAcu_of_isNeg {θ : AngValue} (h : θ.IsObt) : ¬ θ.IsAcu := sbtw_asymm h

theorem not_isAcu_of_not_isRight {θ : AngValue} (h : θ.IsRight) : ¬ θ.IsAcu :=
  Or.casesOn h (fun h ↦ not_isAcu_of_eq_neg_pi_div_two h) (fun h ↦ not_isAcu_of_eq_pi_div_two h)

theorem not_isObt_of_not_isRight {θ : AngValue} (h : θ.IsRight) : ¬ θ.IsObt :=
  Or.casesOn h (fun h ↦ not_isObt_of_eq_neg_pi_div_two h) (fun h ↦ not_isObt_of_eq_pi_div_two h)

theorem isRight_of_isAcu {θ : AngValue} (h : θ.IsAcu) : ¬ θ.IsRight :=
  fun hr ↦ (not_isAcu_of_not_isRight hr) h

theorem isRight_of_isNeg {θ : AngValue} (h : θ.IsObt) : ¬ θ.IsRight :=
  fun hr ↦ (not_isObt_of_not_isRight hr) h

theorem isAcu_or_isNeg_of_isRight {θ : AngValue} (h : ¬ θ.IsRight) : θ.IsAcu ∨ θ.IsObt := by
  contrapose! h
  have h := (and_congr btw_iff_not_sbtw btw_iff_not_sbtw).mpr h.symm
  rcases btw_antisymm (btw_cyclic_right h.1) (btw_cyclic_left h.2) with h | h
  · exact (pi_div_two_ne_neg_pi_div_two h).elim
  · exact (or_congr_left eq_comm).mp h

theorem not_isRight_or_isAcu_or_isNeg {θ : AngValue} : θ.IsRight ∨ θ.IsAcu ∨ θ.IsObt :=
  if h : θ.IsRight then .inl h else .inr (isAcu_or_isNeg_of_isRight h)

theorem isRight_or_isObt_of_not_isAcu {θ : AngValue} (h : ¬ θ.IsAcu) : θ.IsRight ∨ θ.IsObt :=
  Or.casesOn not_isRight_or_isAcu_or_isNeg (fun h ↦ .inl h) fun hn ↦
    Or.casesOn hn (fun hp ↦ (h hp).elim) (fun h ↦ .inr h)

theorem isRight_or_isAcu_of_not_isObt {θ : AngValue} (h : ¬ θ.IsObt) : θ.IsRight ∨ θ.IsAcu :=
  Or.casesOn not_isRight_or_isAcu_or_isNeg (fun h ↦ .inl h) fun hn ↦
    Or.casesOn hn (fun h ↦ .inr h) (fun hp ↦ (h hp).elim)

end trichotomy

section toReal

theorem isAcu_iff {θ : AngValue} : θ.IsAcu ↔ - π / 2 < θ.toReal ∧ θ.toReal < π / 2 := sorry

theorem isObt_iff {θ : AngValue} : θ.IsObt ↔  θ.toReal < - π / 2 ∨ π / 2 < θ.toReal := sorry

theorem isRight_iff' {θ : AngValue} : θ.IsRight ↔ θ.toReal = - π / 2 ∨ θ.toReal = π / 2 := sorry

theorem not_isRight_iff' {θ : AngValue} : ¬ θ.IsRight ↔ θ.toReal ≠ - π / 2 ∧ θ.toReal ≠ π / 2 := sorry

end toReal

section cos

theorem zero_lt_cos_iff_isAcu {θ : AngValue} : θ.IsAcu ↔ 0 < cos θ := sorry

theorem zero_lt_cos_iff_isObt {θ : AngValue} : θ.IsObt ↔ sin θ < 0 := sorry

theorem isRight_iff_sin_eq_zero {θ : AngValue} : θ.IsRight ↔ cos θ = 0 := sorry

theorem not_isRight_iff_cos_ne_zero {θ : AngValue} : ¬ θ.IsRight ↔ cos θ ≠ 0 := sorry

end cos

section neg

@[simp]
theorem neg_isAcu_iff_isAcu {θ : AngValue} : (-θ).IsAcu ↔ θ.IsAcu := sorry

@[simp]
theorem neg_isObt_iff_isObt {θ : AngValue} : (-θ).IsObt ↔ θ.IsObt := sorry

@[simp]
theorem neg_isRight_iff_isRight {θ : AngValue} : (-θ).IsRight ↔ θ.IsRight := sorry

end neg

end acute_obtuse_right

end AngValue

-- `a section discussing cos sin, uniqueness with pos neg`
-- `sin >0 implies angle IsPos, cos >0 implies ..., sin = 0 implies ...`
-- `acute, ... also implies uniqueness`
-- sin cos of special values is already at simp


section trigonometric

theorem pos_angle_eq_angle_iff_cos_eq_cos (ang₁ ang₂ : AngValue) (hang₁ : ang₁.IsPos) (hang₂ : ang₂.IsPos) : cos ang₁ = cos ang₂ ↔ ang₁ = ang₂ := by
  rw [cos_eq_iff_eq_or_eq_neg]
  constructor
  intro e
  rcases e with e₁ | e₂
  · exact e₁
  · exfalso
    exact AngValue.not_isNeg_of_isPos hang₁ (e₂ ▸ AngValue.neg_isNeg_iff_isPos.mpr hang₂)
  exact .inl

theorem neg_angle_eq_angle_iff_cos_eq_cos (ang₁ ang₂ : AngValue) (hang₁ : ang₁.IsNeg) (hang₂ : ang₂.IsNeg) : cos ang₁ = cos ang₂ ↔ ang₁ = ang₂ := by
  rw [cos_eq_iff_eq_or_eq_neg]
  constructor
  intro e
  rcases e with e₁ | e₂
  · exact e₁
  · exfalso
    exact AngValue.not_isPos_of_isNeg hang₁ (e₂ ▸ AngValue.neg_isPos_iff_isNeg.mpr hang₂)
  exact .inl

/-
Move the sum and difference formulas, product-to-sum formulas, and sum-to-product formulas of trigonometric functions of `Real.sin` here and translate it to `AngValue.sin`. For example,

theorem Real.sin_sub (x : ℝ) (y : ℝ) :
Real.sin (x - y) = Real.sin x * Real.cos y - Real.cos x * Real.sin y

theorem Real.cos_sub (x : ℝ) (y : ℝ) :
Real.cos (x - y) = Real.cos x * Real.cos y + Real.sin x * Real.sin y

theorem Real.sin_sub_sin (x : ℝ) (y : ℝ) :
Real.sin x - Real.sin y = 2 * Real.sin ((x - y) / 2) * Real.cos ((x + y) / 2)

theorem Real.cos_sub_cos (x : ℝ) (y : ℝ) :
Real.cos x - Real.cos y = -2 * Real.sin ((x + y) / 2) * Real.sin ((x - y) / 2)

theorem Real.cos_add_cos (x : ℝ) (y : ℝ) :
Real.cos x + Real.cos y = 2 * Real.cos ((x + y) / 2) * Real.cos ((x - y) / 2)

theorem Real.tan_mul_cos {x : ℝ} (hx : Real.cos x ≠ 0) :
Real.tan x * Real.cos x = Real.sin x
-/
-- This is needed. Since this work should be done in Mathlib, `This work should be moved to file FromMathlib. Add a section called Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` since these formulas should belong to this file or subfile of folder of same name.
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
--`theorem of the form (x y : AngValue) : 2 • x = 2 • y ↔ (x : AngDValue) = y`

end angvalue_angdvalue_compatibility

section real_angdvalue_compatibility
-- `see section real_angvalue_compatibility, but we do not allow a function from AngDValue to Real`
end real_angdvalue_compatibility

/-
-- A diagram commute is needed, add this to norm_cast
theorem (θ : AngValue) (d : Dir) : ((θ +ᵥ d) : Proj) = (θ : AngDValue) +ᵥ (d : Proj)
-/

end angdvalue



namespace AngValue

section half

def half (θ : AngValue) : AngValue := ∠[θ.toReal / 2]

theorem coe_half {x : ℝ} (hn : - π < x) (h : x ≤ π) : ∠[x].half = ∠[x / 2] :=
  congrArg AngValue.coe (congrFun (congrArg HDiv.hDiv (toReal_coe_eq_self hn h)) 2)

theorem smul_two_half {θ : AngValue} : 2 • θ.half = θ := θ.two_nsmul_toReal_div_two

theorem sub_half_eq_half {θ : AngValue} : θ - θ.half = θ.half :=
  sub_eq_of_eq_add (smul_two_half.symm.trans (two_nsmul θ.half))

theorem half_toReal {θ : AngValue} : θ.half.toReal = θ.toReal / 2 := by
  simp only [half, toReal_coe, toIocMod_eq_self, gt_iff_lt, lt_add_iff_pos_right, zero_lt_two,
    zero_lt_mul_left, not_lt, ge_iff_le, add_le_iff_nonpos_right, Set.mem_Ioc, le_neg_add_iff_add_le]
  constructor <;>
  linarith [θ.neg_pi_lt_toReal, θ.toReal_le_pi]

theorem half_toReal_le_two_inv_mul_pi {θ : AngValue} : θ.half.toReal ≤ π / 2 := by
  rw [θ.half_toReal]
  exact (div_le_div_right (by norm_num)).mpr θ.toReal_le_pi

theorem neg_two_inv_mul_pi_lt_half_toReal {θ : AngValue} : -π/2 < θ.half.toReal := by
  rw [θ.half_toReal]
  exact (div_lt_div_right (by norm_num)).mpr θ.neg_pi_lt_toReal

theorem half_toReal_lt_pi {θ : AngValue} : θ.half.toReal < π :=
  (θ.half_toReal_le_two_inv_mul_pi).trans_lt (by field_simp [Real.pi_pos])

theorem eq_two_mul_coe_of_half_toReal_eq {θ : AngValue} {x : ℝ} (h : θ.half.toReal = x) : θ = ∠[2 * x] := by
  rw [← h, half_toReal, mul_div_cancel' θ.toReal two_ne_zero, θ.coe_toReal]

theorem half_inj {α β : AngValue} (h : α.half = β.half) : α = β :=
  toReal_inj.mp ((div_left_inj' (by norm_num)).mp <|
    ((α.half_toReal).symm.trans (congrArg toReal h)).trans β.half_toReal)

@[simp]
theorem half_congr {α β : AngValue} : α.half = β.half ↔ α = β := ⟨half_inj, congrArg half⟩

theorem half_neg_of_ne_pi {θ : AngValue} (h : θ ≠ π) : (- θ).half = - θ.half := by
  rw [half, half, neg_toReal h, ← coe_neg]
  field_simp

theorem half_neg_of_isND {θ : AngValue} (h : θ.IsND) : (- θ).half = - θ.half := half_neg_of_ne_pi h.2

section special_value

theorem zero_half : (0 : AngValue).half = 0 := by
  rw [half, toReal_zero, zero_div, coe_zero]

theorem eq_zero_of_half_eq_zero {θ : AngValue} (h : θ.half = 0) : θ = 0 := half_inj (h.trans zero_half.symm)

theorem half_eq_zero_iff_eq_zero {θ : AngValue} : θ.half = 0 ↔ θ = 0 :=
  ⟨eq_zero_of_half_eq_zero, fun h ↦ (half_congr.mpr h).trans zero_half⟩

theorem pi_half : ∠[π].half = ∠[π / 2] := coe_half (by norm_num [Real.pi_pos]) (Eq.ge rfl)

theorem eq_pi_of_half_eq_pi {θ : AngValue} (h : θ.half = ∠[π / 2]) : θ = π :=
  half_inj (h.trans pi_half.symm)

theorem half_eq_pi_iff_eq_pi {θ : AngValue} : θ.half = ∠[π / 2] ↔ θ = π :=
  ⟨eq_pi_of_half_eq_pi, fun h ↦ (half_congr.mpr h).trans pi_half⟩

end special_value

section pos_neg

theorem half_isPos_of_isPos {θ : AngValue} (h : θ.IsPos) : θ.half.IsPos := by
  refine' isPos_iff.mpr ⟨_, θ.half_toReal_lt_pi⟩
  rw [half_toReal]
  linarith [zero_lt_toReal_of_isPos h]

theorem half_isNeg_iff_isNeg {θ : AngValue} : θ.half.IsNeg ↔ θ.IsNeg := by
  refine' isNeg_iff.trans (Iff.trans _ isNeg_iff.symm)
  nth_rw 1 [half_toReal, ← zero_div (2 : ℝ), div_lt_div_right (by norm_num)]

end pos_neg

section acute_obtuse

theorem half_isAcu_of_ne_pi {θ : AngValue} (h : θ ≠ π) : θ.half.IsAcu := sorry

theorem half_not_isAcu {θ : AngValue} : ¬ θ.half.IsObt := sorry

end acute_obtuse

end half



section abs
/-
-- Is this definition useful?
instance AngValue.instAbs : Abs AngValue where
  abs θ := ∠[|θ.toReal|]
variable (θ : AngValue)
#check |θ|
-- `We shall wait and see what congruence will become`
-/

def abs (θ : AngValue) : ℝ := |θ.toReal|

theorem zero_le_abs {θ : AngValue} : 0 ≤ θ.abs := abs_nonneg θ.toReal

theorem abs_le_pi {θ : AngValue} : θ.abs ≤ π := abs_toReal_le_pi θ

theorem neg_pi_lt_abs {θ : AngValue} : - π < θ.abs :=
  LT.lt.trans_le (by norm_num [Real.pi_pos]) θ.zero_le_abs

theorem coe_abs_eq_abs {x : ℝ} (hn : - π < x) (h : x ≤ π) : ∠[x].abs = |x| :=
  congrArg Abs.abs (toReal_coe_eq_self hn h)

theorem coe_abs_eq_abs_of_abs_le_pi {x : ℝ} (h : |x| ≤ π) : ∠[x].abs = |x| :=
  if hp : x = - π then by
    rw [hp, abs_neg, coe_neg, AngValue.neg_coe_pi]
    exact coe_abs_eq_abs (by norm_num [Real.pi_pos]) (Eq.ge rfl)
  else coe_abs_eq_abs (Ne.lt_of_le' hp (neg_le_of_abs_le h)) (le_of_abs_le h)

theorem coe_abs_le_abs (x : ℝ) : ∠[x].abs ≤ |x| :=
  if h : |x| ≤ π then (coe_abs_eq_abs_of_abs_le_pi h).le
  else (∠[x].abs_le_pi).trans (le_of_not_le h)

theorem abs_min {θ : AngValue} {x : ℝ} (h : θ = ∠[x]) : θ.abs ≤ |x| := by
  rw [h]
  exact coe_abs_le_abs x

theorem eq_coe_or_neg_coe_of_abs_eq {θ : AngValue} {x : ℝ} (h : θ.abs = x) : θ = ∠[x] ∨ θ = - ∠[x] := by
  rcases eq_or_eq_neg_of_abs_eq h with h | h
  · rw [← h]
    exact .inl θ.coe_toReal.symm
  · rw [← coe_neg, ← h]
    exact .inr θ.coe_toReal.symm

theorem abs_eq_toReal_or_neg_toeal {θ : AngValue} : θ.abs = θ.toReal ∨ θ.abs = - θ.toReal :=
  abs_choice θ.toReal

theorem abs_coe_eq_self_or_neg {θ : AngValue} : ∠[θ.abs] = θ ∨ ∠[θ.abs] = - θ := by
  rcases θ.abs_eq_toReal_or_neg_toeal with h | h
  · rw [h]
    exact .inl θ.coe_toReal
  · rw [h, coe_neg]
    exact .inr (neg_inj.mpr θ.coe_toReal)

section special_value

theorem zero_abs : (0 : AngValue).abs = 0 := by
  rw [abs, toReal_zero, abs_zero]

theorem abs_eq_zero_iff_eq_zero {θ : AngValue} : θ.abs = 0 ↔ θ = 0 :=
  abs_eq_zero.trans toReal_eq_zero_iff

theorem abs_ne_zero_iff_ne_zero {θ : AngValue} : θ.abs ≠ 0 ↔ θ ≠ 0 := abs_eq_zero_iff_eq_zero.not

theorem zero_lt_abs_iff_ne_zero {θ : AngValue} : 0 < θ.abs ↔ θ ≠ 0 :=
  ((θ.zero_le_abs).gt_iff_ne).trans abs_ne_zero_iff_ne_zero

theorem pi_abs : (π : AngValue).abs = π := by
  rw [abs, toReal_pi, abs_eq_self.mpr (le_of_lt Real.pi_pos)]

theorem eq_pi_of_abs_eq_pi {θ : AngValue} (h : θ.abs = π) : θ = π :=
  toReal_eq_pi_iff.mp ((or_iff_left (ne_of_gt θ.neg_pi_lt_toReal)).mp (eq_or_eq_neg_of_abs_eq h))

theorem abs_eq_pi_iff_eq_pi {θ : AngValue} : θ.abs = π ↔ θ = π :=
  ⟨eq_pi_of_abs_eq_pi, fun h ↦ (congrArg abs h).trans pi_abs⟩

theorem abs_ne_pi_iff_ne_pi {θ : AngValue} : θ.abs ≠ π ↔ θ ≠ π := abs_eq_pi_iff_eq_pi.not

theorem abs_lt_pi_iff_ne_pi {θ : AngValue} : θ.abs < π ↔ θ ≠ π :=
  ((θ.abs_le_pi).lt_iff_ne).trans abs_ne_pi_iff_ne_pi

theorem pi_div_two_abs : ∠[π / 2].abs = π / 2 := by
  rw [abs, toReal_pi_div_two, abs_eq_self.mpr (div_nonneg (le_of_lt Real.pi_pos) zero_le_two)]

theorem neg_pi_div_two_abs : ∠[- π / 2].abs = π / 2 := by
  rw [abs, toReal_neg_pi_div_two, ← neg_neg (π / 2), neg_div 2 π]
  norm_num [div_nonneg (le_of_lt Real.pi_pos) zero_le_two]

end special_value

section pos_neg_nd

theorem zero_lt_abs_lt_pi_iff_isND {θ : AngValue} : 0 < θ.abs ∧ θ.abs < π ↔ θ.IsND :=
  ((θ.zero_lt_abs_iff_ne_zero).and θ.abs_lt_pi_iff_ne_pi).trans (θ.isND_iff).symm

theorem abs_coe_not_isNeg {θ : AngValue} : ¬ ∠[θ.abs].IsNeg :=
  coe_not_isNeg_of_zero_le_self_le_pi zero_le_abs abs_le_pi

theorem abs_coe_isPos_iff_isND {θ : AngValue} : ∠[θ.abs].IsPos ↔ θ.IsND := by
  rw [isPos_iff, toReal_coe_eq_self neg_pi_lt_abs abs_le_pi, zero_lt_abs_lt_pi_iff_isND]

theorem abs_coe_isPos_of_isPos {θ : AngValue} (h : θ.IsPos) : ∠[θ.abs].IsPos :=
  abs_coe_isPos_iff_isND.mpr (isND_of_isPos h)

theorem abs_eq_toReal_of_not_isNeg {θ : AngValue} (h : ¬ θ.IsNeg) : θ.abs = θ.toReal :=
  abs_eq_self.mpr (not_isNeg_iff.mp h)

theorem abs_coe_eq_self_of_not_isNeg {θ : AngValue} (h : ¬ θ.IsNeg) : ∠[θ.abs] = θ := by
  rw [abs_eq_toReal_of_not_isNeg h, coe_toReal]

theorem abs_eq_toReal_of_isPos {θ : AngValue} (h : θ.IsPos) : θ.abs = θ.toReal :=
  abs_eq_toReal_of_not_isNeg (not_isNeg_of_isPos h)

theorem abs_coe_eq_self_of_isPos {θ : AngValue} (h : θ.IsPos) : ∠[θ.abs] = θ :=
  abs_coe_eq_self_of_not_isNeg (not_isNeg_of_isPos h)

theorem abs_eq_toReal_of_isND {θ : AngValue} (h : ¬ θ.IsND) : θ.abs = θ.toReal :=
  abs_eq_toReal_of_not_isNeg (not_isNeg_of_not_isND h)

theorem abs_coe_eq_self_of_isND {θ : AngValue} (h : ¬ θ.IsND) : ∠[θ.abs] = θ :=
  abs_coe_eq_self_of_not_isNeg (not_isNeg_of_not_isND h)

theorem abs_eq_neg_toReal_of_isNeg {θ : AngValue} (h : θ.IsNeg) : θ.abs = - θ.toReal :=
  abs_of_neg (isNeg_iff.mp h)

theorem abs_coe_eq_neg_of_isNeg {θ : AngValue} (h : θ.IsNeg) : ∠[θ.abs] = - θ := by
  rw [abs_eq_neg_toReal_of_isNeg h, coe_neg, coe_toReal]

theorem not_isNeg_of_abs_eq_toReal {θ : AngValue} (h : θ.abs = θ.toReal) : ¬ θ.IsNeg :=
  not_isNeg_iff.mpr (abs_eq_self.mp h)

theorem not_isNeg_of_abs_coe_eq_self {θ : AngValue} (h : ∠[θ.abs] = θ) : ¬ θ.IsNeg := by
  apply not_isNeg_of_abs_eq_toReal
  rw [← toReal_coe_eq_self neg_pi_lt_abs abs_le_pi, h]

theorem abs_eq_toReal_iff {θ : AngValue} : θ.abs = θ.toReal ↔ ¬ θ.IsNeg :=
  ⟨not_isNeg_of_abs_eq_toReal, abs_eq_toReal_of_not_isNeg⟩

theorem abs_ne_toReal_iff {θ : AngValue} : θ.abs ≠ θ.toReal ↔ θ.IsNeg :=
  (θ.abs_eq_toReal_iff).not.trans not_not

theorem abs_coe_eq_neg_iff_isNeg {θ : AngValue} : ∠[θ.abs] = θ ↔ ¬ θ.IsNeg :=
  ⟨not_isNeg_of_abs_coe_eq_self, abs_coe_eq_self_of_not_isNeg⟩

theorem abs_coe_ne_neg_iff_not_isNeg {θ : AngValue} : ∠[θ.abs] ≠ θ ↔ θ.IsNeg :=
  abs_coe_eq_neg_iff_isNeg.not.trans not_not

end pos_neg_nd

/- section acute_obtuse

end acute_obtuse -/

theorem abs_eq_iff {α β : AngValue} : α.abs = β.abs ↔ α = β ∨ α = - β :=
  if h : β = π then by
    rw [h, pi_abs]
    exact abs_eq_pi_iff_eq_pi.trans (or_iff_left_of_imp (fun h ↦ h.trans neg_coe_pi)).symm
  else abs_eq_abs.trans (or_congr toReal_inj ((neg_toReal h).congr_right.symm.trans toReal_inj))

theorem abs_congr {α β : AngValue} (h : α = β) : α.abs = β.abs := abs_eq_iff.mpr (.inl h)

theorem abs_neg {θ : AngValue} : (- θ).abs = θ.abs := abs_eq_iff.mpr (.inr (Eq.refl (- θ)))

theorem abs_add_le {α β : AngValue} : (α + β).abs ≤ α.abs + β.abs :=
  (abs_min (by simp only [coe_add, coe_toReal])).trans (abs_add α.toReal β.toReal)

end abs

end AngValue

end EuclidGeom
