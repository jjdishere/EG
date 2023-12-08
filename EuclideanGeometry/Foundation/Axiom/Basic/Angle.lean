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
noncomputable section

namespace EuclidGeom

open Real

def AngDValue := AddCircle π

namespace AngDValue

instance : NormedAddCommGroup AngDValue :=
  inferInstanceAs (NormedAddCommGroup (AddCircle π))

instance : Inhabited AngDValue :=
  inferInstanceAs (Inhabited (AddCircle π))

@[coe]
def _root_.AngValue.toAngDValue' : AngValue → AngDValue :=
  Quotient.map' id (by
    rintro _ _ ⟨⟨v, ⟨k, hv⟩⟩, h⟩
    exact ⟨⟨v, ⟨k * 2, by simpa [mul_assoc] using hv⟩⟩, h⟩)

instance : Coe AngValue AngDValue where
  coe := AngValue.toAngDValue'

def _root_.AngValue.toAngDValue : AngValue →+ AngDValue where
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

end EuclidGeom
