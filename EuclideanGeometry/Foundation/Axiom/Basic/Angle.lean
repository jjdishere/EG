import EuclideanGeometry.Foundation.Axiom.Basic.Vector
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
open Real.Angle

noncomputable section
namespace EuclidGeom

section angvalue
-- `using abbrev inherits instances and simp`
def AngValue := Real.Angle

instance : NormedAddCommGroup AngValue := inferInstanceAs (NormedAddCommGroup Real.Angle)

instance : CircularOrder AngValue := inferInstanceAs (CircularOrder Real.Angle)

end angvalue
end EuclidGeom

@[coe]
def Real.toAngValue : ℝ → EuclidGeom.AngValue := Real.Angle.coe

namespace EuclidGeom
section angvalue

instance : Coe Real AngValue where
  coe := Real.toAngValue

@[pp_dot]
def AngValue.toReal : AngValue → ℝ := Real.Angle.toReal

instance : Coe AngValue ℝ where
  coe := AngValue.toReal

section real_angvalue_compatibility
-- this section is partially intended to be not so complete, we disencouage using real to denote the angle. for more involved use of real angvalue compatibility, please use theorems in Real.AddCircle.

theorem AngValue.toreal_le_pi {θ : AngValue} : θ.toReal ≤ π := toReal_le_pi θ

theorem AngValue.neg_pi_lt_toreal {θ : AngValue} : -π < θ.toReal := neg_pi_lt_toReal θ

theorem AngValue.neg_pi_lt_toreal_le_pi {θ : AngValue} : -π < θ.toReal ∧ θ.toReal ≤ π :=
  ⟨θ.neg_pi_lt_toreal, θ.toreal_le_pi⟩

theorem AngValue.abs_toreal_le_pi {θ : AngValue} : |θ.toReal| ≤ π := abs_toReal_le_pi θ

section composite

@[simp]
theorem AngValue.toreal_toangvalue_eq_self {θ : AngValue} : (θ.toReal).toAngValue = θ := coe_toReal θ

@[simp]
theorem toangvalue_toreal_eq_self_of_neg_pi_lt_le_pi {r : ℝ} (h₁ : -π < r) (h₂ : r ≤ π) : r.toAngValue.toReal = r :=
  toReal_coe_eq_self_iff.mpr ⟨h₁, h₂⟩

theorem toAngValue_eq_iff {r s : ℝ} : r.toAngValue = s.toAngValue ↔ ∃ k : ℤ, r - s = k * (2 * π) :=
  QuotientAddGroup.eq_iff_sub_mem.trans <| AddSubgroup.mem_zmultiples_iff.trans <|
    exists_congr (fun k ↦ eq_comm.trans (zsmul_eq_mul (2 * π) k).congr_right)

theorem toangvalue_toreal_eq_self_add_two_mul_int_mul_pi (r : ℝ) : ∃ k : ℤ, r.toAngValue.toReal = r + k * (2 * π) := by
  rcases toAngValue_eq_iff.mp r.toAngValue.toreal_toangvalue_eq_self with ⟨k, h⟩
  exact ⟨k, eq_add_of_sub_eq' h⟩

theorem toangvalue_eq_of_add_two_mul_int_mul_pi {r₁ r₂ : ℝ} (k : ℤ) (h : r₁ = r₂ + k * (2 * π)) : r₁.toAngValue = r₂.toAngValue :=
  toAngValue_eq_iff.mpr ⟨k, sub_eq_of_eq_add' h⟩

@[simp]
theorem add_two_pi (x : ℝ) : (x + 2 * π : ℝ).toAngValue = x.toAngValue :=
  toangvalue_eq_of_add_two_mul_int_mul_pi 1 (by rw [Int.cast_one, one_mul])

@[simp]
theorem sub_two_pi (x : ℝ) : (x - 2 * π : ℝ).toAngValue = x.toAngValue := by
  refine' toangvalue_eq_of_add_two_mul_int_mul_pi (- 1) _
  rw [Int.cast_neg, Int.cast_one, neg_mul, one_mul]
  rfl

theorem AngValue.toreal_inj {α β : AngValue} (h : α.toReal = β.toReal) : α = β := toReal_inj.mp h

@[simp]
theorem AngValue.toreal_congr {α β : AngValue} : α.toReal = β.toReal ↔ α = β := toReal_inj

end composite

namespace AngValue

section special_value

--special values -pi 0 pi 2pi -2pi `To be added`
@[simp]
theorem coe_zero : ((0 : ℝ) : AngValue) = (0 : AngValue) := rfl

@[simp]
theorem toreal_eq_zero_iff {θ : AngValue} : θ.toReal = 0 ↔ θ = 0 := toReal_eq_zero_iff

theorem eq_zero_of_toreal_eq_zero {θ : AngValue} (h : θ.toReal = 0) : θ = 0 := toReal_eq_zero_iff.mp h

theorem toreal_eq_zero_of_eq_zero {θ : AngValue} (h : θ = 0) : θ.toReal = 0 := toReal_eq_zero_iff.mpr h

theorem ne_zero_of_toreal_ne_zero {θ : AngValue} (h : θ.toReal ≠ 0) : θ ≠ 0 :=
  fun hs ↦ h (toreal_eq_zero_of_eq_zero hs)

theorem toreal_ne_zero_of_ne_zero {θ : AngValue} (h : θ ≠ 0) : θ.toReal ≠ 0 :=
  fun hs ↦ h (eq_zero_of_toreal_eq_zero hs)

@[simp]
theorem toreal_pi : (π : AngValue).toReal = π := toReal_pi

@[simp]
theorem toreal_eq_pi_iff {θ : AngValue} : θ.toReal = π ↔ θ = π := toReal_eq_pi_iff

theorem eq_pi_of_toreal_eq_pi {θ : AngValue} (h : θ.toReal = π) : θ = π := toReal_eq_pi_iff.mp h

theorem toreal_eq_pi_of_eq_pi {θ : AngValue} (h : θ = π) : θ.toReal = π := toReal_eq_pi_iff.mpr h

theorem ne_pi_of_toreal_ne_pi {θ : AngValue} (h : θ.toReal ≠ π) : θ ≠ π :=
  fun hs ↦ h (toreal_eq_pi_of_eq_pi hs)

theorem toreal_ne_pi_of_ne_pi {θ : AngValue} (h : θ ≠ π) : θ.toReal ≠ π :=
  fun hs ↦ h (eq_pi_of_toreal_eq_pi hs)

theorem pi_ne_zero : (π : AngValue) ≠ 0 := Real.Angle.pi_ne_zero

@[simp]
theorem toreal_pi_div_two : ((π / 2 : ℝ) : AngValue).toReal = π / 2 := toReal_pi_div_two

@[simp]
theorem toreal_eq_pi_div_two_iff {θ : AngValue} : θ.toReal = π / 2 ↔ θ = (π / 2 : ℝ) :=
  toReal_eq_pi_div_two_iff

@[simp]
theorem toreal_neg_pi_div_two : ((-π / 2 : ℝ) : AngValue).toReal = -π / 2 := toReal_neg_pi_div_two

@[simp]
theorem toreal_eq_neg_pi_div_two_iff {θ : AngValue} : θ.toReal = -π / 2 ↔ θ = (-π / 2 : ℝ) :=
  toReal_eq_neg_pi_div_two_iff

theorem pi_div_two_ne_zero : ((π / 2 : ℝ) : AngValue) ≠ 0 := Real.Angle.pi_div_two_ne_zero

theorem neg_pi_div_two_ne_zero : ((-π / 2 : ℝ) : AngValue) ≠ 0 := Real.Angle.neg_pi_div_two_ne_zero

@[simp]
theorem coe_two_pi : ((2 * π : ℝ) : AngValue) = (0 : AngValue) := Real.Angle.coe_two_pi

@[simp]
theorem neg_coe_pi : (- π : AngValue) = (π : AngValue) := Real.Angle.neg_coe_pi

theorem sub_coe_pi_eq_add_coe_pi {θ : AngValue} : θ - π = θ + π := Real.Angle.sub_coe_pi_eq_add_coe_pi θ

theorem eq_or_eq_add_pi_of_two_zsmul_eq {ψ θ : AngValue} (h : (2 : ℤ) • ψ = (2 : ℤ) • θ) : ψ = θ ∨ ψ = θ + ↑π :=
  two_zsmul_eq_iff.mp h

theorem eq_or_eq_add_pi_of_two_nsmul_eq {ψ θ : AngValue} (h : (2 : ℕ) • ψ = (2 : ℕ) • θ) : ψ = θ ∨ ψ = θ + ↑π :=
  two_nsmul_eq_iff.mp h

theorem eq_zero_or_eq_pi_of_two_nsmul_eq_zero {θ : AngValue} (h : (2 : ℕ) • θ = 0) : θ = 0 ∨ θ = π :=
  two_nsmul_eq_zero_iff.mp h

theorem ne_zero_of_two_nsmul_ne_zero {θ : AngValue} (h : (2 : ℕ) • θ ≠ 0) : θ ≠ 0 :=
  (two_nsmul_ne_zero_iff.mp h).1

theorem ne_pi_of_two_nsmul_ne_zero {θ : AngValue} (h : (2 : ℕ) • θ ≠ 0) : θ ≠ π :=
  (two_nsmul_ne_zero_iff.mp h).2

theorem eq_zero_or_eq_pi_of_two_zsmul_eq_zero {θ : AngValue} (h : (2 : ℤ) • θ = 0) : θ = 0 ∨ θ = π :=
  two_zsmul_eq_zero_iff.mp h

theorem ne_zero_of_two_zsmul_ne_zero {θ : AngValue} (h : (2 : ℤ) • θ ≠ 0) : θ ≠ 0 :=
  (two_zsmul_ne_zero_iff.mp h).1

theorem ne_pi_of_two_zsmul_ne_zero {θ : AngValue} (h : (2 : ℤ) • θ ≠ 0) : θ ≠ π :=
  (two_zsmul_ne_zero_iff.mp h).2

theorem eq_zero_or_eq_pi_of_eq_neg {θ : AngValue} (h : θ = - θ) : θ = 0 ∨ θ = π := eq_neg_self_iff.mp h

theorem ne_zero_of_ne_neg {θ : AngValue} (h : θ ≠ - θ) : θ ≠ 0 := (ne_neg_self_iff.mp h).1

theorem ne_pi_of_ne_neg {θ : AngValue} (h : θ ≠ - θ) : θ ≠ π := (ne_neg_self_iff.mp h).2

theorem two_nsmul_eq_pi {θ : AngValue} (h : (2 : ℕ) • θ = π) : θ = (π / 2 : ℝ) ∨ θ = (- π / 2 : ℝ) :=
  two_nsmul_eq_pi_iff.mp h

theorem two_zsmul_eq_pi {θ : AngValue} (h : (2 : ℤ) • θ = π) : θ = (π / 2 : ℝ) ∨ θ = (- π / 2 : ℝ) :=
  two_zsmul_eq_pi_iff.mp h

end special_value

section group_hom
-- `the current direction of simp is turn every thing into Real, is this good?` ` Maybe all reversed is better`
@[simp low]
theorem add_coe (x y: ℝ) : (x : AngValue) + (y : AngValue) = (((x + y) : ℝ) : AngValue) := rfl

@[simp low]
theorem neg_coe (x : ℝ): -(x : AngValue) = (((-x) : ℝ) : AngValue) := rfl

@[simp low]
theorem sub_coe (x y: ℝ) : (x : AngValue) - (y : AngValue) = (((x - y) : ℝ) : AngValue)  := rfl

@[simp low]
theorem nsmul_coe (n : ℕ) (x : ℝ) : n • (x : AngValue) = ((n * x: ℝ) : AngValue) := (nsmul_eq_mul _ x) ▸ Eq.refl _

@[simp low]
theorem zsmul_coe (n : ℤ) (x : ℝ) : n • (x : AngValue) = ((n * x : ℝ) : AngValue) := (zsmul_eq_mul x _) ▸ Eq.refl _

@[simp low]
theorem two_nsmul_coe_div_two (x : ℝ) : 2 • (↑(x / 2) : AngValue) = x.toAngValue :=
  Real.Angle.two_nsmul_coe_div_two x

@[simp low]
theorem two_nsmul_toreal_div_two {θ : AngValue} : 2 • (θ.toReal / 2).toAngValue = θ := by
  nth_rw 2 [← θ.toreal_toangvalue_eq_self]
  exact two_nsmul_coe_div_two θ.toReal

@[simp low]
theorem two_zsmul_coe_div_two (x : ℝ) : (2 : ℤ) • (↑(x / 2) : AngValue) = x.toAngValue :=
  two_nsmul_coe_div_two x

@[simp low]
theorem two_zsmul_toreal_div_two {θ : AngValue} : (2 : ℤ) • (θ.toReal / 2).toAngValue = θ :=
  θ.two_nsmul_toreal_div_two

end group_hom

end AngValue

end real_angvalue_compatibility

open Classical

section pos_neg_isnd

namespace AngValue

@[pp_dot]
def IsPos (θ : AngValue) : Prop := sbtw 0 θ π

@[pp_dot]
def IsNeg (θ : AngValue) : Prop := sbtw (π: AngValue) θ 0

@[pp_dot]
structure IsND (θ : AngValue) : Prop where intro ::
  ne_zero : θ ≠ 0
  ne_pi : θ ≠ π

section special_value

theorem zero_not_ispos : ¬ (0 : AngValue).IsPos := sbtw_irrefl_left

theorem zero_not_isneg : ¬ (0 : AngValue).IsNeg := sbtw_irrefl_right

theorem zero_not_isnd : ¬ (0 : AngValue).IsND := fun nd ↦ nd.1 rfl

theorem not_ispos_of_eq_zero {θ : AngValue} (h : θ = 0) : ¬ θ.IsPos := by
  rw [h]
  exact zero_not_ispos

theorem ne_zero_of_ispos {θ : AngValue} (h : θ.IsPos) : θ ≠ 0 := fun hs ↦ not_ispos_of_eq_zero hs h

theorem not_isneg_of_eq_zero {θ : AngValue} (h : θ = 0) : ¬ θ.IsNeg :=  by
  rw [h]
  exact zero_not_isneg

theorem ne_zero_of_isneg {θ : AngValue} (h : θ.IsNeg) : θ ≠ 0 := fun hs ↦ not_isneg_of_eq_zero hs h

theorem not_isnd_of_eq_zero {θ : AngValue} (h : θ = 0) : ¬ θ.IsND := fun nd ↦ nd.1 h

theorem pi_not_ispos : ¬ (π : AngValue).IsPos := sbtw_irrefl_right

theorem pi_not_isneg : ¬ (π : AngValue).IsNeg := sbtw_irrefl_left

theorem pi_not_isnd : ¬ (π : AngValue).IsND := fun nd ↦ nd.2 rfl

theorem not_ispos_of_eq_pi {θ : AngValue} (h : θ = π) : ¬ θ.IsPos :=  by
  rw [h]
  exact pi_not_ispos

theorem ne_pi_of_ispos {θ : AngValue} (h : θ.IsPos) : θ ≠ π := fun hs ↦ not_ispos_of_eq_pi hs h

theorem not_isneg_of_eq_pi {θ : AngValue} (h : θ = π) : ¬ θ.IsNeg :=  by
  rw [h]
  exact pi_not_isneg

theorem ne_pi_of_isneg {θ : AngValue} (h : θ.IsNeg) : θ ≠ π := fun hs ↦ not_isneg_of_eq_pi hs h

theorem not_isnd_of_eq_pi {θ : AngValue} (h : θ = π) : ¬ θ.IsND := fun nd ↦ nd.2 h

theorem isnd_iff {θ : AngValue} : θ.IsND ↔ θ ≠ 0 ∧ θ ≠ π :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

theorem not_isnd_iff {θ : AngValue} : ¬ θ.IsND ↔ (θ = 0 ∨ θ = π) :=
  (not_iff_not.mpr θ.isnd_iff).trans or_iff_not_and_not.symm

end special_value

section trichotomy

theorem not_isneg_of_ispos {θ : AngValue} (h : θ.IsPos) : ¬ θ.IsNeg := sbtw_asymm h

theorem isnd_of_ispos {θ : AngValue} (h : θ.IsPos) : θ.IsND where
  ne_zero hs := not_ispos_of_eq_zero hs h
  ne_pi hs := not_ispos_of_eq_pi hs h

theorem not_ispos_of_isneg {θ : AngValue} (h : θ.IsNeg) : ¬ θ.IsPos := sbtw_asymm h

theorem isnd_of_isneg {θ : AngValue} (h : θ.IsNeg) : θ.IsND where
  ne_zero hs := not_isneg_of_eq_zero hs h
  ne_pi hs := not_isneg_of_eq_pi hs h

theorem not_ispos_of_not_isnd {θ : AngValue} (h : ¬ θ.IsND) : ¬ θ.IsPos := fun hs ↦ h (isnd_of_ispos hs)

theorem not_isneg_of_not_isnd {θ : AngValue} (h : ¬ θ.IsND) : ¬ θ.IsNeg := fun hs ↦ h (isnd_of_isneg hs)

theorem ispos_or_isneg_of_isnd {θ : AngValue} (h : θ.IsND) : θ.IsPos ∨ θ.IsNeg := by
  contrapose! h
  have h := (and_congr btw_iff_not_sbtw btw_iff_not_sbtw).mpr h
  rcases btw_antisymm (btw_cyclic_right h.1) (btw_cyclic_left h.2) with h | h
  · exact (pi_ne_zero h.symm).elim
  · exact not_isnd_iff.mpr (Or.comm.mp ((or_congr_left eq_comm).mp h))

theorem not_isnd_or_ispos_or_isneg {θ : AngValue} : ¬ θ.IsND ∨ θ.IsPos ∨ θ.IsNeg :=
  if h : θ.IsND then .inr (ispos_or_isneg_of_isnd h) else .inl h

end trichotomy

section toreal
-- expand this section, add θ.IsPos → (0 < (θ : ℝ)), ...
theorem zero_le_toreal_iff {θ : AngValue} : 0 ≤ (θ : ℝ) ↔ btw 0 θ π := by
  have hp : Fact (0 < 2 * π) := { out := Real.two_pi_pos }
  rw [← neg_coe_pi, ← θ.toreal_toangvalue_eq_self]
  refine' Iff.trans _ btw_cyclic.symm
  refine' (Eq.to_iff _).trans QuotientAddGroup.btw_coe_iff.symm
  congr
  refine' ((toIcoMod_eq_self hp.1).mpr _).symm
  rw [neg_add_eq_of_eq_add (two_mul π)]
  exact ⟨neg_nonpos.mpr (le_of_lt Real.pi_pos), Real.pi_pos⟩

theorem zero_le_toreal_of_ispos {θ : AngValue} (h : θ.IsPos) : 0 ≤ (θ : ℝ) :=
  zero_le_toreal_iff.mpr (btw_of_sbtw h)

theorem zero_lt_toreal_of_ispos {θ : AngValue} (h : θ.IsPos) : 0 < (θ : ℝ) :=
  (toreal_ne_zero_of_ne_zero (ne_zero_of_ispos h)).symm.lt_of_le (zero_le_toreal_of_ispos h)

theorem toreal_lt_pi_of_ispos {θ : AngValue} (h : θ.IsPos) : (θ : ℝ) < π :=
  (toreal_ne_pi_of_ne_pi (ne_pi_of_ispos h)).lt_of_le toreal_le_pi

theorem toreal_lt_zero_of_isneg {θ : AngValue} (h : θ.IsNeg) : (θ : ℝ) < 0 := by
  contrapose! h
  exact not_sbtw_of_btw (zero_le_toreal_iff.mp h)

theorem toreal_le_zero_of_isneg {θ : AngValue} (h : θ.IsNeg) : (θ : ℝ) ≤ 0 :=
  le_of_lt (toreal_lt_zero_of_isneg h)

theorem ispos_of_zero_lt_toreal_of_ne_pi {θ : AngValue} (h : 0 < (θ : ℝ)) (hn : θ ≠ π) : θ.IsPos :=
  Or.casesOn (ispos_or_isneg_of_isnd ⟨ne_zero_of_toreal_ne_zero (ne_of_gt h), hn⟩)
    (fun h ↦ h) (fun hp ↦ (not_lt_of_ge (toreal_le_zero_of_isneg hp) h).elim)

theorem isneg_of_toreal_lt_zero {θ : AngValue} (h : (θ : ℝ) < 0) : θ.IsNeg := by
  contrapose! h
  exact zero_le_toreal_iff.mpr (btw_iff_not_sbtw.mpr h)

theorem ispos_iff {θ : AngValue} : θ.IsPos ↔ (0 < (θ : ℝ) ∧ ((θ : ℝ) < π)) := ⟨
  fun h ↦ ⟨zero_lt_toreal_of_ispos h, toreal_lt_pi_of_ispos h⟩,
  fun h ↦ ispos_of_zero_lt_toreal_of_ne_pi h.1 (ne_pi_of_toreal_ne_pi (ne_of_lt h.2))⟩

theorem isneg_iff {θ : AngValue} : θ.IsNeg ↔ ((θ : ℝ) < 0) :=
  ⟨fun h ↦ toreal_lt_zero_of_isneg h, fun h ↦ isneg_of_toreal_lt_zero h⟩

theorem isnd_iff' {θ : AngValue} : θ.IsND ↔ ((θ : ℝ) ≠ 0 ∧ (θ : ℝ) ≠ π) := ⟨
  fun h ↦ ⟨toreal_ne_zero_of_ne_zero h.1, toreal_ne_pi_of_ne_pi h.2⟩,
  fun h ↦ ⟨ne_zero_of_toreal_ne_zero h.1 ,ne_pi_of_toreal_ne_pi h.2⟩⟩

theorem not_isnd_iff' {θ : AngValue} : ¬ θ.IsND ↔ ((θ : ℝ) = 0 ∨ (θ : ℝ) = π) :=
  isnd_iff'.not.trans (not_and_or.trans (or_congr not_ne_iff not_ne_iff))

end toreal

section neg
-- `add iff to simp`
theorem neg_isneg_of_ispos {θ : AngValue} (h : θ.IsPos) : (-θ).IsNeg := sorry

theorem neg_ispos_of_isneg {θ : AngValue} (h : θ.IsNeg) : (-θ).IsPos := sorry

theorem neg_isnd_of_isnd {θ : AngValue} (h : θ.IsND) : (-θ).IsND := sorry

theorem isneg_of_neg_ispos {θ : AngValue} (h : (-θ).IsPos) : θ.IsNeg := sorry

theorem ispos_of_neg_isneg {θ : AngValue} (h : (-θ).IsNeg) : θ.IsPos := sorry

theorem isnd_of_neg_isnd {θ : AngValue} (h : (-θ).IsND) : θ.IsND := sorry

@[simp]
theorem neg_ispos_iff_isneg {θ : AngValue} : (-θ).IsPos ↔ θ.IsNeg := sorry

@[simp]
theorem neg_isneg_iff_ispos {θ : AngValue} : (-θ).IsNeg ↔ θ.IsPos := sorry

@[simp]
theorem neg_isnd_iff_isnd {θ : AngValue} : (-θ).IsND ↔ θ.IsND := sorry

end neg

end AngValue

end pos_neg_isnd

-- `Do we prepare is acute, is right, ... here?` `To be added`

section trigonometric
-- `a section discussing cos sin, uniqueness with pos neg`
-- `sin >0 implies angle > 0, cos >0 implies ..., sin = 0 implies ...`
-- `acute, ... also implies uniqueness`
-- sin cos of special values is already at simp

@[simp]
theorem AngValue.cos_coe (x : ℝ) : cos (x.toAngValue) = Real.cos x := Real.Angle.cos_coe _

@[simp]
theorem AngValue.sin_coe (x : ℝ) : sin (x.toAngValue) = Real.sin x := Real.Angle.sin_coe _

theorem AngValue.cos_eq_iff_eq_or_eq_neg (ang₁ ang₂ : AngValue) : cos ang₁ = cos ang₂ ↔ ang₁ = ang₂ ∨ ang₁ = -ang₂  := Real.Angle.cos_eq_iff_eq_or_eq_neg

theorem pos_angle_eq_angle_iff_cos_eq_cos (ang₁ ang₂ : AngValue) (hang₁ : ang₁.IsPos) (hang₂ : ang₂.IsPos) : cos ang₁ = cos ang₂ ↔ ang₁ = ang₂ := by
  rw [Real.Angle.cos_eq_iff_eq_or_eq_neg]
  constructor
  intro e
  rcases e with e₁ | e₂
  · exact e₁
  · exfalso
    exact AngValue.not_isneg_of_ispos hang₁ (e₂ ▸ AngValue.neg_isneg_of_ispos hang₂)
  exact Or.inl

theorem neg_angle_eq_angle_iff_cos_eq_cos (ang₁ ang₂ : AngValue) (hang₁ : ang₁.IsNeg) (hang₂ : ang₂.IsNeg) : cos ang₁ = cos ang₂ ↔ ang₁ = ang₂ := by
  rw [Real.Angle.cos_eq_iff_eq_or_eq_neg]
  constructor
  intro e
  rcases e with e₁ | e₂
  · exact e₁
  · exfalso
    exact AngValue.not_ispos_of_isneg hang₁ (e₂ ▸ AngValue.neg_ispos_of_isneg hang₂)
  exact Or.inl

end trigonometric

@[pp_dot]
def AngValue.toDir (θ : AngValue) : Dir where
  toVec := ⟨cos θ, sin θ⟩
  unit := by
    unfold inner InnerProductSpace.toInner InnerProductSpace.complexToReal InnerProductSpace.isROrCToReal
    rw [← cos_sq_add_sin_sq θ]
    rw [pow_two, pow_two]
    simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]

@[pp_dot]
def Dir.toAngValue (d : Dir) : AngValue := (Complex.arg d.1 : Real.Angle)

section mul_add_isom

@[simp]
theorem toangvalue_todir_eq_self (d : Dir) : d.toAngValue.toDir = d := sorry

@[simp]
theorem todir_toangvalue_eq_self (θ : AngValue) : θ.toDir.toAngValue = θ := sorry

@[simp]
theorem zero_todir_eq_one : (0 : AngValue).toDir = 1 := by
  unfold AngValue.toDir
  ext
  simp only [cos_zero, Dir.one_eq_one_toComplex, Complex.one_re]
  simp only [sin_zero, Dir.one_eq_one_toComplex, Complex.one_im]

@[simp]
theorem one_toangvalue_eq_zero : (1 : Dir).toAngValue = 0 := sorry

@[simp]
theorem pi_todir_eq_neg_one : (π : AngValue).toDir = -1 := by
  unfold AngValue.toDir
  ext
  simp only [Dir.tovec_neg_eq_neg_tovec, Dir.one_eq_one_toComplex, Complex.neg_re, Complex.one_re]
  exact Real.Angle.cos_coe_pi
  simp only [Dir.tovec_neg_eq_neg_tovec, Dir.one_eq_one_toComplex, Complex.neg_im, Complex.one_im, neg_zero]
  exact Real.Angle.sin_coe_pi

@[simp]
theorem neg_one_toangvalue_eq_pi : (-1 : Dir).toAngValue = π := sorry

@[simp]
theorem pi_div_two_todir_eq_I : ((π/2 : ℝ) : AngValue).toDir = Dir.I := by
  unfold AngValue.toDir
  ext
  simp only [AngValue.cos_coe, Real.cos_pi_div_two, Dir.I_toComplex_eq_I, Complex.I_re]
  simp only [AngValue.sin_coe, Real.sin_pi_div_two, Dir.I_toComplex_eq_I, Complex.I_im]

@[simp]
theorem I_toangvalue_eq_pi_div_2 : Dir.I.toAngValue = (π/2 : ℝ)  := sorry

@[simp]
theorem neg_pi_div_two_todir_eq_neg_I : ((-π/2 : ℝ) : AngValue).toDir = -Dir.I := sorry

@[simp]
theorem neg_pi_div_two_todir_eq_neg_I' : AngValue.toDir ↑(-(π / 2)) = -Dir.I := by
  field_simp

@[simp]
theorem neg_I_toangvalue_eq_neg_pi_div_2 : (-Dir.I).toAngValue = (-π/2 : ℝ)  := sorry

@[simp]
theorem mul_toangvalue_eq_toangvalue_add (d₁ d₂ : Dir) : (d₁ * d₂).toAngValue = d₁.toAngValue + d₂.toAngValue := Complex.arg_mul_coe_angle (Dir.tovec_ne_zero _) (Dir.tovec_ne_zero _)

@[simp]
theorem add_todir_eq_todir_mul (θ₁ θ₂ : AngValue) : (θ₁ + θ₂).toDir = θ₁.toDir * θ₂.toDir := sorry

@[simp]
theorem inv_toangvalue_eq_toangvalue_neg (d : Dir) : (d⁻¹).toAngValue = - d.toAngValue := sorry

@[simp]
theorem neg_todir_eq_todir_inv (θ : AngValue) : (-θ).toDir  = θ.toDir⁻¹ := sorry

@[simp]
theorem div_toangvalue_eq_toangvalue_sub (d₁ d₂ : Dir) : (d₁ / d₂).toAngValue = d₁.toAngValue - d₂.toAngValue := sorry

@[simp]
theorem sub_todir_eq_todir_div (θ₁ θ₂ : AngValue) : (θ₁ - θ₂).toDir = θ₁.toDir / θ₂.toDir := sorry

@[simp]
theorem npow_toangvalue_eq_toangvalue_nsmul (n : ℕ) (d : Dir) : (d ^ n).toAngValue = n • d.toAngValue := sorry

@[simp]
theorem nsmul_todir_eq_todir_npow (n : ℕ) (θ : AngValue) : (n • θ).toDir = θ.toDir ^ n := sorry

@[simp]
theorem zpow_toangvalue_eq_toangvalue_zsmul (n : ℤ) (d : Dir) : (d ^ n).toAngValue = n • d.toAngValue := sorry

@[simp]
theorem zsmul_todir_eq_todir_zpow_ (n : ℤ) (θ : AngValue) : (n • θ).toDir = θ.toDir ^ n := sorry

-- not really useful, fields and corollories are really useful, should write out explicitly
def AddDir.toAngValue.add_hom : Additive Dir ≃+ AngValue where
  toFun := fun d => Dir.toAngValue d
  invFun := fun θ => AngValue.toDir θ
  left_inv := toangvalue_todir_eq_self
  right_inv := todir_toangvalue_eq_self
  map_add' := mul_toangvalue_eq_toangvalue_add

end mul_add_isom

end angvalue

section angdvalue

def AngDValue := AddCircle π

instance : NormedAddCommGroup AngDValue := inferInstanceAs (NormedAddCommGroup (AddCircle π))

-- `structure not really usefu?`
-- `can we use < of setoid to define this map? does this create more rfl?`
@[pp_dot]
def AngValue.toAngDValue : AngValue → AngDValue := Quotient.lift (fun x : ℝ => (x : AddCircle π)) sorry

instance : Coe AngValue AngDValue where
  coe := AngValue.toAngDValue

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

def AngValue.toAngDValue.add_hom : AngValue →+ AngDValue where
  toFun := AngValue.toAngDValue
  map_zero' := sorry
  map_add' := sorry

end angvalue_angdvalue_compatibility

@[coe]
def Real.toAngDValue : ℝ → AngDValue := fun r => (r : AddCircle π)

instance : Coe ℝ AngDValue where
  coe := Real.toAngDValue

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

@[pp_dot]
def AngDValue.toProj : AngDValue → Proj := Quotient.lift (fun θ => (AngValue.toDir θ : Proj)) sorry

@[pp_dot]
def Proj.toAngDValue : Proj → AngDValue := Quotient.lift (fun p => AngValue.toAngDValue (Complex.arg (p : Dir).1 : Real.Angle)) sorry

section mul_add_isom
-- `just copy section mul_add_isom of Dir AngValue`

def AddProj.toAngDValue : Additive Proj ≃+ AngDValue where
  toFun := Quotient.lift (fun p => AngValue.toAngDValue (Complex.arg (p : Dir).1 : Real.Angle)) sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_add' _ _:= by sorry

end mul_add_isom

@[simp]
theorem toproj_toangdvalue_eq_toangvalue_toangdvalue (x : Dir) : x.toProj.toAngDValue = x.toAngValue.toAngDValue := rfl

end angdvalue

def Dir.AngDiff (x y : Dir) : AngValue := (y / x).toAngValue

-- Our aim is to prove the Cosine value of the angle of two Vec_nd-s, their norm and inner product satisfy THE EQUALITY. We will use this to prove the Cosine theorem of Triangle, which is in the file Trigonometric

section Cosine_theorem_for_Vec_nd

theorem fst_of_angle_tovec (x y : Dir) : (y * (x⁻¹)).1.1 = x.1.1 * y.1.1 + x.1.2 * y.1.2 := by
  have h : x.1.1 * y.1.1 + x.1.2 * y.1.2 = y.1.1 * x.1.1 - y.1.2 * (-x.1.2) := by ring
  rw [h]
  rfl

def Vec_nd.angle (v₁ v₂ : Vec_nd) := Dir.AngDiff (Vec_nd.toDir v₁) (Vec_nd.toDir v₂)

@[simp]
theorem cos_arg_of_dir_eq_fst (x : Dir) : cos (x.toAngValue) = x.1.1 := by
  have w₁ : (AngValue.toDir (x.toAngValue)).1.1 = cos (x.toAngValue) := rfl
  simp [← w₁, toangvalue_todir_eq_self]

@[simp]
theorem sin_arg_of_dir_eq_fst (x : Dir) : sin (x.toAngValue) = x.1.2 := by
  have w₁ : (AngValue.toDir (x.toAngValue)).1.2 = sin (x.toAngValue) := rfl
  simp only [← w₁, toangvalue_todir_eq_self]

theorem cos_angle_of_dir_dir_eq_inner (d₁ d₂ : Dir) : cos (Dir.AngDiff d₁ d₂) = inner d₁.1 d₂.1 := by
  unfold Dir.AngDiff inner InnerProductSpace.toInner InnerProductSpace.complexToReal InnerProductSpace.isROrCToReal
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
  rw [cos_arg_of_dir_eq_fst]
  exact (fst_of_angle_tovec d₁ d₂)

theorem norm_mul_norm_mul_cos_angle_eq_inner_of_Vec_nd (v₁ v₂ : Vec_nd) : (Vec.norm v₁) * (Vec.norm v₂) * cos (Vec_nd.angle v₁ v₂) = inner v₁.1 v₂.1 := by
  have h : @inner ℝ _ _ v₁.1 v₂.1 = inner (v₁.norm • (Vec_nd.toDir v₁).1) (v₂.norm • (Vec_nd.toDir v₂).1) := by simp only [ne_eq,
    Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add,
    Vec_nd.norm_smul_todir_eq_self]
  rw [h]
  rw [inner_smul_left, inner_smul_right, ← cos_angle_of_dir_dir_eq_inner, mul_assoc]
  rfl

theorem perp_iff_angle_eq_pi_div_two_or_angle_eq_neg_pi_div_two (v₁ v₂ : Vec_nd) : v₁.toProj = v₂.toProj.perp ↔ (Vec_nd.angle v₁ v₂ = ↑(π / 2)) ∨ (Vec_nd.angle v₁ v₂ = ↑(-π / 2)) := by
  let d₁ := Vec_nd.toDir v₁
  let d₂ := Vec_nd.toDir v₂
  constructor
  intro h
  let h := Quotient.exact h
  unfold HasEquiv.Equiv instHasEquiv PM.con PM at h
  simp only [Con.rel_eq_coe, Con.rel_mk] at h
  unfold Vec_nd.angle Dir.AngDiff
  by_cases v₁.toDir = Dir.I * v₂.toDir
  · right
    rw [h]
    simp only [div_mul_cancel''', Dir.inv_of_I_eq_neg_I, neg_I_toangvalue_eq_neg_pi_div_2]
  · left
    have e : d₂ / d₁ = Dir.I := by
      have w : d₁ = - (Dir.I * d₂) := by tauto
      rw [← neg_mul, ← Dir.inv_of_I_eq_neg_I] at w
      exact Eq.symm (eq_mul_inv_of_mul_eq (mul_eq_of_eq_inv_mul w))
    rw [e]
    simp only [I_toangvalue_eq_pi_div_2]
  intro h
  by_cases Dir.AngDiff d₁ d₂ = ↑(π / 2)
  · have w : AngValue.toDir (Dir.AngDiff d₁ d₂) = AngValue.toDir ↑(π / 2) := by
      rw [h]
    unfold Dir.AngDiff at w
    simp only [toangvalue_todir_eq_self, pi_div_two_todir_eq_I] at w
    unfold Vec_nd.toProj Proj.perp
    have e : Vec_nd.toDir v₂ = d₂ := rfl
    have e' : d₂ = Dir.I * d₁ := by
      exact eq_mul_of_div_eq w
    have e'' : Dir.toProj (Dir.I * d₁) = Proj.I * d₁.toProj := rfl
    rw [e, e', e'', ← mul_assoc]
    simp only [Proj.I_mul_I_eq_one_of_Proj, one_mul]
  · have w : AngValue.toDir (Dir.AngDiff d₁ d₂) = AngValue.toDir (↑(-π / 2)) := by
      have w' : Dir.AngDiff d₁ d₂ = ↑(-π / 2) := by tauto
      rw [w']
    unfold Dir.AngDiff at w
    simp only [I_toangvalue_eq_pi_div_2] at w
    unfold Vec_nd.toProj Proj.perp
    have e : Vec_nd.toDir v₁ = d₁ := rfl
    have e' : d₁ = Dir.I * d₂ := by
      simp only [neg_pi_div_two_todir_eq_neg_I] at w
      rw [← Dir.inv_of_I_eq_neg_I] at w
      simp only [div_toangvalue_eq_toangvalue_sub, sub_todir_eq_todir_div, toangvalue_todir_eq_self] at w
      exact eq_mul_of_inv_mul_eq (mul_eq_of_eq_div (Eq.symm w))
    rw [e, e']
    rfl

end Cosine_theorem_for_Vec_nd

section Linear_Algebra

theorem det_eq_sin_mul_norm_mul_norm' (u v :Dir) : det u.1 v.1 = sin (Dir.AngDiff u v) := by
  rw [det_eq_im_of_quotient]
  unfold Dir.AngDiff
  rw [sin_arg_of_dir_eq_fst]
  rfl

theorem det_eq_sin_mul_norm_mul_norm (u v : Vec_nd): det u v = sin (Vec_nd.angle u v) * Vec.norm u * Vec.norm v := by
  let nu := u.toDir
  let nv := v.toDir
  let unorm := u.norm
  let vnorm := v.norm
  have hu : u.1 = u.norm • nu.1 := by simp only [ne_eq, Vec_nd.norm_smul_todir_eq_self]
  have hv : v.1 = v.norm • nv.1 := by simp only [ne_eq, Vec_nd.norm_smul_todir_eq_self]
  rw [hu, hv, det_smul_left_eq_mul_det, det_smul_right_eq_mul_det]
  have unorm_nonneg : 0 ≤ unorm := Vec.norm_nonnegative u
  have vnorm_nonneg : 0 ≤ vnorm := Vec.norm_nonnegative v
  rw [Vec.norm_smul_eq_mul_norm (unorm_nonneg), Vec.norm_smul_eq_mul_norm (vnorm_nonneg)]
  have : det nu.1 nv.1 = sin (Vec_nd.angle u v) * Vec.norm nu.1 *Vec.norm nv.1 := by
    rw[Dir.norm_of_dir_tovec_eq_one, Dir.norm_of_dir_tovec_eq_one, mul_one, mul_one, det_eq_sin_mul_norm_mul_norm']
    unfold Vec_nd.angle
    rfl
  rw[this]
  ring

end Linear_Algebra

-- Here is a small section which would not be used later. We just compare our definitions to the standard sameRay definitions.
section sameRay_theorems

theorem sameRay_iff_eq (a b : Dir) : SameRay ℝ a.1 b.1 ↔ a = b := by
  rw [Complex.sameRay_iff]
  constructor
  · simp only [Dir.tovec_ne_zero, false_or]
    intro h
    have g : a.toAngValue.toDir = b.toAngValue.toDir := congrArg (fun (z : Real) => z.toAngValue.toDir) h
    simp only [toangvalue_todir_eq_self] at g
    exact g
  · tauto

theorem sameRay_Vec_nd_toDir (z : Vec_nd) : SameRay ℝ z.1 z.toDir.1 := by
  rw [Complex.sameRay_iff_arg_div_eq_zero, (Vec_nd.norm_smul_todir_eq_self z).symm, Complex.real_smul, ← mul_div, div_self (Dir.tovec_ne_zero (Vec_nd.toDir z)), mul_one, norm_of_Vec_nd_eq_norm_of_Vec_nd_fst]
  exact Complex.arg_ofReal_of_nonneg (Vec.norm_nonnegative z)

theorem toDir_eq_toDir_of_sameRay (z₁ z₂ : Vec_nd) : SameRay ℝ z₁.1 z₂.1 → z₁.toDir = z₂.toDir := fun h => (sameRay_iff_eq z₁.toDir z₂.toDir).1 (SameRay.symm (SameRay.trans (SameRay.symm (SameRay.trans h (sameRay_Vec_nd_toDir z₂) (by simp only [ne_eq, ne_zero_of_Vec_nd, false_or, IsEmpty.forall_iff]))) (sameRay_Vec_nd_toDir z₁) (by simp only [ne_eq, ne_zero_of_Vec_nd, false_or, IsEmpty.forall_iff])))

end sameRay_theorems

section half

namespace AngValue

def half (θ : AngValue) : AngValue := (θ.toReal / 2).toAngValue

theorem smul_two_half {θ : AngValue} : 2 • θ.half = θ := θ.two_nsmul_toreal_div_two

end AngValue

end half

end EuclidGeom
