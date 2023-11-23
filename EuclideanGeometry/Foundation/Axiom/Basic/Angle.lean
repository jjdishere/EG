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
def AngValue := Real.Angle

instance : NormedAddCommGroup AngValue := inferInstanceAs (NormedAddCommGroup Real.Angle)

instance : CircularOrder AngValue := inferInstanceAs (CircularOrder Real.Angle)

end angvalue
end EuclidGeom

@[pp_dot]
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

theorem toreal_le_pi {θ : AngValue} : θ.toReal ≤ π := sorry

theorem toreal_neg_pi_le {θ : AngValue} : -π < θ.toReal := sorry

section composite

@[simp]
theorem toreal_toangvalue_eq_self {θ : AngValue}:  (θ.toReal).toAngValue = θ := by sorry

theorem toangvalue_toreal_eq_self_of_neg_pi_lt_le_pi {r : ℝ} (h₁ : -π < r) (h₂ : r ≤ π) : r.toAngValue.toReal = r := sorry

theorem toangvalue_toreal_eq_self_add_two_mul_int_mul_pi (r : ℝ) : ∃ k : ℤ, r.toAngValue.toReal = r + k * (2 * π) := sorry

theorem toangvalue_eq_of_add_two_mul_int_mul_pi {r₁ r₂ : ℝ} (k : ℤ) (h : r₁ = r₂ + k *(2 * π)) : r₁.toAngValue = r₂.toAngValue := sorry

end composite

section special_value
--special values -pi 0 pi 2pi -2pi `To be added`
@[simp]
theorem AngValue.coe_zero : ((0 : Real) : AngValue) = (0 : AngValue) := rfl

@[simp]
theorem AngValue.coe_two_pi : ((2 * π : Real) : AngValue) = (0 : AngValue) := Real.Angle.coe_two_pi

@[simp]
theorem AngValue.neg_coe_pi : (-π :AngValue) = (π : AngValue)  := Real.Angle.neg_coe_pi


end special_value

section group_hom
--`add sub neg smul` `to be added`
-- `the current direction of simp is turn every thing into Real, is this good?`
@[simp]
theorem AngValue.add_coe (x y: ℝ) : (x : AngValue) + (y : AngValue) = (((x + y) : ℝ) : AngValue) := rfl

@[simp]
theorem AngValue.sub_coe (x y: ℝ) : (x : AngValue) - (y : AngValue) = (((x - y) : ℝ) : AngValue)  := rfl

@[simp]
theorem AngValue.nat_mul_coe (n : ℕ) (x : ℝ) : n • (x : AngValue) = ((n * x: ℝ) : AngValue) := (nsmul_eq_mul _ x) ▸ Eq.refl _

@[simp]
theorem AngValue.int_mul_coe (n : ℤ) (x : ℝ) : n • (x : AngValue) = ((n * x : ℝ ) : AngValue) := (zsmul_eq_mul x _) ▸ Eq.refl _

@[simp]
theorem AngValue.neg_coe (x : ℝ): -(x : AngValue) = (((-x) : ℝ) : AngValue) := rfl


end group_hom

end real_angvalue_compatibility

section pos_neg_isnd

namespace AngValue

@[pp_dot]
def IsPos (θ : AngValue) : Prop := sbtw 0 θ π

@[pp_dot]
def IsNeg (θ : AngValue) : Prop := sbtw (π: Real.Angle) θ 0

@[pp_dot]
def IsND (θ : AngValue) : Prop := ¬ (θ = 0 ∨ θ = π)

section trichotomy

theorem not_isneg_of_ispos {θ : AngValue} : θ.IsPos → ¬ θ.IsNeg := sorry

theorem isnd_of_ispos {θ : AngValue} : θ.IsPos → θ.IsND := sorry

theorem not_ispos_of_isneg {θ : AngValue} : θ.IsNeg → ¬ θ.IsPos := sorry

theorem isnd_of_isneg {θ : AngValue} : θ.IsNeg → θ.IsND := sorry

theorem not_ispos_of_isnd {θ : AngValue} : θ.IsND → ¬ θ.IsPos := sorry

theorem not_isneg_of_isnd {θ : AngValue} : θ.IsND → ¬ θ.IsNeg := sorry

theorem ispos_or_isneg_or_not_isnd {θ : AngValue} : θ.IsPos ∨ θ.IsNeg ∨ ¬ θ.IsND := sorry

end trichotomy

section neg

theorem neg_isneg_of_ispos {θ : AngValue} : θ.IsPos → (-θ).IsNeg := sorry

theorem neg_ispos_of_isneg {θ : AngValue} : θ.IsNeg → (-θ).IsPos := sorry

theorem neg_isnd_of_isnd {θ : AngValue} : θ.IsND → (-θ).IsND := sorry

end neg

theorem not_is_nd_iff {θ : AngValue} : ¬ θ.IsND ↔ (θ = 0 ∨ θ = π) := sorry

section toreal
-- expand this section, add θ.IsPos → (0 < (θ : ℝ)), ...
theorem ispos_iff' {θ : AngValue} : θ.IsPos ↔ (0 < (θ : ℝ) ∧ ((θ : ℝ) < π)) := sorry

theorem isneg_iff' {θ : AngValue} : θ.IsNeg ↔ (-π < (θ : ℝ) ∧ ((θ : ℝ) < 0)) := sorry

theorem not_is_nd_iff' {θ : AngValue} : ¬ θ.IsND ↔ ((θ : ℝ) = 0 ∨ (θ : ℝ) = π) := sorry

end toreal

end AngValue
end pos_neg_isnd

-- `Do we prepare is acute, is right, ... here?` `To be added`

section trignometric
-- `a section discussing cos sin, uniqueness with pos neg`
-- `acute, ... also implies uniqueness`
-- sin cos special values is already at simp

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

end trignometric

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
--`TBA`
-- `not reall useful, fields and corollories are really useful, should write out explicitly` `Avoid AddDir`
def AddDir.toAngValue : Additive Dir ≃+ AngValue where
  toFun := fun d => (Complex.arg (d : Dir).1 : Real.Angle)
  invFun := fun θ => AngValue.toDir θ
  left_inv := sorry
  right_inv := sorry
  map_add' _ _:= Complex.arg_mul_coe_angle (Dir.tovec_ne_zero _) (Dir.tovec_ne_zero _)

end mul_add_isom


end angvalue

section angdvalue

def AngDValue := AddCircle π

instance : NormedAddCommGroup AngDValue := inferInstanceAs (NormedAddCommGroup (AddCircle π))

-- `structure not really usefu?`
-- `can we use < of setoid to define this map? does this create more rfl?`
def AngValue.toAngDValue : AngValue →+ AngDValue where
  toFun := Quotient.lift (fun x : ℝ => (x : AddCircle π)) sorry
  map_zero' := sorry
  map_add' := sorry

instance : Coe AngValue AngDValue where
  coe := AngValue.toAngDValue

def Real.toAngDValue : ℝ → AngDValue := fun r => (r : AngDValue)

instance : Coe ℝ AngDValue where
  coe := Real.toAngDValue

def AddDir.toAngDValue : Additive Dir →+ AngDValue where
  toFun := fun d => AngValue.toAngDValue (Complex.arg (d : Dir).1 : Real.Angle)
  map_zero' := by
    have : (1 : Dir) = (0 : Additive Dir) := rfl
    simp only [this ▸ Dir.one_eq_one_toComplex, Complex.arg_one, Real.Angle.coe_zero, map_zero]
  map_add' _ _:= by sorry

def Dir.toAngDValue : Dir → AngDValue := fun d => AddDir.toAngDValue d

def AngDValue.toProj : AngDValue → Proj := Quotient.lift (fun θ => (AngValue.toDir θ : Proj)) sorry

def AddProj.toAngDValue : Additive Proj ≃+ AngDValue where
  toFun := Quotient.lift (fun p => AngValue.toAngDValue (Complex.arg (p : Dir).1 : Real.Angle)) sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_add' _ _:= by sorry

def Proj.toAngDValue : Proj → AngDValue := fun p => AddProj.toAngDValue p
-- some coercion compatibility
-- special values
-- lift +-
-- pos neg 0

end angdvalue


-- def angle (x y : Dir) := Complex.arg ( (y * (x⁻¹)).1)
--`should change to`
-- def Dir.Angle_diff (x y : Dir) := (y * (x⁻¹)).toAngValue
--`All following theorems needs to change`

theorem fst_of_angle_tovec (x y : Dir) : (y * (x⁻¹)).1.1 = x.1.1 * y.1.1 + x.1.2 * y.1.2 := by
  have h : x.1.1 * y.1.1 + x.1.2 * y.1.2 = y.1.1 * x.1.1 - y.1.2 * (-x.1.2) := by ring
  rw [h]
  rfl

/-
def AngValue.toDir (θ : ℝ) : Dir where
  toVec := ⟨cos θ, sin θ⟩
  unit := by
    unfold inner InnerProductSpace.toInner InnerProductSpace.complexToReal InnerProductSpace.isROrCToReal
    rw [← cos_sq_add_sin_sq θ]
    rw [pow_two, pow_two]
    simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
-/
--`should remove Complex.arg, we use Dir.toAngValue now`
section Make_angle_theorems

@[simp]
theorem angvalue_todir_arg_toComplex_of_nonzero_eq_todir (x : Vec_nd) : AngValue.toDir (Complex.arg x.1) = Vec_nd.toDir x := by
  unfold Vec_nd.toDir AngValue.toDir HSMul.hSMul instHSMul SMul.smul Complex.instSMulRealComplex Vec.norm
  simp only [ne_eq, smul_eq_mul, zero_mul, sub_zero, add_zero]
  ext <;>
  dsimp <;>
  unfold Real.toAngValue
  rw [Real.Angle.cos_coe, Complex.cos_arg]
  ring
  exact x.2
  rw [Real.Angle.sin_coe, Complex.sin_arg]
  ring

@[simp]
theorem angvalue_todir_arg_toComplex_of_Dir_eq_self (x: Dir) : AngValue.toDir (Complex.arg (x.1)) = x := by
  have w : Complex.abs (x.1) = 1 := Dir.norm_of_dir_tovec_eq_one x
  ext : 1
  unfold AngValue.toDir Real.toAngValue
  simp only [cos_coe, sin_coe]
  rw [Complex.cos_arg, Complex.sin_arg, w]
  unfold Dir.toVec
  ext : 1
  simp only [div_one]
  simp only [div_one]
  by_contra h
  rw [h] at w
  simp only [map_zero, zero_ne_one] at w

@[simp]
theorem angvalue_todir_zero_eq_one : AngValue.toDir 0 = 1 := by
  unfold AngValue.toDir
  ext
  simp only [cos_zero, sin_zero, Dir.fst_of_one_eq_one]
  simp only [cos_zero, sin_zero, Dir.snd_of_one_eq_zero]

@[simp]
theorem angvalue_todir_pi_eq_neg_one : AngValue.toDir π = -1 := by
  unfold AngValue.toDir
  ext
  simp only [cos_pi, sin_pi, tovec_neg_eq_neg_tovec, one_eq_one_toComplex, Complex.neg_re, Complex.one_re]
  simp only [cos_pi, sin_pi, tovec_neg_eq_neg_tovec, one_eq_one_toComplex, Complex.neg_im, Complex.one_im, neg_zero]

@[simp]
theorem angvalue_todir_neg_pi_eq_neg_one : AngValue.toDir (-π) = -1 := by
  unfold AngValue.toDir
  ext
  simp only [cos_neg, cos_pi, sin_neg, sin_pi, neg_zero, tovec_neg_eq_neg_tovec, one_eq_one_toComplex, Complex.neg_re, Complex.one_re]
  simp only [cos_neg, cos_pi, sin_neg, sin_pi, neg_zero, tovec_neg_eq_neg_tovec, one_eq_one_toComplex, Complex.neg_im, Complex.one_im]

theorem angvalue_todir_neg_mul_angvalue_todir_eq_one (x : ℝ) : AngValue.toDir (-x) * AngValue.toDir x = 1 := by
  ext
  unfold toVec AngValue.toDir HMul.hMul instHMul Mul.mul instMulDir
  simp only [cos_neg, sin_neg, Complex.mul_re, neg_mul, sub_neg_eq_add]
  rw [← pow_two, ← pow_two, cos_sq_add_sin_sq x]
  rfl
  unfold toVec AngValue.toDir HMul.hMul instHMul Mul.mul instMulDir
  simp only [cos_neg, sin_neg, Complex.mul_im, neg_mul]
  rw [mul_comm, add_right_neg]
  rfl

@[simp]
theorem angvalue_todir_neg_eq_AngValue.toDir_inv (x : ℝ) : AngValue.toDir (-x) = (AngValue.toDir x)⁻¹ := by
  rw [← one_mul (AngValue.toDir x)⁻¹, ← angvalue_todir_neg_mul_angvalue_todir_eq_one x, mul_assoc, mul_right_inv, mul_one]

@[simp]
theorem angvalue_todir_pi_div_two_eq_I : AngValue.toDir (π / 2) = I := by
  unfold AngValue.toDir
  ext
  simp only [cos_pi_div_two, sin_pi_div_two, fst_of_I_eq_zero]
  simp only [cos_pi_div_two, sin_pi_div_two, snd_of_I_eq_one]

@[simp]
theorem angvalue_todir_neg_pi_div_two_eq_neg_I : AngValue.toDir (-(π / 2)) = -I := by
  unfold AngValue.toDir
  ext
  simp only [cos_neg, cos_pi_div_two, sin_neg, sin_pi_div_two, tovec_neg_eq_neg_tovec, I_toComplex_eq_I, Complex.neg_re, Complex.I_re, neg_zero]
  simp only [cos_neg, cos_pi_div_two, sin_neg, sin_pi_div_two, tovec_neg_eq_neg_tovec, I_toComplex_eq_I, Complex.neg_im, Complex.I_im]

@[simp]
theorem AngValue.toDir_neg_pi_div_two_eq_neg_I' : AngValue.toDir ((-π) / 2) = -I := by
  rw [neg_div]
  simp only [angvalue_todir_neg_pi_div_two_eq_neg_I]

end Make_angle_theorems

-- Our aim is to prove the Cosine value of the angle of two Vec_nd-s, their norm and inner product satisfy THE EQUALITY. We will use this to prove the Cosine theorem of Triangle, which is in the file Trigonometric

section Cosine_theorem_for_Vec_nd

theorem Vec_nd.norm_smul_todir_eq_self (v : Vec_nd) : Vec.norm v.1 • (Vec_nd.toDir v).toVec = v := by
  symm
  apply (inv_smul_eq_iff₀ (Iff.mpr norm_ne_zero_iff v.2)).1
  rfl

def Vec_nd.angle (v₁ v₂ : Vec_nd) := Dir.angle (Vec_nd.toDir v₁) (Vec_nd.toDir v₂)

theorem cos_arg_of_dir_eq_fst (x : Dir) : cos (Complex.arg x.1) = x.1.1 := by
  have w₁ : (AngValue.toDir (Complex.arg x.1)).1.1 = cos (Complex.arg x.1) := rfl
  simp only [← w₁, angvalue_todir_arg_toComplex_of_Dir_eq_self]

theorem sin_arg_of_dir_eq_fst (x : Dir) : sin (Complex.arg (x.1)) = x.1.2 := by
  have w₁ : (AngValue.toDir (Complex.arg (x.1))).1.2 = sin (Complex.arg (x.1)) := rfl
  simp only [← w₁, angvalue_todir_arg_toComplex_of_Dir_eq_self]

theorem cos_angle_of_dir_dir_eq_inner (d₁ d₂ : Dir) : cos (Dir.angle d₁ d₂) = inner d₁.1 d₂.1 := by
  unfold Dir.angle inner InnerProductSpace.toInner InnerProductSpace.complexToReal InnerProductSpace.isROrCToReal
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
  rw [cos_arg_of_dir_eq_fst]
  exact (Dir.fst_of_angle_tovec d₁ d₂)

theorem norm_mul_norm_mul_cos_angle_eq_inner_of_Vec_nd (v₁ v₂ : Vec_nd) : (Vec.norm v₁) * (Vec.norm v₂) * cos (Vec_nd.angle v₁ v₂) = inner v₁.1 v₂.1 := by
  have h : @inner ℝ _ _ v₁.1 v₂.1 = inner (Vec.norm v₁ • (Vec_nd.toDir v₁).1) (Vec.norm v₂ • (Vec_nd.toDir v₂).1) := by
    nth_rw 1 [← Vec_nd.norm_smul_todir_eq_self v₁, ← Vec_nd.norm_smul_todir_eq_self v₂]
  rw [h]
  rw [inner_smul_left, inner_smul_right, ← cos_angle_of_dir_dir_eq_inner, mul_assoc]
  rfl

theorem perp_iff_angle_eq_pi_div_two_or_angle_eq_neg_pi_div_two (v₁ v₂ : Vec_nd) : v₁.toProj = v₂.toProj.perp ↔ (Vec_nd.angle v₁ v₂ = π / 2) ∨ (Vec_nd.angle v₁ v₂ = -(π / 2)) := by
  let d₁ := Vec_nd.toDir v₁
  let d₂ := Vec_nd.toDir v₂
  constructor
  intro h
  let h := Quotient.exact h
  unfold HasEquiv.Equiv instHasEquiv PM.con PM at h
  simp only [Con.rel_eq_coe, Con.rel_mk] at h
  unfold Vec_nd.angle Dir.angle
  by_cases d₁ = Dir.I * d₂
  · right
    rw [mul_inv_eq_of_eq_mul (Eq.symm (inv_mul_eq_of_eq_mul h))]
    simp only [Dir.inv_of_I_eq_neg_I, Dir.neg_I_toComplex_eq_neg_I, Complex.arg_neg_I]
  · left
    have e : d₂ * d₁⁻¹ = Dir.I := by
      have w : d₁ = - (Dir.I * d₂) := by tauto
      rw [← neg_mul, ← Dir.inv_of_I_eq_neg_I] at w
      exact Eq.symm (eq_mul_inv_of_mul_eq (mul_eq_of_eq_inv_mul w))
    rw [e]
    simp only [Dir.I_toComplex_eq_I, Complex.arg_I]
  intro h
  by_cases Dir.angle d₁ d₂ = π / 2
  · have w : AngValue.toDir (Dir.angle d₁ d₂) = AngValue.toDir (π / 2) := by
      rw [h]
    unfold Dir.angle at w
    simp only [angvalue_todir_arg_toComplex_of_Dir_eq_self, angvalue_todir_pi_div_two_eq_I] at w
    unfold Vec_nd.toProj Proj.perp
    have e : Vec_nd.toDir v₂ = d₂ := rfl
    have e' : d₂ = Dir.I * d₁ := by
      exact eq_mul_of_div_eq w
    have e'' : Dir.toProj (Dir.I * d₁) = Proj.I * d₁.toProj := rfl
    rw [e, e', e'', ← mul_assoc]
    simp only [Proj.I_mul_I_eq_one_of_Proj, one_mul]
  · have w : AngValue.toDir (Dir.angle d₁ d₂) = AngValue.toDir (-(π / 2)) := by
      have w' : Dir.angle d₁ d₂ = -(π / 2) := by tauto
      rw [w']
    unfold Dir.angle at w
    simp only [angvalue_todir_arg_toComplex_of_Dir_eq_self, angvalue_todir_neg_eq_angvalue_todir_inv,
      angvalue_todir_pi_div_two_eq_I, Dir.inv_of_I_eq_neg_I] at w
    unfold Vec_nd.toProj Proj.perp
    have e : Vec_nd.toDir v₁ = d₁ := rfl
    have e' : d₁ = Dir.I * d₂ := by
      rw [← Dir.inv_of_I_eq_neg_I] at w
      exact eq_mul_of_inv_mul_eq (mul_eq_of_eq_div (Eq.symm w))
    rw [e, e']
    rfl

end Cosine_theorem_for_Vec_nd

section Linear_Algebra

theorem det_eq_sin_mul_norm_mul_norm' (u v :Dir) : det u.1 v.1 = sin (Dir.angle u v) := by
  rw [det_eq_im_of_quotient]
  unfold Dir.angle
  rw [sin_arg_of_dir_eq_fst]

theorem det_eq_sin_mul_norm_mul_norm (u v : Vec_nd): det u v = sin (Vec_nd.angle u v) * Vec.norm u * Vec.norm v := by
  let nu := u.toDir
  let nv := v.toDir
  let unorm := u.norm
  let vnorm := v.norm
  have hu : u.1 = unorm • nu.1 := Vec_nd.self_eq_norm_smul_todir u
  have hv : v.1 = vnorm • nv.1 := Vec_nd.self_eq_norm_smul_todir v
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
  · simp only [tovec_ne_zero, false_or]
    intro h
    let g := congrArg (fun z => mk_angle z) h
    simp only [mk_angle_arg_toComplex_of_Dir_eq_self] at g
    exact g
  · tauto

theorem sameRay_Vec_nd_toDir (z : Vec_nd) : SameRay ℝ z.1 z.toDir.1 := by
  rw [Complex.sameRay_iff_arg_div_eq_zero, Vec_nd.self_eq_norm_smul_todir z, Complex.real_smul, ← mul_div, div_self (tovec_ne_zero (Vec_nd.toDir z)), mul_one, norm_of_Vec_nd_eq_norm_of_Vec_nd_fst]
  exact Complex.arg_ofReal_of_nonneg (Vec.norm_nonnegative z)

theorem toDir_eq_toDir_of_sameRay (z₁ z₂ : Vec_nd) : SameRay ℝ z₁.1 z₂.1 → z₁.toDir = z₂.toDir := fun h => (sameRay_iff_eq z₁.toDir z₂.toDir).1 (SameRay.symm (SameRay.trans (SameRay.symm (SameRay.trans h (sameRay_Vec_nd_toDir z₂) (by simp only [ne_eq, ne_zero_of_Vec_nd, false_or, IsEmpty.forall_iff]))) (sameRay_Vec_nd_toDir z₁) (by simp only [ne_eq, ne_zero_of_Vec_nd, false_or, IsEmpty.forall_iff])))

end sameRay_theorems

end EuclidGeom
