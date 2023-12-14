import EuclideanGeometry.Foundation.Axiom.Basic.Angle
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.NormedSpace.Ray
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Logic.Equiv.TransferInstance

/-!
# Standard Vector Space

This file defines the standard inner product real vector space of dimension two, but we will build this on the complex numbers.

## Important definitions

## Notation

## Implementation Notes

## Further Works

-/

set_option autoImplicit false

alias Units.coe_div := Units.val_div_eq_div_val

section -- should be in mathlib

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable {x y : E}
variable {F : Type*} [SMulHomClass F ℝ E M] (f : F)

theorem SameRay.norm_smul_map_eq (h : SameRay ℝ x y) : ‖x‖ • f y = ‖y‖ • f x := by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  simp only [norm_smul_of_nonneg, *, mul_smul]
  rw [smul_comm, smul_comm b, map_smul, map_smul, smul_comm a b (f u)]

end

section -- should be in mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable {x y : E}
variable {F : Type*} [SMulHomClass F ℝ E M] (f : F)

theorem SameRay.inv_norm_smul_map_eq (hx : x ≠ 0) (hy : y ≠ 0) (h : SameRay ℝ x y) :
    ‖x‖⁻¹ • f x = ‖y‖⁻¹ • f y := by
  rw [inv_smul_eq_iff₀, smul_comm, eq_comm, inv_smul_eq_iff₀, h.norm_smul_map_eq] <;>
    rwa [norm_ne_zero_iff]

end

namespace Module.Ray -- should be in mathlib

variable {R : Type*} [StrictOrderedCommSemiring R]
  {M₁ : Type*} [AddCommMonoid M₁] [Module R M₁]
  {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂]
  {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃]

theorem map_trans (e₁₂ : M₁ ≃ₗ[R] M₂) (e₂₃ : M₂ ≃ₗ[R] M₃) :
    map (e₁₂.trans e₂₃) = (map e₁₂).trans (map e₂₃) := by
  ext ⟨v⟩
  rfl

end Module.Ray

namespace Projectivization -- should be in mathlib

open scoped LinearAlgebra.Projectivization

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
variable {L W : Type*} [DivisionRing L] [AddCommGroup W] [Module L W]
variable {σ : K →+* L} {σ' : L →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

/-- An semilinear equivalence of vector spaces induces a equivalence on projective spaces. -/
def mapEquiv (f : V ≃ₛₗ[σ] W) : ℙ K V ≃ ℙ L W where
  toFun := map f.toLinearMap f.injective
  invFun := map f.symm.toLinearMap f.symm.injective
  left_inv x := by
    induction x using Projectivization.ind
    simp [map_mk]
  right_inv x := by
    induction x using Projectivization.ind
    simp [map_mk]

@[simp]
theorem mapEquiv_refl : mapEquiv (LinearEquiv.refl K V) = Equiv.refl (ℙ K V) := by
  ext ⟨v⟩
  rfl

@[simp]
theorem mapEquiv_symm (f : V ≃ₛₗ[σ] W) : (mapEquiv f).symm = mapEquiv f.symm :=
  rfl

@[simp]
theorem mapEquiv_trans
    {K₁ V₁ : Type*} [Field K₁] [AddCommGroup V₁] [Module K₁ V₁]
    {K₂ V₂ : Type*} [Field K₂] [AddCommGroup V₂] [Module K₂ V₂]
    {K₃ V₃ : Type*} [Field K₃] [AddCommGroup V₃] [Module K₃ V₃]
    {σ₁₂ : K₁ →+* K₂} {σ₂₃ : K₂ →+* K₃} {σ₁₃ : K₁ →+* K₃}
    {σ₂₁ : K₂ →+* K₁} {σ₃₂ : K₃ →+* K₂} {σ₃₁ : K₃ →+* K₁}
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
    {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₃ : RingHomInvPair σ₂₃ σ₃₂}
    [RingHomInvPair σ₁₃ σ₃₁] {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
    {re₃₂ : RingHomInvPair σ₃₂ σ₂₃} [RingHomInvPair σ₃₁ σ₁₃]
    (e₁₂ : V₁ ≃ₛₗ[σ₁₂] V₂) (e₂₃ : V₂ ≃ₛₗ[σ₂₃] V₃) :
    mapEquiv (e₁₂.trans e₂₃) = (mapEquiv e₁₂).trans (mapEquiv e₂₃) := by
  ext ⟨v⟩
  rfl

end Projectivization

section

namespace InnerProductSpace.Core
variable {𝕜 F : Type*} [IsROrC 𝕜] [AddCommGroup F] [Module 𝕜 F] [Core 𝕜 F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 F _ x y

attribute [local instance] toInner'
attribute [local instance] toNorm

theorem inner_self_eq_norm_mul_norm' (x : F) : ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  apply IsROrC.ext
  · simp [inner_self_eq_norm_mul_norm]
  · simp [inner_self_im]

theorem inner_self_eq_norm_sq' (x : F) : ⟪x, x⟫ = ‖x‖ ^ 2 := by
  rw [pow_two, inner_self_eq_norm_mul_norm']

end InnerProductSpace.Core

section
variable {𝕜 E : Type*} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

theorem inner_self_eq_norm_mul_norm' (x : E) : ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  apply IsROrC.ext
  · simp [inner_self_eq_norm_mul_norm]
  · simp [inner_self_im]

theorem inner_self_eq_norm_sq' (x : E) : ⟪x, x⟫ = ‖x‖ ^ 2 := by
  rw [pow_two, inner_self_eq_norm_mul_norm']

end

namespace IsROrC
variable {𝕜 : Type*} [IsROrC 𝕜]
open scoped ComplexConjugate

@[coe]
def toComplex (z : 𝕜) : ℂ := ⟨re z, im z⟩

instance : Coe 𝕜 ℂ := ⟨toComplex⟩

@[simp, norm_cast]
lemma toComplex_eq_self (z : ℂ) : toComplex z = z := rfl

@[simp, norm_cast]
lemma toComplex_re (z : 𝕜) : (z : ℂ).re = re z := rfl

@[simp, norm_cast]
lemma toComplex_im (z : 𝕜) : (z : ℂ).im = im z := rfl

@[simp, norm_cast]
lemma toComplex_one : ↑(1 : 𝕜) = (1 : ℂ) := by ext <;> simp

@[simp, norm_cast]
lemma toComplex_zero : ↑(0 : 𝕜) = (0 : ℂ) := by ext <;> simp

@[simp, norm_cast]
lemma toComplex_mul (z w : 𝕜) : ↑(z * w) = (z * w : ℂ) := by ext <;> simp

@[simp, norm_cast]
lemma toComplex_add (z w : 𝕜) : ↑(z + w) = (z + w : ℂ) := by ext <;> simp

@[simp]
lemma normSq_toComplex (z : 𝕜) : Complex.normSq (z : ℂ) = normSq z := by simp [Complex.normSq, normSq]

@[simp, norm_cast]
lemma toComplex_inv (z : 𝕜) : ↑(z⁻¹) = (z : ℂ)⁻¹ := by ext <;> simp

@[simp, norm_cast]
lemma abs_toComplex (z : 𝕜) : Complex.abs (z : ℂ) = ‖z‖ := by
  rw [← pow_left_inj (map_nonneg _ _) (norm_nonneg _) zero_lt_two,
    Complex.sq_abs, Complex.normSq_apply, norm_sq_eq_def]
  rfl

instance : SMul 𝕜 ℂ where
  smul x z := x * z

lemma smul_def (x : 𝕜) (z : ℂ) : x • z = x * z := rfl

instance IsROrC.normedSpaceComplex : NormedSpace 𝕜 ℂ where
  smul x z := x * z
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]
  smul_zero := by simp [smul_def]
  smul_add := by simp [smul_def, mul_add]
  add_smul := by simp [smul_def, add_mul]
  zero_smul := by simp [smul_def]
  norm_smul_le := by simp [smul_def]

example : IsROrC.normedSpaceComplex = IsROrC.innerProductSpace.toNormedSpace := rfl
example : IsROrC.normedSpaceComplex = IsROrC.innerProductSpace.toNormedSpace.complexToReal := rfl

end IsROrC

noncomputable section

namespace EuclidGeom

open Real

structure Vec where
  fst : ℝ
  snd : ℝ

-- instance : NormedAddCommGroup Vec := inferInstanceAs <| NormedAddCommGroup (WithLp 2 (ℝ × ℝ))
-- instance : InnerProductSpace ℝ Vec := inferInstanceAs <| InnerProductSpace ℝ (WithLp 2 (ℝ × ℝ))

namespace Vec

def equivWithLp : Vec ≃ WithLp 2 (ℝ × ℝ) :=
  ⟨fun ⟨x, y⟩ ↦ ⟨x, y⟩, fun ⟨x, y⟩ ↦ ⟨x, y⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance nontrivial : Nontrivial Vec := equivWithLp.nontrivial

instance addCommGrop : AddCommGroup Vec := equivWithLp.addCommGroup

-- cannot be a instace because this will create a diamond
/-
instance moduleReal : Module ℝ Vec := equivWithLp.module ℝ

example : moduleReal = Module.complexToReal Vec := rfl
-/

instance normedAddCommGroup : NormedAddCommGroup Vec where
  norm v := ‖equivWithLp v‖
  dist v₁ v₂ := dist (equivWithLp v₁) (equivWithLp v₂)
  dist_self _ := dist_self (equivWithLp _)
  dist_comm _ _ := dist_comm (equivWithLp _) (equivWithLp _)
  dist_triangle _ _ _ := dist_triangle (equivWithLp _) (equivWithLp _) (equivWithLp _)
  edist v₁ v₂ := edist (equivWithLp v₁) (equivWithLp v₂)
  edist_dist _ _ := edist_dist (equivWithLp _) (equivWithLp _)
  eq_of_dist_eq_zero := by simp
  dist_eq _ _ := dist_eq_norm (equivWithLp _) (equivWithLp _)

theorem norm_def (v : Vec) :
    ‖v‖ = sqrt (v.fst * v.fst + v.snd * v.snd) :=
  norm_eq_sqrt_inner (𝕜 := ℝ) (equivWithLp v)

theorem norm_sq (v : Vec) :
    ‖v‖ ^ 2 = v.fst * v.fst + v.snd * v.snd :=
  norm_sq_eq_inner (𝕜 := ℝ) (equivWithLp v)

-- cannot be a instace because this will create a diamond
/-
instance normedAddCommGroupReal : InnerProductSpace ℝ Vec where
  norm_smul_le x v := norm_smul_le x (equivWithLp v)
  inner v₁ v₂ := ⟪equivWithLp v₁, equivWithLp v₂⟫_ℝ
  norm_sq_eq_inner _ := norm_sq_eq_inner (equivWithLp _)
  conj_symm _ _ := inner_conj_symm (equivWithLp _) (equivWithLp _)
  add_left _ _ _ := inner_add_left (equivWithLp _) (equivWithLp _) (equivWithLp _)
  smul_left _ _ _ := inner_smul_left (equivWithLp _) (equivWithLp _) _
-/
attribute [pp_dot] fst snd

lemma ext {v₁ v₂ : Vec} (h₁ : v₁.fst = v₂.fst) (h₂ : v₁.snd = v₂.snd) : v₁ = v₂ := by
  cases v₁
  cases v₂
  dsimp at *
  simp [*]

lemma mk_fst {x y : ℝ} : (mk x y).fst = x :=
  rfl

lemma mk_snd {x y : ℝ} : (mk x y).snd = y :=
  rfl

@[simp]
lemma mk_zero_zero : (⟨0, 0⟩ : Vec) = 0 :=
  rfl

@[simp]
lemma zero_fst : (0 : Vec).fst = 0 :=
  rfl

@[simp]
lemma zero_snd : (0 : Vec).snd = 0 :=
  rfl

@[simp]
lemma mk_add_mk (x₁ x₂ y₁ y₂ : ℝ) : mk x₁ y₁ + mk x₂ y₂ = mk (x₁ + x₂) (y₁ + y₂) := rfl

@[simp]
lemma add_fst (v₁ v₂ : Vec) : (v₁ + v₂).fst = v₁.fst + v₂.fst :=
  rfl

@[simp]
lemma add_snd (v₁ v₂ : Vec) : (v₁ + v₂).snd = v₁.snd + v₂.snd :=
  rfl

@[simp]
lemma neg_mk (x y : ℝ) : -mk x y = mk (-x) (-y) := rfl

@[simp]
lemma neg_fst (v : Vec) : (-v).fst = -v.fst :=
  rfl

@[simp]
lemma neg_snd (v : Vec) : (-v).snd = -v.snd :=
  rfl

open IsROrC in
instance normedSpace {𝕜 : Type*} [IsROrC 𝕜] : NormedSpace 𝕜 Vec where
  smul z v := ⟨re z * v.fst - im z * v.snd, re z * v.snd + im z * v.fst⟩
  one_smul v := by simp [(· • ·)]
  mul_smul z w v := by dsimp [(· • ·)]; rw [mul_re, mul_im]; ring_nf
  smul_zero z := by simp [(· • ·)]
  smul_add z v₁ v₂ := by dsimp [(· • ·)]; apply ext <;> ring
  add_smul z w v := by dsimp [(· • ·)]; rw [map_add, map_add]; ring_nf
  zero_smul v := by simp [(· • ·)]
  norm_smul_le z v := le_of_eq <| (sq_eq_sq (norm_nonneg _) (by positivity)).mp <| by
    simp only [(· • ·), mul_pow, norm_sq, norm_sq_eq_def]
    ring

example : normedSpace = normedSpace.complexToReal := rfl

lemma complex_smul_def (s : ℂ) (v : Vec) : s • v = mk (s.re * v.fst - s.im * v.snd) (s.re * v.snd + s.im * v.fst) :=
  rfl

@[simp]
lemma complex_smul_mk (s : ℂ) (x y : ℝ) : s • mk x y = mk (s.re * x - s.im * y) (s.re * y + s.im * x) :=
  rfl

@[simp]
lemma complex_smul_fst (s : ℂ) (v : Vec) : (s • v).fst = s.re * v.fst - s.im * v.snd :=
  rfl

@[simp]
lemma complex_smul_snd (s : ℂ) (v : Vec) : (s • v).snd = s.re * v.snd + s.im * v.fst :=
  rfl

lemma smul_def' (s : ℝ) (v : Vec) : s • v = mk (s * v.fst - 0 * v.snd) (s * v.snd + 0 * v.fst) :=
  rfl

@[simp default - 1, nolint simpNF]
lemma smul_mk' (s : ℝ) (x y : ℝ) : s • mk x y = mk (s * x - 0 * y) (s * y + 0 * x) :=
  rfl

@[simp default - 1, nolint simpNF]
lemma smul_fst' (s : ℝ) (v : Vec) : (s • v).fst = s * v.fst - 0 * v.snd :=
  rfl

@[simp default - 1, nolint simpNF]
lemma smul_snd' (s : ℝ) (v : Vec) : (s • v).snd = s * v.snd + 0 * v.fst := by
  rfl

lemma smul_def (s : ℝ) (v : Vec) : s • v = mk (s * v.fst) (s * v.snd) := by
  dsimp [smul_def', complex_smul_def]; simp

@[simp]
lemma smul_mk (s : ℝ) (x y : ℝ) : s • mk x y = mk (s * x) (s * y) := by
  dsimp; simp

@[simp]
lemma smul_fst (s : ℝ) (v : Vec) : (s • v).fst = s * v.fst := by
  dsimp; simp

@[simp]
lemma smul_snd (s : ℝ) (v : Vec) : (s • v).snd = s * v.snd := by
  dsimp; simp

def det : Vec →ₗ[ℝ] Vec →ₗ[ℝ] ℝ where
  toFun v₁ := {
    toFun := fun v₂ ↦ v₁.fst * v₂.snd - v₁.snd * v₂.fst
    map_add' := fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ↦ by dsimp; ring
    map_smul' := fun a ⟨x₂, y₂⟩ ↦ by dsimp; ring }
  map_add' := fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ↦ by ext; dsimp; ring
  map_smul' := fun a ⟨x₂, y₂⟩ ↦ by ext; dsimp; ring

lemma det_apply (v₁ v₂ : Vec) :
    det v₁ v₂ = v₁.fst * v₂.snd - v₁.snd * v₂.fst :=
  rfl

@[simp]
lemma det_self (v : Vec) : det v v = 0 := by
  dsimp [det_apply]
  ring

lemma det_skew (v₁ v₂ : Vec) : -det v₁ v₂ = det v₂ v₁ := by
  dsimp [det_apply]
  ring

instance innerProductSpace' : InnerProductSpace ℝ Vec where
  inner v₁ v₂ := v₁.fst * v₂.fst + v₁.snd * v₂.snd
  norm_sq_eq_inner v := by simp [norm_sq]
  conj_symm v₁ v₂ := by simp [Complex.conj_ofReal, mul_comm]
  add_left v₁ v₂ v₃ := by dsimp; ring
  smul_left v₁ v₂ z := by dsimp; ring

lemma real_inner_apply (v₁ v₂ : Vec) :
    ⟪v₁, v₂⟫_ℝ = v₁.fst * v₂.fst + v₁.snd * v₂.snd :=
  rfl

instance innerProductSpace : InnerProductSpace ℂ Vec where
  inner v₁ v₂ := ⟨⟪v₁, v₂⟫_ℝ, det v₁ v₂⟩
  norm_sq_eq_inner v := by simp [norm_sq]; rfl
  conj_symm v₁ v₂ := by
    ext
    · simp [real_inner_comm]
    · simp [det_skew]
  add_left v₁ v₂ v₃ := by
    ext
    · simp [inner_add_left]
    · simp
  smul_left v₁ v₂ z := by
    ext <;>
    · dsimp [inner, det]
      ring

example : innerProductSpace' = InnerProductSpace.complexToReal := rfl

@[simp]
lemma inner_re (v₁ v₂ : Vec) :
    ⟪v₁, v₂⟫_ℂ.re = ⟪v₁, v₂⟫_ℝ :=
  rfl

@[simp]
lemma inner_im (v₁ v₂ : Vec) :
    ⟪v₁, v₂⟫_ℂ.im = det v₁ v₂ :=
  rfl

lemma complex_inner_apply' (v₁ v₂ : Vec) :
    ⟪v₁, v₂⟫_ℂ = ⟨⟪v₁, v₂⟫_ℝ, det v₁ v₂⟩ :=
  rfl

lemma complex_inner_apply (v₁ v₂ : Vec) :
    ⟪v₁, v₂⟫_ℂ = ⟪v₁, v₂⟫_ℝ + det v₁ v₂ * Complex.I := by
  simp [complex_inner_apply', Complex.mk_eq_add_mul_I]

lemma smul_inner (v₁ v₂ : Vec) : ⟪v₁, v₂⟫_ℂ • v₁ = ‖v₁‖ ^ 2 • v₂ := by
  simp only [complex_inner_apply', real_inner_apply, det_apply, complex_smul_def,
    norm_sq, smul_def]
  apply ext <;> ring

def scaleRotate : ℂ →+* (Vec →ₗ[ℂ] Vec) :=
  Module.toModuleEnd ℂ Vec

@[simp]
lemma scaleRotate_apply (z : ℂ) (v : Vec) :
    scaleRotate z v = z • v :=
  rfl

def scaleRotateEquiv : ℂˣ →* Vec ≃ₗ[ℂ] Vec where
  toFun z := {
    toLinearMap := scaleRotate z
    invFun := fun v ↦ z.inv • v
    left_inv := fun v ↦ by simp [scaleRotate]
    right_inv := fun v ↦ by simp [scaleRotate] }
  map_one' := by
    ext v
    simpa using LinearMap.one_apply v
  map_mul' z w := by
    ext v
    simpa using LinearMap.mul_apply _ _ v

@[simp]
lemma scaleRotateEquiv_mk0 (z : ℂ) (hz : z ≠ 0) :
    (scaleRotateEquiv (.mk0 z hz) : Vec → Vec) = (scaleRotate z : Vec → Vec) :=
  rfl

lemma smul_bijective {z : ℂ} (hz : z ≠ 0) : Function.Bijective (z • · : Vec → Vec) :=
  (scaleRotateEquiv (.mk0 z hz)).bijective

def rotate (θ : AngValue) : Vec ≃ₗ[ℂ] Vec :=
  scaleRotateEquiv (circle.toUnits θ.expMapCircle)

@[simp]
lemma rotate_mk (θ : AngValue) (x y : ℝ) :
    rotate θ ⟨x, y⟩ = ⟨θ.cos * x - θ.sin * y, θ.cos * y + θ.sin * x⟩ := by
  dsimp [rotate]; simp [AngValue.coe_expMapCircle]

@[simp]
lemma rotate_fst (θ : AngValue) (v : Vec) :
    (rotate θ v).fst = θ.cos * v.fst - θ.sin * v.snd := by
  cases v; simp

@[simp]
lemma rotate_snd (θ : AngValue) (v : Vec) :
    (rotate θ v).snd = θ.cos * v.snd + θ.sin * v.fst := by
  cases v; simp

lemma smul_eq_rotate (z : ℂ) (v : Vec) :
    z • v = ‖z‖ • Vec.rotate z.arg v := by
  apply ext
  · simp [mul_sub, ← mul_assoc]
  · simp [mul_add, ← mul_assoc]

@[simp]
lemma expMapCircle_smul_eq_rotate (θ : AngValue) (v : Vec) :
    θ.expMapCircle • v = Vec.rotate θ v := by
  simp [circle.smul_def, smul_eq_rotate]

section -- these lemma should be in mathlib

@[simp]
lemma _root_.LinearEquiv.one_apply {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (x : M) :
    (1 : M ≃ₗ[R] M) x = x :=
  rfl

-- this lemma should be in mathlib
@[simp]
lemma _root_.LinearEquiv.mul_apply {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (f g : M ≃ₗ[R] M) (x : M) :
    (f * g) x = f (g x) :=
  rfl

end

@[simp]
lemma rotate_zero : Vec.rotate 0 = 1 := by
  ext ⟨x, y⟩
  simp

lemma rotate_zero_apply (v : Vec) : Vec.rotate 0 v = v := by
  simp

@[simp]
lemma rotate_pi : Vec.rotate π = .neg ℂ := by
  ext ⟨x, y⟩
  simp

lemma rotate_pi_apply (v : Vec) : Vec.rotate π v = -v := by
  simp

@[simp]
lemma rotate_add (θ ψ : AngValue) :
    Vec.rotate (θ + ψ) = Vec.rotate θ * Vec.rotate ψ := by
  ext ⟨x, y⟩
  simp only [rotate_mk, LinearEquiv.mul_apply, AngValue.cos_add, AngValue.sin_add]
  apply ext <;> ring

lemma rotate_add_apply (θ ψ : AngValue) (v : Vec) :
    Vec.rotate (θ + ψ) v = Vec.rotate θ (Vec.rotate ψ v) := by
  simp

@[simp]
lemma norm_rotate (θ : AngValue) (v : Vec) : ‖Vec.rotate θ v‖ = ‖v‖ := by
  rw [norm_def, norm_def]
  obtain ⟨x, y⟩ := v
  simp only [rotate_mk]
  ring_nf
  rw [add_right_comm (_ * _), add_assoc, mul_comm (x ^ _), ← add_mul, ← add_mul, AngValue.cos_sq_add_sin_sq, one_mul, one_mul]

lemma rotate_eq_zero {θ : AngValue} {v : Vec} : Vec.rotate θ v = 0 ↔ v = 0 := by
  simp

lemma rotate_ne_zero {θ : AngValue} {v : Vec} : Vec.rotate θ v ≠ 0 ↔ v ≠ 0 := by
  simp

instance : HDiv Vec Vec ℂ := ⟨fun v₁ v₂ ↦ ⟪v₂, v₁⟫_ℂ / ‖v₂‖ ^ 2⟩

lemma cdiv_def (v₁ v₂ : Vec) : v₁ / v₂ = ⟪v₂, v₁⟫_ℂ / (‖v₂‖ ^ 2 : ℂ) := rfl

lemma add_cdiv (v₁ v₁' v₂ : Vec) : (v₁ + v₁') / v₂ = v₁ / v₂ + v₁' / v₂ := by
  simp_rw [cdiv_def, inner_add_right, add_div]

lemma neg_cdiv (v₁ v₂ : Vec) : -v₁ / v₂ = -(v₁ / v₂) := by
  simp_rw [cdiv_def, inner_neg_right, neg_div]

lemma cdiv_neg (v₁ v₂ : Vec) : v₁ / -v₂ = -(v₁ / v₂) := by
  simp_rw [cdiv_def, inner_neg_left, neg_div, norm_neg]

lemma sub_cdiv (v₁ v₁' v₂ : Vec) : (v₁ - v₁') / v₂ = v₁ / v₂ - v₁' / v₂ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_cdiv, neg_cdiv]

lemma complex_smul_cdiv (z : ℂ) (v₁ v₂ : Vec) : z • v₁ / v₂ = z * (v₁ / v₂) := by
  simp_rw [cdiv_def, inner_smul_right, mul_div]

lemma mul_cdiv (z : ℂ) (v₁ v₂ : Vec) : z * (v₁ / v₂) = z • v₁ / v₂ :=
  (complex_smul_cdiv z v₁ v₂).symm

lemma smul_cdiv {𝕜 : Type*} [IsROrC 𝕜] (z : 𝕜) (v₁ v₂ : Vec) : z • v₁ / v₂ = z • (v₁ / v₂) :=
  complex_smul_cdiv z v₁ v₂

@[simp]
lemma cdiv_smul_cancel (v₁ : Vec) {v₂ : Vec} (hv₂ : v₂ ≠ 0) : (v₁ / v₂) • v₂ = v₁ := by
  rw [cdiv_def, div_eq_inv_mul, mul_smul, smul_inner]
  norm_cast
  rw [smul_smul, inv_mul_cancel (by simpa), one_smul]

@[simp]
lemma complex_smul_cdiv_cancel (z : ℂ) {v : Vec} (hv : v ≠ 0) : z • v / v = z := by
  rw [cdiv_def, inner_smul_right, inner_self_eq_norm_sq']
  exact mul_div_cancel _ (by simpa)

lemma inner_left_bijective {v : Vec} (h : v ≠ 0) : Function.Bijective (⟪v, ·⟫_ℂ) :=
  Equiv.bijective ⟨(⟪v, ·⟫_ℂ), fun z ↦ (z / ‖v‖ ^ 2) • v,
    fun v₂ ↦ by simp [← cdiv_def, h], fun z ↦ by
      simp only [inner_smul_right, inner_self_eq_norm_sq']
      exact div_mul_cancel _ (by simpa)⟩

lemma inner_right_bijective {v : Vec} (h : v ≠ 0) : Function.Bijective (⟪·, v⟫_ℂ) := by
  simpa [Function.comp_def] using (EquivLike.bijective starRingAut).comp (inner_left_bijective h)

@[simp]
theorem complex_inner_eq_zero_iff {v₁ v₂ : Vec} : ⟪v₁, v₂⟫_ℂ = 0 ↔ v₁ = 0 ∨ v₂ = 0 := by
  constructor
  · contrapose!
    rintro ⟨h₁, h₂⟩
    change sesqFormOfInner v₂ v₁ ≠ 0
    rwa [map_ne_zero_iff]
    exact (inner_right_bijective h₂).injective
  · rintro (h | h) <;> simp [h]

theorem complex_inner_ne_zero_iff {v₁ v₂ : Vec} : ⟪v₁, v₂⟫_ℂ ≠ 0 ↔ v₁ ≠ 0 ∧ v₂ ≠ 0 :=
  complex_inner_eq_zero_iff.not.trans not_or

@[simp]
theorem cdiv_eq_zero {v₁ v₂ : Vec} : v₁ / v₂ = (0 : ℂ) ↔ v₁ = 0 ∨ v₂ = 0 := by
  rw [cdiv_def, div_eq_zero_iff, pow_eq_zero_iff zero_lt_two, Complex.ofReal_eq_zero,
    norm_eq_zero, complex_inner_eq_zero_iff]
  tauto

@[simp]
theorem cdiv_zero (v : Vec) : v / (0 : Vec) = (0 : ℂ) := by
  simp

@[simp]
theorem zero_cdiv (v : Vec) : (0 : Vec) / v = (0 : ℂ) := by
  simp

theorem cdiv_ne_zero {v₁ v₂ : Vec} : v₁ / v₂ ≠ 0 ↔ v₁ ≠ 0 ∧ v₂ ≠ 0 :=
  cdiv_eq_zero.not.trans not_or

lemma cdiv_left_inj {v₁ v₂ v₃ : Vec} (hv₃ : v₃ ≠ 0) : v₁ / v₃ = v₂ / v₃ ↔ v₁ = v₂ := by
  rw [← sub_eq_zero, ← sub_cdiv, cdiv_eq_zero, sub_eq_zero, or_iff_left hv₃]

lemma cdiv_eq_iff {v₁ v₂ : Vec} {z : ℂ} (hv₂ : v₂ ≠ 0) : v₁ / v₂ = z ↔ v₁ = z • v₂ := by
  rw [← complex_smul_cdiv_cancel z hv₂, cdiv_left_inj hv₂, complex_smul_cdiv_cancel z hv₂]

lemma eq_cdiv_iff {v₁ v₂ : Vec} {z : ℂ} (hv₂ : v₂ ≠ 0) : z = v₁ / v₂ ↔ z • v₂ = v₁ := by
  rw [eq_comm, cdiv_eq_iff hv₂, eq_comm]

lemma cdiv_eq_one_iff_eq {v₁ v₂ : Vec} (hv₂ : v₂ ≠ 0) : v₁ / v₂ = (1 : ℂ) ↔ v₁ = v₂ := by
  rw [cdiv_eq_iff hv₂, one_smul]

@[simp]
lemma cdiv_self {v : Vec} (hv : v ≠ 0) : v / v = (1 : ℂ) := by
  rw [cdiv_eq_one_iff_eq hv]

@[simp]
lemma smul_cdiv_cancel {𝕜 : Type*} [IsROrC 𝕜] (z : 𝕜) {v : Vec} (hv : v ≠ 0) : z • v / v = (z : ℂ) := by
  rw [smul_cdiv, cdiv_self hv, IsROrC.smul_def, mul_one]

-- note: why simp do not know to use `smul_cdiv_cancel`?
@[simp]
lemma real_smul_cdiv_cancel (z : ℝ) {v : Vec} (hv : v ≠ 0) : z • v / v = (z : ℂ) :=
  smul_cdiv_cancel z hv

lemma inv_cdiv (v₁ v₂ : Vec) : (v₁ / v₂)⁻¹ = v₂ / v₁ := by
  by_cases hv₁ : v₁ = 0; · simp [hv₁]
  by_cases hv₂ : v₂ = 0; · simp [hv₂]
  apply inv_eq_of_mul_eq_one_left
  rw [mul_cdiv, cdiv_smul_cancel _ hv₁, cdiv_self hv₂]

lemma cdiv_complex_smul (z : ℂ) (v₁ v₂ : Vec) : v₁ / z • v₂ = z⁻¹ * (v₁ / v₂) := by
  rw [← inv_cdiv v₂, ← mul_inv, mul_cdiv, inv_cdiv]

@[simp]
lemma cdiv_smul {𝕜 : Type*} [IsROrC 𝕜] (z : 𝕜) (v₁ v₂ : Vec) : v₁ / z • v₂ = z⁻¹ • (v₁ / v₂) := by
  convert cdiv_complex_smul z v₁ v₂ using 0
  norm_cast

lemma inner_smul_comm_right (v₁ v₂ v₃ : Vec) : ⟪v₁, v₂⟫_ℂ • v₃ = ⟪v₁, v₃⟫_ℂ • v₂ := by
  apply Vec.ext
  · dsimp [inner, det]
    ring
  · dsimp [inner, det]
    ring

lemma cdiv_smul_comm (v₁ v₂ v₃ : Vec) : (v₁ / v₂) • v₃ = (v₃ / v₂) • v₁ := by
  simp_rw [cdiv_def, div_eq_inv_mul, mul_smul]
  congr 1
  exact inner_smul_comm_right _ _ _

lemma cdiv_eq_cdiv_iff_cdiv_eq_cdiv {v₁ v₂ v₃ v₄ : Vec} (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0) : v₁ / v₂ = v₃ / v₄ ↔ v₁ / v₃ = v₂ / v₄ := by
  rw [cdiv_eq_iff hv₂, cdiv_smul_comm, ← cdiv_eq_iff hv₃]

@[simp]
lemma abs_inner (v₁ v₂ : Vec) : Complex.abs ⟪v₁, v₂⟫_ℂ = ‖v₁‖ * ‖v₂‖ := by
  rw [← pow_left_inj (by simp) (by positivity) zero_lt_two]
  rw [Complex.abs_apply, sq_sqrt (Complex.normSq_nonneg _)]
  dsimp [inner, det]
  rw [mul_pow, norm_sq, norm_sq]
  ring

@[simp]
lemma abs_cdiv (v₁ v₂ : Vec) : Complex.abs (v₁ / v₂) = ‖v₁‖ / ‖v₂‖ := by
  by_cases hv₂ : v₂ = 0; · simp [hv₂]
  rw [cdiv_def, map_div₀, abs_inner, map_pow, Complex.abs_ofReal, abs_norm]
  rw [pow_two, mul_div_mul_left _ _ (norm_ne_zero_iff.mpr hv₂)]

-- should be in mathlib
theorem _root_.IsROrC.ofReal_eq_complex_coe : IsROrC.ofReal = ((↑) : ℝ → ℂ) :=
  rfl

lemma real_inner_of_sameRay {v₁ v₂ : Vec} (h : SameRay ℝ v₁ v₂) :
    ⟪v₁, v₂⟫_ℝ = ‖v₁‖ * ‖v₂‖ := by
  obtain (rfl | rfl | ⟨r₁, r₂, hr₁, hr₂, h⟩) := h
  · simp
  · simp
  · rw [← inv_smul_eq_iff₀ hr₂.ne'] at h
    subst h
    rw [inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, norm_smul]
    rw [norm_inv, norm_eq_abs, norm_eq_abs, abs_eq_self.mpr hr₁.le, abs_eq_self.mpr hr₂.le]
    ring

lemma det_of_sameRay {v₁ v₂ : Vec} (h : SameRay ℝ v₁ v₂) :
    det v₁ v₂ = 0 := by
  obtain (rfl | rfl | ⟨r₁, r₂, _, hr₂, h⟩) := h
  · simp
  · simp
  · rw [← inv_smul_eq_iff₀ hr₂.ne'] at h
    subst h
    rw [map_smul, map_smul, det_self, smul_zero, smul_zero]

lemma complex_inner_of_sameRay {v₁ v₂ : Vec} (h : SameRay ℝ v₁ v₂) :
    ⟪v₁, v₂⟫_ℂ = ‖v₁‖ * ‖v₂‖ := by
  ext
  · simp [real_inner_of_sameRay h]
  · simp [det_of_sameRay h]

lemma cdiv_of_sameRay {v₁ v₂ : Vec} (h : SameRay ℝ v₁ v₂) :
    v₁ / v₂ = ‖v₁‖ / ‖v₂‖ := by
  by_cases hv₂ : v₂ = 0; · simp [hv₂]
  rw [cdiv_def, complex_inner_of_sameRay h.symm]
  norm_cast
  rw [pow_two, mul_div_mul_left _ _ (norm_ne_zero_iff.mpr hv₂)]

@[simp]
lemma arg_cdiv (θ : AngValue) {v : Vec} (hv : v ≠ 0) :
    (Vec.rotate θ v / v).arg = θ := by
  rw [← expMapCircle_smul_eq_rotate, circle.smul_def, smul_cdiv]
  simp [hv]

end Vec

/-- the class of non-degenerate vectors -/
abbrev VecND : Type := RayVector ℝ Vec

abbrev VecND.mk (v : Vec) (hv : v ≠ 0) : VecND := ⟨v, hv⟩

namespace VecND

instance : CoeOut VecND Vec := subtypeCoe

instance : Neg VecND where
  neg v := ⟨-v, neg_ne_zero.mpr v.2⟩

@[simp]
theorem ne_zero (x : VecND) : (x : Vec) ≠ 0 := x.2

@[simp, norm_cast]
lemma coe_neg (v : VecND) : (-v : VecND) = -(v : Vec) := rfl

instance : Norm VecND where
  norm v := ‖(v : Vec)‖

@[simp, norm_cast]
lemma norm_coe (v : VecND) :
    ‖(v : Vec)‖ = ‖v‖ :=
  rfl

@[simp]
lemma norm_pos (v : VecND) : 0 < ‖v‖ := norm_pos_iff.2 v.2

open Lean Meta Qq Function Mathlib.Meta.Positivity in
/-- Extension for the `positivity` tactic. -/
@[positivity Norm.norm _]
def evalVecNDNorm :
    PositivityExt where eval {_ _} _zα _pα e := do
  let .app _ a ← whnfR e | throwError "not ‖ · ‖"
  let p ← mkAppM ``EuclidGeom.VecND.norm_pos #[a]
  pure (.positive p)

example (v : VecND) : 0 < ‖v‖ := by positivity

@[simp]
lemma norm_ne_zero (v : VecND) : ‖v‖ ≠ 0 := v.norm_pos.ne'

@[simp]
lemma norm_neg (v : VecND) : ‖-v‖ = ‖v‖ := by
  rw [← norm_coe, ← norm_coe, coe_neg]
  exact _root_.norm_neg _

@[ext]
theorem ext {v₁ v₂ : VecND} : (v₁ : Vec) = (v₂ : Vec) → v₁ = v₂ :=
  Subtype.ext

@[norm_cast]
theorem coe_inj {v₁ v₂ : VecND} : (v₁ : Vec) = (v₂ : Vec) ↔ v₁ = v₂ :=
  Subtype.coe_inj

@[simp, norm_cast]
lemma coe_smul {G : Type*} [Group G] [DistribMulAction G Vec]
    (g : G) (v : VecND) :
    ↑(g • v) = g • (v : Vec) :=
  rfl

@[simp, norm_cast]
lemma coe_vadd {G : Type*} [Group G] [DistribMulAction G Vec]
    (g : Additive G) (v : VecND) :
    ↑(g +ᵥ v) = (Additive.toMul g) • (v : Vec) :=
  rfl

lemma smul_def {G : Type*} [Group G] [DistribMulAction G Vec]
    (g : G) (v : VecND) :
    g • v = ⟨g • (v : Vec), (smul_ne_zero_iff_ne _).mpr v.2⟩ :=
  rfl

lemma vadd_def {G : Type*} [Group G] [DistribMulAction G Vec]
    (g : Additive G) (v : VecND) :
    g +ᵥ v = ⟨(Additive.toMul g) • (v : Vec), (smul_ne_zero_iff_ne _).mpr v.2⟩ :=
  rfl

lemma mk_neg (v : Vec) (hv : v ≠ 0) :
    (⟨-v, neg_ne_zero.mpr hv⟩ : VecND) = (-⟨v, hv⟩ : VecND) :=
  rfl

@[simp]
lemma mk_neg' (v : Vec) (hv : -v ≠ 0) :
    (⟨-v, hv⟩ : VecND) = (-⟨v, neg_ne_zero.mp hv⟩ : VecND) :=
  rfl

lemma mk_smul {G : Type*} [Group G] [DistribMulAction G Vec]
    (g : G) (v : Vec) (hv : v ≠ 0) :
    (⟨g • v, (smul_ne_zero_iff_ne _).mpr hv⟩ : VecND) = (g • ⟨v, hv⟩ : VecND) :=
  rfl

@[simp]
lemma mk_smul' {G : Type*} [Group G] [DistribMulAction G Vec]
    (g : G) (v : Vec) (hv : g • v ≠ 0) :
    (⟨g • v, hv⟩ : VecND) = (g • ⟨v, (smul_ne_zero_iff_ne _).mp hv⟩ : VecND) :=
  rfl

lemma mk_vadd {G : Type*} [Group G] [DistribMulAction G Vec]
    (g : Additive G) (v : Vec) (hv : v ≠ 0) :
    (⟨g +ᵥ v, (smul_ne_zero_iff_ne _).mpr hv⟩ : VecND) = (g +ᵥ ⟨v, hv⟩ : VecND) :=
  rfl

@[simp]
lemma mk_vadd' {G : Type*} [Group G] [DistribMulAction G Vec]
    (g : Additive G) (v : Vec) (hv : g +ᵥ v ≠ 0) :
    (⟨g +ᵥ v, hv⟩ : VecND) = (g +ᵥ ⟨v, (smul_ne_zero_iff_ne _).mp hv⟩ : VecND) :=
  rfl

-- should be `[GroupWithZero G] [DistribMulActionWithZero G Vec] [NoZeroSMulDivisors G Vec]`
-- but we don't have `DistribMulActionWithZero`
@[simp]
lemma mk_smul₀ {G : Type*} [DivisionSemiring G] [Module G Vec] [NoZeroSMulDivisors G Vec]
    (g : G) (v : Vec) (hv : g • v ≠ 0) :
    (⟨g • v, hv⟩ : VecND) = (Units.mk0 g (smul_ne_zero_iff.mp hv).1 • mk v (smul_ne_zero_iff.mp hv).2) := by
  ext
  simp

@[simp]
protected lemma neg_smul {R : Type*} [Ring R] [Module R Vec]
    (g : Rˣ) (v : VecND) :
    (-g) • v = -(g • v) := by
  ext
  simp

@[simp]
protected lemma smul_neg {R : Type*} [Ring R] [Module R Vec]
    (g : Rˣ) (v : VecND) :
    g • -v = -(g • v) := by
  ext
  simp

@[simp]
protected lemma norm_smul (r : ℝˣ) (v : VecND) :
    ‖r • v‖ = ‖(r : ℝ)‖ * ‖v‖ := by
  rw [← norm_coe, coe_smul, Units.smul_def, norm_smul, norm_coe]

instance : Nontrivial VecND := ⟨⟨⟨1, 0⟩, fun h ↦ by simpa using congr_arg Vec.fst h⟩,
  ⟨⟨2, 0⟩, fun h ↦ by simpa using congr_arg Vec.fst h⟩, fun h ↦ by simpa using congr_arg (·.1.fst) h⟩

instance : HDiv VecND VecND ℂˣ := ⟨fun v₁ v₂ ↦ .mk0 ((v₁ : Vec) / (v₂ : Vec)) (Vec.cdiv_ne_zero.mpr <| by simp)⟩

@[simp, norm_cast]
lemma coe_cdiv (v₁ v₂ : VecND) : (v₁ / v₂ : ℂ) = (v₁ : Vec) / (v₂ : Vec) := rfl

lemma smul_cdiv (z : ℂˣ) (v₁ v₂ : VecND) : z • v₁ / v₂ = z * (v₁ / v₂) := by
  ext1
  push_cast
  exact Vec.smul_cdiv _ _ _

@[simp]
lemma cdiv_smul_cancel (v₁ v₂ : VecND) : (v₁ / v₂) • v₂ = v₁ := by
  ext1
  simp [Units.smul_def]

@[simp]
lemma smul_cdiv_cancel (z : ℂˣ) (v : VecND) : z • v / v = z := by
  ext1
  simp [Units.smul_def]

instance : AddTorsor (Additive ℂˣ) VecND where
  zero_vadd v := by simp
  add_vadd z w v := by
    ext
    push_cast
    rw [toMul_add, mul_smul]
  vsub v₁ v₂ := Additive.ofMul <| v₁ / v₂
  vsub_vadd' v₁ v₂ := by simp
  vadd_vsub' z v := by
    apply Additive.toMul.injective
    ext1
    dsimp
    rw [← ofMul_toMul z, ofMul_vadd, Units.smul_def, Vec.smul_cdiv_cancel _ v.ne_zero]
    dsimp

lemma vsub_def (v₁ v₂ : VecND) : v₁ -ᵥ v₂ = Additive.ofMul (v₁ / v₂) :=
  rfl

lemma rotate_ne_zero (θ : AngValue) (v : VecND) : Vec.rotate θ v ≠ 0 := by simp

protected def map (e : Vec ≃ₗ[ℝ] Vec) : VecND ≃ VecND where
  toFun v := ⟨e v, e.map_ne_zero_iff.mpr v.2⟩
  invFun v := ⟨e.symm v, e.symm.map_ne_zero_iff.mpr v.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

def rotate (θ : AngValue) : VecND ≃ VecND :=
  VecND.map ((Vec.rotate θ).restrictScalars ℝ)

def angle (v₁ v₂ : VecND) : AngValue := Complex.arg ↑(Additive.toMul (v₂ -ᵥ v₁))

def SameDir (v₁ v₂ : VecND) : Prop := ∃ x : ℝ, 0 < x ∧ v₁ = x • (v₂ : Vec)

@[simp]
lemma sameRay_iff_sameDir {v₁ v₂ : VecND} : SameRay ℝ (v₁ : Vec) (v₂ : Vec) ↔ SameDir v₁ v₂ := by
  constructor
  · rintro (h₁ | h₂ | ⟨x₁, x₂, hx₁, hx₂, h⟩)
    · exact absurd h₁ v₁.ne_zero
    · exact absurd h₂ v₂.ne_zero
    · use x₂ / x₁, div_pos hx₂ hx₁
      rwa [div_eq_inv_mul, mul_smul, eq_comm, inv_smul_eq_iff₀ hx₁.ne', eq_comm]
  · rintro ⟨x, hx, h⟩
    exact .inr <| .inr <| ⟨1, x, zero_lt_one, hx, (one_smul _ _).trans h⟩

namespace SameDir

alias ⟨ofSameRay, toSameRay⟩ := sameRay_iff_sameDir

@[refl, simp]
lemma refl (v : VecND) : SameDir v v := sameRay_iff_sameDir.mp <| SameRay.refl _

lemma rfl {v : VecND} : SameDir v v := refl _

@[symm]
theorem symm {v₁ v₂ : VecND} (h : SameDir v₁ v₂) : SameDir v₂ v₁ :=
  ofSameRay h.toSameRay.symm

@[trans]
theorem trans {v₁ v₂ v₃ : VecND} (h₁ : SameDir v₁ v₂) (h₂ : SameDir v₂ v₃) : SameDir v₁ v₃ :=
  ofSameRay <| h₁.toSameRay.trans h₂.toSameRay (absurd · v₂.ne_zero)

end SameDir

@[simp]
theorem sameDir_neg_iff {v₁ v₂ : VecND} : SameDir (-v₁) (-v₂) ↔ SameDir v₁ v₂ :=
  (sameRay_iff_sameDir.symm.trans sameRay_neg_iff).trans sameRay_iff_sameDir

alias ⟨SameDir.of_neg, SameDir.neg⟩ := sameDir_neg_iff

theorem sameDir_neg_swap {v₁ v₂ : VecND} : SameDir (-v₁) v₂ ↔ SameDir v₁ (-v₂) := by
  rw [← sameDir_neg_iff, neg_neg]

@[simp]
theorem sameDir_smul_left_iff {v : VecND} {r : ℝˣ} :
    SameDir (r • v) v ↔ 0 < (r : ℝ) :=
  sameRay_iff_sameDir.symm.trans <| sameRay_smul_left_iff_of_ne v.ne_zero r.ne_zero

@[simp]
theorem sameDir_smul_right_iff {v : VecND} {r : ℝˣ} :
    SameDir v (r • v) ↔ 0 < (r : ℝ) :=
  sameRay_iff_sameDir.symm.trans <| sameRay_smul_right_iff_of_ne v.ne_zero r.ne_zero

@[simp]
theorem sameRay_neg_smul_left_iff {v : VecND} {r : ℝˣ} :
    SameDir (r • v) (-v) ↔ (r : ℝ) < 0 :=
  sameRay_iff_sameDir.symm.trans <| sameRay_neg_smul_left_iff_of_ne v.ne_zero r.ne_zero

@[simp]
theorem sameRay_neg_smul_right_iff {v : VecND} {r : ℝˣ} :
    SameDir (-v) (r • v) ↔ (r : ℝ) < 0 :=
  sameRay_iff_sameDir.symm.trans <| sameRay_neg_smul_right_iff_of_ne v.ne_zero r.ne_zero

namespace SameDir

lemma mk0_pos_smul_left {v₁ v₂ : VecND} (h : SameDir v₁ v₂) {x : ℝ} (hx : 0 < x) :
    SameDir (Units.mk0 x hx.ne' • v₁) v₂ :=
  .ofSameRay <| h.toSameRay.pos_smul_left hx

lemma mk0_pos_smul_right {v₁ v₂ : VecND} (h : SameDir v₁ v₂) {x : ℝ} (hx : 0 < x) :
    SameDir v₁ (Units.mk0 x hx.ne' • v₂) :=
  .ofSameRay <| h.toSameRay.pos_smul_right hx

lemma mk0_neg_smul_left {v₁ v₂ : VecND} (h : SameDir v₁ v₂) {x : ℝ} (hx : x < 0) :
    SameDir (Units.mk0 x hx.ne • v₁) (-v₂) := by
  rw [← sameDir_neg_iff, neg_neg, ← VecND.neg_smul]
  exact h.mk0_pos_smul_left (neg_pos.mpr hx)

lemma mk0_neg_smul_right {v₁ v₂ : VecND} (h : SameDir v₁ v₂) {x : ℝ} (hx : x < 0) :
    SameDir (-v₁) (Units.mk0 x hx.ne • v₂) := by
  rw [← sameDir_neg_iff, neg_neg, ← VecND.neg_smul]
  exact h.mk0_pos_smul_right (neg_pos.mpr hx)

end SameDir

theorem sameDir_comm {v₁ v₂ : VecND} : SameDir v₁ v₂ ↔ SameDir v₂ v₁ :=
  ⟨SameDir.symm, SameDir.symm⟩

@[simp]
theorem sameDir_map_iff {v₁ v₂ : VecND} (e : Vec ≃ₗ[ℝ] Vec) :
    SameDir (VecND.map e v₁) (VecND.map e v₂) ↔ SameRay ℝ (v₁ : Vec) (v₂ : Vec) :=
  sameRay_iff_sameDir.symm.trans (SameRay.sameRay_map_iff e)

lemma cdiv_of_sameDir {v₁ v₂ : VecND} (h : v₁.SameDir v₂) :
    (v₁ / v₂ : ℂ) = ‖v₁‖ / ‖v₂‖ := by
  simpa using Vec.cdiv_of_sameRay h.toSameRay

lemma angle_of_sameDir {v₁ v₂ v₃ v₄ : VecND} (h₁ : v₁.SameDir v₃) (h₂ : v₂.SameDir v₄) :
    angle v₁ v₂ = angle v₃ v₄ := by
  simp_rw [angle, (· -ᵥ ·), toMul_ofMul, Complex.arg_coe_angValue_eq_iff,
    Complex.arg_eq_arg_iff (Units.ne_zero _) (Units.ne_zero _), coe_cdiv, Vec.abs_cdiv]
  rw [Vec.mul_cdiv, Vec.cdiv_eq_cdiv_iff_cdiv_eq_cdiv v₁.ne_zero v₄.ne_zero, Vec.cdiv_of_sameRay h₁.toSameRay,
    Vec.cdiv_of_sameRay (by norm_cast; exact h₂.toSameRay.nonneg_smul_left (by positivity))]
  simp only [norm_smul, norm_div, Complex.norm_real, norm_norm]
  norm_cast
  field_simp
  ring

theorem ne_zero_of_ne_zero_smul (v : VecND) {t : ℝ} (h : t ≠ 0) : t • v.1 ≠ 0 := by
  simp only [ne_eq, smul_eq_zero, h, v.2, or_self, not_false_eq_true]

@[simp]
lemma angle_rotate_right (θ : AngValue) (v : VecND) :
    angle v (VecND.rotate θ v) = θ := by
  simp [rotate, VecND.map, angle, vsub_def]

@[simp]
lemma sameDir_rotate (θ : AngValue) (v₁ v₂ : VecND) :
    SameDir (VecND.rotate θ v₁) (VecND.rotate θ v₂) ↔ v₁.SameDir v₂ := by
  simp [rotate]

@[simp]
lemma rotate_angle_eq_div_norm_smul (v₁ v₂ : VecND) :
    Vec.rotate (angle v₁ v₂) v₁ = (‖v₁‖ / ‖v₂‖) • v₂ := by
  rw [← inv_smul_eq_iff₀ (by positivity), inv_div]
  have : ↑(v₂ -ᵥ v₁ +ᵥ v₁) = (v₂ : Vec) := congr_arg _ <| vsub_vadd _ _
  simp only [vadd_def, vsub_def, Units.smul_def, Vec.smul_eq_rotate] at this
  simpa using this

lemma sameDir_rotate_angle_left (v₁ v₂ : VecND) :
    SameDir (VecND.rotate (angle v₁ v₂) v₁) v₂ := by
  simp [rotate, VecND.map]
  positivity

lemma sameDir_rotate_angle_right (v₁ v₂ : VecND) :
    SameDir v₁ (VecND.rotate (angle v₂ v₁) v₂) :=
  (sameDir_rotate_angle_left v₂ v₁).symm

theorem norm_mul_cos (v₁ v₂ : VecND) :
    ‖v₁‖ * ‖v₂‖ * (VecND.angle v₁ v₂).cos = ⟪v₁.1, v₂.1⟫_ℝ := by
  rw [angle, vsub_def, toMul_ofMul, coe_cdiv, AngValue.cos_coe,
    Complex.cos_arg (Vec.cdiv_ne_zero.mpr ⟨VecND.ne_zero _, VecND.ne_zero _⟩), Vec.abs_cdiv,
    Vec.cdiv_def, Vec.complex_inner_apply, Vec.real_inner_apply, Vec.det_apply]
  norm_cast
  rw [Complex.div_ofReal_re]
  field_simp
  ring

theorem norm_mul_sin (v₁ v₂ : VecND) :
    ‖v₁‖ * ‖v₂‖ * (VecND.angle v₁ v₂).sin = Vec.det v₁.1 v₂.1 := by
  rw [angle, vsub_def, toMul_ofMul, coe_cdiv, AngValue.sin_coe,
    Complex.sin_arg, Vec.abs_cdiv,
    Vec.cdiv_def, Vec.complex_inner_apply, Vec.real_inner_apply, Vec.det_apply]
  norm_cast
  rw [Complex.div_ofReal_im]
  field_simp
  ring

theorem norm_smul_expMapCircle (v₁ v₂ : VecND) :
    (‖v₁‖ * ‖v₂‖) • ((VecND.angle v₁ v₂).expMapCircle : ℂ) = ⟪v₁.1, v₂.1⟫_ℂ := by
  ext
  · simp [AngValue.coe_expMapCircle, VecND.norm_mul_cos]
  · simp [AngValue.coe_expMapCircle, VecND.norm_mul_sin]

end VecND

abbrev Dir := Module.Ray ℝ Vec

abbrev VecND.toDir (v : VecND) : Dir := ⟦v⟧

@[simp]
lemma Dir.quotient_mk_eq (v : VecND) : ⟦v⟧ = v.toDir := rfl

attribute [pp_dot] VecND.toDir

instance : Coe VecND Dir := ⟨VecND.toDir⟩

@[simp]
lemma VecND.neg_toDir (v : VecND) : (-v).toDir = -v.toDir := rfl

@[simp]
lemma VecND.toDir_eq_toDir_iff {v₁ v₂ : VecND} : v₁.toDir = v₂.toDir ↔ v₁.SameDir v₂ :=
  Quotient.eq.trans sameRay_iff_sameDir

@[simp, nolint simpNF]
lemma VecND.smul_pos_toDir {x : ℝ} (v : VecND) (hx : 0 < x) :
    (Units.mk0 x hx.ne' • v).toDir = v.toDir :=
  VecND.toDir_eq_toDir_iff.mpr <| SameDir.rfl.mk0_pos_smul_left hx

@[simp, nolint simpNF]
lemma VecND.smul_neg_toDir {x : ℝ} (v : VecND) (hx : x < 0) :
    (Units.mk0 x hx.ne • v).toDir = -v.toDir :=
  VecND.toDir_eq_toDir_iff.mpr <| SameDir.rfl.mk0_neg_smul_left hx

namespace Dir

@[elab_as_elim]
protected theorem ind {C : Dir → Prop} (h : ∀ (v : VecND), C v)
    (x : Dir) : C x :=
  Quotient.ind h x

protected def map (f : Vec ≃ₗ[ℝ] Vec) : Dir ≃ Dir :=
  Module.Ray.map f

@[simp]
theorem map_apply (f : Vec ≃ₗ[ℝ] Vec) (v : VecND) :
    Dir.map f v = VecND.toDir ⟨f v, f.map_ne_zero_iff.2 v.2⟩ :=
  rfl

@[simp]
theorem map_refl : (Dir.map <| LinearEquiv.refl ℝ Vec) = Equiv.refl _ :=
  Module.Ray.map_refl

@[simp]
theorem map_symm (f : Vec ≃ₗ[ℝ] Vec) : (Dir.map f).symm = Dir.map f.symm :=
  rfl

@[simp]
theorem map_trans (f₁ f₂ : Vec ≃ₗ[ℝ] Vec) : Dir.map (f₁.trans f₂) = (Dir.map f₁).trans (Dir.map f₂) :=
  Module.Ray.map_trans _ _

class NegCommute {α : Type*} [Neg α] (f : Dir → α) : Prop where
  map_neg' : ∀ d : Dir, f (-d) = -(f d)

lemma map_neg {α : Type*} [Neg α] (f : Dir → α) [NegCommute f] (d : Dir) :
    f (-d) = -(f d) :=
  NegCommute.map_neg' (f := f) d

@[simp]
lemma map_neg' (f : Dir ≃ Dir) [NegCommute f] (d : Dir) :
    f (-d) = -(f d) :=
  map_neg f d

instance negCommute_refl : NegCommute (Equiv.refl _) := ⟨by simp⟩

instance negCommute_symm (f : Dir ≃ Dir) [NegCommute f] : NegCommute f.symm :=
  ⟨fun d ↦ by simp [- map_neg', ← show f (-f.symm d) = -d by simp]⟩

instance negCommute_comp {α : Type*} [Neg α] (f : Dir → Dir) (g : Dir → α) [NegCommute f] [NegCommute g] :
    NegCommute (g ∘ f) :=
  ⟨fun d ↦ (congr_arg g (map_neg f d)).trans (map_neg g (f d))⟩

instance negCommute_trans (f g : Dir ≃ Dir) [NegCommute f] [NegCommute g] :
    NegCommute (f.trans g) :=
  negCommute_comp f g

instance negCommute_map (f : Vec ≃ₗ[ℝ] Vec) : NegCommute (Dir.map f) := ⟨Module.Ray.map_neg f⟩

abbrev rotate (θ : AngValue) : Dir ≃ Dir :=
  Dir.map ((Vec.rotate θ).restrictScalars ℝ)

instance negCommute_rotate (θ : AngValue) : NegCommute (rotate θ) := negCommute_map _

@[simp]
lemma rotate_zero : Dir.rotate 0 = Equiv.refl _ := by
  ext d
  induction d using Dir.ind
  simp

lemma rotate_pi_apply (d : Dir) : Dir.rotate π d = -d :=
  d.ind fun v ↦ by simp

lemma rotate_add_apply (θ ψ : AngValue) (d : Dir) :
    Dir.rotate (θ + ψ) d = Dir.rotate θ (Dir.rotate ψ d) :=
  d.ind fun v ↦ by simp

lemma rotate_add (θ ψ : AngValue) :
    Dir.rotate (θ + ψ) = Dir.rotate θ * Dir.rotate ψ := by
  ext
  simp [rotate_add_apply]

instance : VAdd AngValue Dir where
  vadd θ := rotate θ

lemma vadd_def (θ : AngValue) (p : Dir) : θ +ᵥ p = Dir.map ((Vec.rotate θ).restrictScalars ℝ) p :=
  rfl

instance : Nonempty Dir := (nonempty_quotient_iff _).mpr inferInstance

instance : AddTorsor AngValue Dir where
  zero_vadd d := d.ind fun v ↦ by
    simp [vadd_def]
  add_vadd θ₁ θ₂ d := d.ind fun v ↦ by
    simp [vadd_def]
  vsub := Quotient.lift₂ (Function.swap VecND.angle)
    fun _ _ _ _ h₁ h₂ ↦ VecND.angle_of_sameDir (.ofSameRay h₂) (.ofSameRay h₁)
  vsub_vadd' d₁ d₂ := d₁.ind fun v₁ ↦ d₂.ind fun v₂ ↦ by
    dsimp [vadd_def]
    rw [VecND.toDir_eq_toDir_iff]
    exact VecND.sameDir_rotate_angle_left v₂ v₁
  vadd_vsub' θ d := d.ind fun v ↦ by
    dsimp [vadd_def]
    exact VecND.angle_rotate_right θ v

@[simp]
lemma rotate_eq_vadd (θ : AngValue) (d : Dir) : rotate θ d = θ +ᵥ d := rfl

@[simp]
lemma vsub_toDir (v₁ v₂ : VecND) : v₂.toDir -ᵥ v₁.toDir = VecND.angle v₁ v₂ := rfl

@[simp]
lemma vadd_neg (θ : AngValue) (d : Dir) : θ +ᵥ -d = -(θ +ᵥ d) :=
  map_neg (rotate θ) d

@[simp]
lemma pi_vadd (d : Dir) : ∠[π] +ᵥ d = -d :=
  rotate_pi_apply d

@[simp]
lemma neg_vsub_left (d₁ d₂ : Dir) : -d₁ -ᵥ d₂ = d₁ -ᵥ d₂ + ∠[π] := by
  rw [← pi_vadd, vadd_vsub_assoc, add_comm]

@[simp]
lemma neg_vsub_right (d₁ d₂ : Dir) : d₁ -ᵥ -d₂ = d₁ -ᵥ d₂ + ∠[π] := by
  rw [← pi_vadd, vsub_vadd_eq_vsub_sub, sub_eq_add_neg, AngValue.neg_coe_pi]

protected abbrev normalize {M : Type*} [AddCommGroup M] [Module ℝ M]
    {F : Type*} [LinearMapClass F ℝ Vec M]
    (f : F) :
    Dir → M :=
  Quotient.lift (fun v : VecND ↦ ‖v‖⁻¹ • f ↑v)
    fun x y h ↦ SameRay.inv_norm_smul_map_eq f (by simp) (by simp) h

@[simp]
lemma normalize_apply {M : Type*} [AddCommGroup M] [Module ℝ M]
    {F : Type*} [LinearMapClass F ℝ Vec M]
    (f : F) (v : VecND) :
    Dir.normalize f ⟦v⟧ = ‖v‖⁻¹ • f v :=
  rfl

lemma normalize_apply_ne_zero {M : Type*} [AddCommGroup M] [Module ℝ M]
    {F : Type*} [LinearMapClass F ℝ Vec M]
    (f : F) (hf : Function.Injective f) (d : Dir) :
    d.normalize f ≠ 0 := d.ind fun v ↦ by
  simp [not_or, map_ne_zero_iff f hf]

@[pp_dot]
def unitVecND (d : Dir) : VecND :=
  ⟨Dir.normalize LinearMap.id d, normalize_apply_ne_zero _ (fun _ _ ↦ id) _⟩

@[pp_dot]
abbrev unitVec (d : Dir) : Vec :=
  d.unitVecND

@[simp]
lemma coe_unitVecND (d : Dir) : d.unitVecND = d.unitVec := rfl

lemma _root_.EuclidGeom.VecND.toDir_unitVecND (v : VecND) : v.toDir.unitVecND = ⟨‖v‖⁻¹ • v, by simp⟩ := rfl

lemma _root_.EuclidGeom.VecND.toDir_unitVec (v : VecND) : v.toDir.unitVec = ‖v‖⁻¹ • v := rfl

lemma _root_.EuclidGeom.VecND.inv_norm_smul (v : VecND) : ‖v‖⁻¹ • (v : Vec) = v.toDir.unitVecND := rfl

@[simp]
lemma neg_unitVecND (d : Dir) : (-d).unitVecND = -d.unitVecND := d.ind fun v ↦ by
  ext
  rw [← VecND.neg_toDir, VecND.toDir_unitVecND, VecND.toDir_unitVecND]
  simp

@[simp]
lemma neg_unitVec (d : Dir) : (-d).unitVec = -d.unitVec :=
  congr_arg _ d.neg_unitVecND

@[simp]
theorem _root_.EuclidGeom.VecND.norm_smul_toDir_unitVec (v : VecND) : ‖v‖ • v.toDir.unitVec = v := by
  simp [Dir.unitVec, Dir.unitVecND]

@[simp]
theorem _root_.EuclidGeom.Vec.norm_smul_toDir_unitVec {v : Vec} (hv : v ≠ 0) : ‖v‖ • (VecND.mk v hv).toDir.unitVec = v :=
  VecND.norm_smul_toDir_unitVec ⟨v, hv⟩

@[simp]
lemma unitVecND_toDir (d : Dir) : d.unitVecND.toDir = d := by
  induction d using Dir.ind
  simp [VecND.toDir_unitVecND]

lemma norm_unitVec (d : Dir) : ‖d.unitVec‖ = 1 := by
  rw [← d.unitVecND_toDir, VecND.toDir_unitVec, norm_smul, norm_inv, ← VecND.norm_coe, norm_norm, inv_mul_cancel]
  simp

@[simp]
lemma norm_unitVecND (d : Dir) : ‖d.unitVecND‖ = 1 := by
  rw [← VecND.norm_coe, norm_unitVec]

section CircularOrder

instance : Btw Dir where
  btw d₁ d₂ d₃ := btw (d₁ -ᵥ d₁) (d₂ -ᵥ d₁) (d₃ -ᵥ d₁)

@[simp]
lemma btw_vadd_left {θ : AngValue} {d₁ d₂ d₃ : Dir} :
    btw (θ +ᵥ d₁) (θ +ᵥ d₂) (θ +ᵥ d₃) ↔ btw d₁ d₂ d₃ := by
  simp only [btw, vadd_vsub_vadd_cancel_left, vsub_self, sub_zero]

@[simp]
lemma btw_vadd_right {θ₁ θ₂ θ₃ : AngValue} {d : Dir} :
    btw (θ₁ +ᵥ d) (θ₂ +ᵥ d) (θ₃ +ᵥ d) ↔ btw θ₁ θ₂ θ₃ := by
  simp only [btw, vadd_vsub_vadd_cancel_right, vsub_self, sub_zero]

@[simp]
lemma btw_vsub_right {d₁ d₂ d₃ d : Dir} :
    btw (d₁ -ᵥ d) (d₂ -ᵥ d) (d₃ -ᵥ d) ↔ btw d₁ d₂ d₃ := by
  simp only [btw, vsub_sub_vsub_cancel_right, vsub_self, sub_zero]

@[simp]
lemma btw_vsub_left {d d₁ d₂ d₃ : Dir} :
    btw (d -ᵥ d₁) (d -ᵥ d₂) (d -ᵥ d₃) ↔ btw d₃ d₂ d₁ := by
  rw [← btw_vsub_right (d := d)]
  simp [btw]
  sorry

@[simp]
lemma btw_neg {d₁ d₂ d₃ : Dir} :
    btw (-d₁) (-d₂) (-d₃) ↔ btw d₁ d₂ d₃ := by
  rw [← pi_vadd, ← pi_vadd, ← pi_vadd, btw_vadd_left]

instance : CircularOrder Dir where
  btw d₁ d₂ d₃ := btw (d₁ -ᵥ d₁) (d₂ -ᵥ d₁) (d₃ -ᵥ d₁)
  sbtw d₁ d₂ d₃ := sbtw (d₁ -ᵥ d₁) (d₂ -ᵥ d₁) (d₃ -ᵥ d₁)
  btw_refl d := by simpa using btw_refl _
  btw_cyclic_left {d₁ d₂ d₃} h := by
    simp [btw]
    sorry
  sbtw_iff_btw_not_btw := sorry
  sbtw_trans_left := sorry
  btw_antisymm := sorry
  btw_total := sorry

end CircularOrder

@[simp]
theorem _root_.EuclidGeom.angle_toDir_unitVecND_left (v₁ v₂ : VecND) : VecND.angle v₁.toDir.unitVecND v₂ = VecND.angle v₁ v₂ := by
  rw [← vsub_toDir, ← vsub_toDir]
  simp

@[simp]
theorem _root_.EuclidGeom.angle_toDir_unitVecND_right (v₁ v₂ : VecND) : VecND.angle v₁ v₂.toDir.unitVecND = VecND.angle v₁ v₂ := by
  rw [← vsub_toDir, ← vsub_toDir]
  simp

@[simp]
theorem angle_unitVecND (d₁ d₂ : Dir) : VecND.angle d₁.unitVecND d₂.unitVecND = d₂ -ᵥ d₁ := by
  induction d₁ using Dir.ind
  induction d₂ using Dir.ind
  simp

@[simp]
theorem inner_unitVec (d₁ d₂ : Dir) : ⟪d₁.unitVec, d₂.unitVec⟫_ℝ = (d₂ -ᵥ d₁).cos := by
  simp [← VecND.norm_mul_cos]

@[simp]
theorem det_unitVec (d₁ d₂ : Dir) : Vec.det d₁.unitVec d₂.unitVec = (d₂ -ᵥ d₁).sin := by
  simp [← VecND.norm_mul_sin]

theorem complex_inner_unitVec (d₁ d₂ : Dir) : ⟪d₁.unitVec, d₂.unitVec⟫_ℂ = (d₂ -ᵥ d₁).expMapCircle := by
  simp [← VecND.norm_smul_expMapCircle]

end Dir

-- def Proj := Projectivization ℝ Vec
-- for better defeq
def Proj := Quotient <| Setoid.correspondence (RayVector.Setoid ℝ Vec) ⟨projectivizationSetoid ℝ Vec, by
  intro _ _ h
  obtain ⟨x, hx, h⟩ := VecND.SameDir.ofSameRay h
  exact ⟨.mk0 x hx.ne', h.symm⟩⟩

@[pp_dot]
def Dir.toProj : Dir → Proj := Quotient.mk _

@[pp_dot]
abbrev VecND.toProj (v : VecND) : Proj := v.toDir.toProj

@[simp]
lemma Dir.unitVecND_toProj (d : Dir) : d.unitVecND.toProj = d.toProj := by
  simp [VecND.toProj]

theorem VecND.toProj_eq_toProj_iff₀ {v₁ v₂ : VecND} :
    v₁.toProj = v₂.toProj ↔ ∃ a : ℝˣ, (v₁ : Vec) = a • (v₂ : Vec) := by
  simp_rw [eq_comm (b := _ • _)]
  exact Quotient.eq''

theorem VecND.toProj_eq_toProj_iff {v₁ v₂ : VecND} :
    v₁.toProj = v₂.toProj ↔ ∃ a : ℝ, (v₁ : Vec) = a • (v₂ : Vec) := by
  rw [toProj_eq_toProj_iff₀]
  constructor
  · rintro ⟨x, h⟩
    exact ⟨x, h⟩
  · rintro ⟨x, h⟩
    exact ⟨.mk0 x (smul_ne_zero_iff.mp (h.symm.trans_ne v₁.ne_zero)).1, h⟩

theorem VecND.toProj_eq_toProj_iff' {v₁ v₂ : VecND} :
    v₁.toProj = v₂.toProj ↔ ∃ a : ℝˣ, v₁ = a • v₂ := by
  rw [toProj_eq_toProj_iff₀]
  norm_cast

instance : Coe Dir Proj where
  coe v := v.toProj

@[simp]
theorem VecND.toDir_toProj (v : VecND) :
    (v.toDir : Proj) = v.toProj :=
  rfl

theorem Dir.toProj_eq_toProj_iff {d₁ d₂ : Dir} :
    (d₁ : Proj) = (d₂ : Proj) ↔ d₁ = d₂ ∨ d₁ = -d₂ := d₁.ind fun v₁ ↦ d₂.ind fun v₂ ↦ by
  constructor
  · simp_rw [VecND.toDir_toProj, VecND.toProj_eq_toProj_iff₀, ← VecND.neg_toDir, VecND.toDir_eq_toDir_iff]
    rintro ⟨x, h⟩
    by_cases hx : 0 ≤ (x : ℝ)
    · exact .inl ⟨x, hx.lt_of_ne x.ne_zero.symm, h⟩
    · exact .inr ⟨-x, neg_pos.mpr (lt_of_not_ge hx), by simp [h]; rfl⟩
  · simp_rw [VecND.toDir_toProj, VecND.toProj_eq_toProj_iff, ← VecND.neg_toDir, VecND.toDir_eq_toDir_iff]
    rintro (⟨x, -, h⟩ | ⟨x, -, h⟩)
    · exact ⟨x, h⟩
    · exact ⟨-x, by simpa using h⟩

theorem Dir.toProj_eq_toProj_iff_unitVec₀ {d₁ d₂ : Dir} :
    d₁.toProj = d₂.toProj ↔ ∃ a : ℝˣ, d₁.unitVec = a • d₂.unitVec := by
  conv_lhs => rw [← d₁.unitVecND_toDir, ← d₂.unitVecND_toDir]
  rw [VecND.toProj_eq_toProj_iff₀]

theorem Dir.toProj_eq_toProj_iff_unitVec {d₁ d₂ : Dir} :
    d₁.toProj = d₂.toProj ↔ ∃ a : ℝ, d₁.unitVec = a • d₂.unitVec := by
  conv_lhs => rw [← d₁.unitVecND_toDir, ← d₂.unitVecND_toDir]
  rw [VecND.toProj_eq_toProj_iff]

theorem Dir.toProj_eq_toProj_iff_unitVecND {d₁ d₂ : Dir} :
    d₁.toProj = d₂.toProj ↔ ∃ a : ℝˣ, d₁.unitVecND = a • d₂.unitVecND := by
  conv_lhs => rw [← d₁.unitVecND_toDir, ← d₂.unitVecND_toDir]
  rw [VecND.toProj_eq_toProj_iff']

@[simp]
lemma VecND.neg_toProj (v : VecND) : (-v).toProj = v.toProj := by
  rw [toProj_eq_toProj_iff']
  exact ⟨-1, by simp⟩

@[simp]
lemma Dir.toProj_neg (d : Dir) : (↑(-d) : Proj) = (d : Proj) :=
  d.ind fun v ↦ by rw [← VecND.neg_toDir, VecND.toDir_toProj, VecND.toDir_toProj, VecND.neg_toProj]

theorem Vec.det_eq_zero_iff_eq_smul_right {u v : Vec} : Vec.det u v = 0 ↔ v = 0 ∨ (∃ (t : ℝ), u = t • v) := by
  constructor
  · intro e
    by_cases h : v = 0; · exact .inl h
    right
    have h : v.1 ≠ 0 ∨ v.2 ≠ 0
    · contrapose! h
      apply Vec.ext <;> simp [h]
    push_neg at h
    obtain (h | h) := h
    · use v.1⁻¹ * u.1
      rw [mul_smul, eq_inv_smul_iff₀ h]
      rw [det_apply, sub_eq_zero] at e
      apply ext
      · simp [mul_comm]
      · simp [e, mul_comm]
    · use v.2⁻¹ * u.2
      rw [mul_smul, eq_inv_smul_iff₀ h]
      rw [det_apply, sub_eq_zero] at e
      apply ext
      · simp [e, mul_comm]
      · simp [mul_comm]
  · rintro (h | ⟨t, rfl⟩)
    · simp [h]
    · simp

theorem Vec.det_eq_zero_iff_eq_smul_left {u v : Vec} : Vec.det u v = 0 ↔ u = 0 ∨ (∃ (t : ℝ), v = t • u) := by
  rw [← det_skew, neg_eq_zero, det_eq_zero_iff_eq_smul_right]

theorem VecND.det_eq_zero_iff_toProj_eq_toProj {u v : VecND} :
    Vec.det u v = 0 ↔ u.toProj = v.toProj := by
  rw [Vec.det_eq_zero_iff_eq_smul_right, VecND.toProj_eq_toProj_iff]
  simp


namespace Proj

protected theorem ind {C : Proj → Prop} (h : ∀ (d : Dir), C d)
    (x : Proj) : C x :=
  Quotient.ind h x

protected abbrev lift {α : Sort*} (f : Dir → α) (hf : ∀ d, f (-d) = f d) : Proj → α :=
  Quotient.lift (fun d : Dir ↦ f d) fun (d₁ d₂ : Dir) ↦ (by
    induction' d₁ using Dir.ind with v₁
    induction' d₂ using Dir.ind with v₂
    intro ⟨x, h⟩
    dsimp at h ⊢
    norm_cast at h
    rw [← h]
    by_cases h : 0 < (x : ℝ)
    · congr 1
      simp [h]
    · push_neg at h
      rw [← hf v₂.toDir, ← v₂.neg_toDir]
      congr 1
      simp [- VecND.neg_toDir, h.lt_of_ne])

@[simp]
lemma lift_dir_toProj {α : Sort*} (f : Dir → α) (hf : ∀ d, f (-d) = f d) (d : Dir) :
    Proj.lift f hf d = f d :=
  rfl

@[simp]
lemma lift_vecND_toProj {α : Sort*} (f : Dir → α) (hf : ∀ d, f (-d) = f d) (v : VecND) :
    Proj.lift f hf v.toProj = f v.toDir :=
  rfl

def map (f : Dir ≃ Dir) [Dir.NegCommute f] : Proj ≃ Proj where
  toFun := Proj.lift (f ·) fun d ↦ by simp [Dir.map_neg]
  invFun := Proj.lift (f.symm ·) fun d ↦ by simp [Dir.map_neg]
  left_inv p := by
    induction p using Proj.ind
    simp
  right_inv p := by
    induction p using Proj.ind
    simp

@[simp]
lemma map_apply (f : Dir ≃ Dir) {_ : Dir.NegCommute f} (d : Dir) :
    Proj.map f d = f d :=
  rfl

@[simp]
lemma map_vecND_toProj (f : Dir ≃ Dir) {_ : Dir.NegCommute f} (v : VecND) :
    Proj.map f v.toProj = f v.toDir :=
  rfl

@[simp]
theorem map_refl : (Proj.map (Equiv.refl _)) = Equiv.refl _ := by
  ext ⟨⟩
  rfl

@[simp]
theorem map_symm (f : Dir ≃ Dir) {_ : Dir.NegCommute f} :
    (Proj.map f).symm = Proj.map f.symm :=
  rfl

@[simp]
theorem map_trans (f g : Dir ≃ Dir) {_ : Dir.NegCommute f} {_ : Dir.NegCommute g} :
    Proj.map (f.trans g) = (Proj.map f).trans (Proj.map g) := by
  ext p
  induction p using Proj.ind
  simp

instance : Nonempty Proj := (nonempty_quotient_iff _).mpr <| inferInstanceAs (Nonempty Dir)

instance : VAdd AngDValue Proj where
  vadd := AngDValue.lift (fun θ ↦ Proj.map (Dir.rotate θ)) fun θ ↦ by
    ext p
    induction p using Proj.ind
    simp [add_vadd]

lemma vadd_coe_left (θ : AngValue) (p : Proj) : (θ : AngDValue) +ᵥ p = Proj.map (Dir.rotate θ) p := by
  induction θ using AngValue.induction_on
  rfl

@[simp]
lemma vadd_coe (θ : AngValue) (d : Dir) : (θ : AngDValue) +ᵥ (d : Proj) = θ +ᵥ d := by
  simp only [vadd_coe_left, Dir.vadd_def]
  simp

instance : AddTorsor AngDValue Proj where
  zero_vadd p := by
    induction p using Proj.ind
    rw [← AngDValue.coe_zero]
    simp [- AngDValue.coe_zero]
  add_vadd θ₁ θ₂ p := by
    induction θ₁ using AngDValue.induction_on
    induction θ₂ using AngDValue.induction_on
    induction p using Proj.ind
    rw [← AngDValue.coe_add]
    simp [- AngDValue.coe_add, add_vadd]
  vsub := Proj.lift (fun d₁ ↦ Proj.lift (fun d₂ ↦ d₁ -ᵥ d₂)
    (fun d₂ ↦ by simp [AngDValue.coe_eq_coe_iff])) (fun d₁ ↦ by ext d₂; simp)
  vsub_vadd' p₁ p₂ := by
    induction p₁ using Proj.ind
    induction p₂ using Proj.ind
    simp
  vadd_vsub' θ p := by
    induction θ using AngDValue.induction_on
    induction p using Proj.ind
    simp

@[pp_dot]
def perp (p : Proj) : Proj := ∡[π / 2] +ᵥ p

@[simp]
lemma perp_perp (p : Proj) : p.perp.perp = p := by
  rw [perp, perp, vadd_vadd]
  norm_cast
  simp

end Proj

end EuclidGeom
