import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Standard ℝ²

This file defines the standard inner product real vector space of dimension two.

## Important definitions

* `Dir` : the class of unit vectors in the 2d real vector space
* `Proj` : the class of `Dir` quotient by `±1`, in other words, `ℝP²` . 

## Notation

## Implementation Notes

In section `StdR2`, we define all of the sturctures on the standard 2d inner product real vector space `ℝ × ℝ`. We use defs and do NOT use instances here in order to avoid conflicts to existing instance of such stuctures on `ℝ × ℝ` which is based on `L^∞` norm of the product space. Then we define the angle of two vectors, which takes value in `(-π, π]`. Notice that if any one of the two vector is `0`, the angle is defined to be `0`.

Then we define the class `Dir` of vectors of unit length. We equip it with the structure of commutative group. The quotient `Proj` of `Dir` by `±1` is automatically a commutative group.

## Further Works
Inequalities about `ℝ²` should be written at the beginning of this file.

The current definition is far from being general enough. Roughly speaking, it suffices to define the Euclidean Plane to be a `NormedAddTorsor` over any 2 dimensional normed real inner product spaces `V` with a choice of an orientation on `V`, rather than over the special `ℝ × ℝ`. All further generalizations in this file should be done together with Plane.lean.
-/

noncomputable section
namespace EuclidGeom

scoped notation "π" => Real.pi

/- structures on `ℝ × ℝ`-/
namespace StdR2

protected def AddGroupNorm : AddGroupNorm (ℝ × ℝ) where
  toFun := fun x => Real.sqrt (x.1 * x.1  + x.2 * x.2)
  map_zero' := by simp
  add_le' := fun x y => by 
    simp
    repeat rw [← pow_two]
    apply le_of_pow_le_pow 2 (by positivity) (by positivity)
    rw [Real.sq_sqrt (by positivity)]
    nth_rw 1 [pow_two]
    nth_rw 1 [pow_two]
    nth_rw 1 [pow_two]
    simp [mul_add, add_mul]
    rw [Real.mul_self_sqrt (by positivity)]
    rw [Real.mul_self_sqrt (by positivity)]
    have P :  x.1 * y.1 + x.2 * y.2 ≤ Real.sqrt (x.1^2 + x.2^2) * Real.sqrt (y.1^2 + y.2^2) := by
      let h := (x.1 * y.1 + x.2 * y.2 ≤  0)
      by_cases h
      · apply le_trans h
        exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      · apply le_of_pow_le_pow 2 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)
        rw [mul_pow]
        simp [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
        simp [pow_two, add_mul, mul_add]
        let h1 := two_mul_le_add_pow_two (x.1 * y.2) (x.2 * y.1)
        linarith
    repeat rw [pow_two] at P
    let Q := P
    rw [mul_comm (Real.sqrt (x.fst ^ 2 + x.snd ^ 2)) _] at Q
    simp [pow_two] at *    
    linarith

  neg' := fun _ => by simp
  eq_zero_of_map_eq_zero' := fun x => by
    simp
    intro h
    rw [Real.sqrt_eq_zero'] at h
    simp [← pow_two] at h
    let hx₁ := sq_nonneg x.1
    let hx₂ := sq_nonneg x.2
    ext
    · by_contra h₁
      simp at h₁
      rw [← Ne.def] at h₁
      have h₁₁ := sq_pos_of_ne_zero _ h₁
      linarith
    · by_contra h₁
      simp at h₁
      rw [← Ne.def] at h₁
      have h₂₁ := sq_pos_of_ne_zero _ h₁
      linarith

protected def InnerProductSpace.Core : InnerProductSpace.Core ℝ (ℝ × ℝ) where
  inner := fun r s => r.1 * s.1 + r.2 * s.2
  conj_symm := fun _ _ => by
    simp
    ring
  nonneg_re := fun _ => by 
    simp
    ring_nf
    positivity
  definite := fun x hx => by
    simp at hx
    rw [← pow_two, ← pow_two] at hx
    have g₁ : 0 ≤ @HPow.hPow ℝ ℕ ℝ _ x.1 2  := by positivity
    have g₂ : 0 ≤ @HPow.hPow ℝ ℕ ℝ _ x.2 2  := by positivity
    ext
    · dsimp
      by_contra h
      have h₁ : 0 < @HPow.hPow ℝ ℕ ℝ _ x.1 2  := by positivity
      linarith
    · dsimp
      by_contra h
      have h₂ : 0 < @HPow.hPow ℝ ℕ ℝ _ x.2 2  := by positivity
      linarith  
  add_left := fun _ _ _ => by 
    simp
    ring
  smul_left := fun _ _ _ => by
    simp
    ring

/- shortcuts -/
protected def NormedAddCommGroup : NormedAddCommGroup (ℝ × ℝ) := AddGroupNorm.toNormedAddCommGroup StdR2.AddGroupNorm

protected def NormedAddGroup : NormedAddGroup (ℝ × ℝ) := @NormedAddCommGroup.toNormedAddGroup _ StdR2.NormedAddCommGroup

protected def InnerProductSpace : @InnerProductSpace ℝ (ℝ × ℝ) _ StdR2.NormedAddCommGroup := InnerProductSpace.ofCore StdR2.InnerProductSpace.Core

protected def SeminormedAddCommGroup := @NormedAddCommGroup.toSeminormedAddCommGroup _ (StdR2.InnerProductSpace.Core.toNormedAddCommGroup)

protected def SeminormedAddGroup := @SeminormedAddCommGroup.toSeminormedAddGroup _ (StdR2.SeminormedAddCommGroup)

protected def MetricSpace := @NormedAddCommGroup.toMetricSpace _ (StdR2.InnerProductSpace.Core.toNormedAddCommGroup)

protected def PseudoMetricSpace := @MetricSpace.toPseudoMetricSpace _ StdR2.MetricSpace

protected def Norm := @NormedAddCommGroup.toNorm _ (StdR2.NormedAddCommGroup)

protected def toComplex (x : ℝ × ℝ) : ℂ := ⟨x.1, x.2⟩

/- WARNING : the arg of `0 : ℂ` is `0`, the result of quotient by `0 : ℂ` is `0 : ℂ`-/
protected def angle (x y : ℝ × ℝ) : ℝ := Complex.arg ((StdR2.toComplex x)/(StdR2.toComplex y))

def ComplextoVec (c : ℂ) : ℝ × ℝ := ⟨c.1, c.2⟩

end StdR2

/- the notation for class of vectors-/
scoped notation "Vec" => ℝ × ℝ



@[ext]
class Dir where
  vec : Vec
  unit : StdR2.InnerProductSpace.Core.inner vec vec = 1 

def Vec.normalize (x : ℝ × ℝ) (h : x ≠ 0) : Dir where
  vec := (StdR2.NormedAddCommGroup.norm x)⁻¹ • x 
  unit := by 
    rw [@real_inner_smul_left _ StdR2.NormedAddCommGroup StdR2.InnerProductSpace _ _ _, @real_inner_smul_right _ StdR2.NormedAddCommGroup StdR2.InnerProductSpace _ _ _, @inner_self_eq_norm_sq_to_K _ _ _ StdR2.NormedAddCommGroup StdR2.InnerProductSpace]
    dsimp
    rw [pow_two]
    rw [← mul_assoc _ _ (@norm (ℝ × ℝ) StdR2.NormedAddCommGroup.toNorm x)]
    simp only [ne_eq, inv_mul_mul_self]
    rw [inv_mul_cancel ((@norm_ne_zero_iff _ StdR2.NormedAddGroup).mpr h)]

-- Should change Dir into the following Dir'to use all instances on Dir'
def Dir' := @Metric.sphere _ StdR2.PseudoMetricSpace (0: ℝ × ℝ) 1

-- Or alternatively, define CommGroup instance on Dir
namespace Dir

instance : Neg Dir where
  neg := fun x => {
      vec := -x.vec
      unit := by 
        rw [← unit]
        exact @inner_neg_neg _ _ _ StdR2.NormedAddCommGroup StdR2.InnerProductSpace _ _
    }

def mk_angle (θ : ℝ) : Dir where
  vec := (Real.cos θ, Real.sin θ)
  unit := by 
    rw [← Real.cos_sq_add_sin_sq θ]
    rw [pow_two, pow_two]
    rfl

instance : Mul Dir where
  mul := fun z w => {
    vec := StdR2.ComplextoVec (StdR2.toComplex z.vec * StdR2.toComplex w.vec)
    -- vec := (z.vec.1 * w.vec.1 - z.vec.2 * w.vec.2, z.vec.1 * w.vec.2 + z.vec.2 * w.vec.1)
    unit := by
      unfold Inner.inner StdR2.InnerProductSpace.Core StdR2.ComplextoVec StdR2.toComplex
      simp
      ring_nf
      calc 
        _ = (z.vec.1 ^ 2 + z.vec.2 ^ 2) * (w.vec.1 ^ 2 + w.vec.2 ^ 2) := by
          ring_nf
          simp only [Real.rpow_two]
          linarith
        _ = 1 * 1 := by 
          simp only [Real.rpow_two, pow_two]
          congr 1
          · exact z.unit
          · exact w.unit
        _ = 1 := one_mul 1
  } 

instance : One Dir where
  one := {
    vec := (1, 0)
    unit := by 
      unfold Inner.inner StdR2.InnerProductSpace.Core
      simp
  }

@[simp]
theorem fst_of_one_eq_one : (1 : Dir).vec.1 = 1 := rfl

@[simp]
theorem snd_of_one_eq_zero : (1 : Dir).vec.2 = 0 := rfl

@[simp]
theorem one_eq_one_toComplex : StdR2.toComplex (1 : Dir).vec = 1 := rfl

@[simp]
theorem one_ComplextoVec_eq_one : StdR2.ComplextoVec (1 : ℂ) = (1, 0) := rfl

@[simp]
theorem eq_self_toComplex_ComplextoVec (x : ℝ × ℝ) : StdR2.ComplextoVec (StdR2.toComplex x) = x := rfl

@[simp]
theorem sq_sum_eq_one (x : Dir) : @HPow.hPow ℝ ℕ ℝ _ x.vec.1 2 + @HPow.hPow ℝ ℕ ℝ _ x.vec.2 2 = 1 := by
  rw [pow_two, pow_two]
  exact x.unit

instance : Semigroup Dir where
  mul_assoc _ _ _ := by
    ext : 1
    unfold vec HMul.hMul instHMul Mul.mul instMulDir StdR2.ComplextoVec StdR2.toComplex
    simp
    ring_nf

instance : Monoid Dir where
  one_mul := fun _ => by
    ext : 1
    unfold vec HMul.hMul instHMul Mul.mul Semigroup.toMul instSemigroupDir instMulDir
    simp
    rfl
  mul_one := fun _ => by
    ext : 1
    unfold vec HMul.hMul instHMul Mul.mul Semigroup.toMul instSemigroupDir instMulDir
    simp
    rfl

instance : CommGroup Dir where
  inv := fun x => {
    vec := (x.1.fst, -x.1.snd)
    unit := by
      unfold inner StdR2.InnerProductSpace.Core
      simp
      exact x.2
  }
  mul_left_inv _ := by
    ext : 1
    unfold HMul.hMul Inv.inv instHMul Mul.mul Semigroup.toMul Monoid.toSemigroup instMonoidDir instSemigroupDir instMulDir StdR2.toComplex StdR2.ComplextoVec
    simp
    ring_nf
    ext
    simp
    simp
    
  mul_comm _ _ := by
    ext : 1
    unfold vec HMul.hMul instHMul Mul.mul Semigroup.toMul Monoid.toSemigroup instMonoidDir instSemigroupDir instMulDir
    simp
    ring_nf

instance : HasDistribNeg Dir where
  neg := Neg.neg
  neg_neg _ := by
    unfold Neg.neg instNegDir
    simp
  neg_mul _ _ := by
    ext : 1
    unfold Neg.neg instNegDir vec HMul.hMul instHMul Mul.mul instMulDir StdR2.toComplex StdR2.ComplextoVec vec
    simp
    ring_nf
  mul_neg _ _ := by
    ext : 1
    unfold Neg.neg instNegDir vec HMul.hMul instHMul Mul.mul instMulDir StdR2.toComplex StdR2.ComplextoVec vec
    simp
    ring_nf

end Dir

def PM : Dir → Dir → Prop :=
fun x y => x = y ∨ x = -y

/-
@[simp]
theorem neg_to_complex_eq_to_complex_neg (x : Dir) : StdR2.toComplex (-x).vec = -StdR2.toComplex x.vec := by
  sorry
-/

namespace PM

def equivalence : Equivalence PM where
  refl _ := by simp [PM]
  symm := fun h => 
    match h with
      | Or.inl h₁ => Or.inl (Eq.symm h₁)
      | Or.inr h₂ => Or.inr (Iff.mp neg_eq_iff_eq_neg (id (Eq.symm h₂)))
  trans := by
    intro _ _ z g h
    unfold PM
    match g with
      | Or.inl g₁ => 
          rw [← g₁] at h
          exact h
      | Or.inr g₂ => 
          match h with
            | Or.inl h₁ =>
              rw [h₁] at g₂
              right
              exact g₂
            | Or.inr h₂ =>
              rw [h₂] at g₂
              have g₃ : z = - - z := Iff.mp neg_eq_iff_eq_neg rfl
              rw [← g₃] at g₂
              rw [g₂]
              left
              rfl

instance con : Con Dir where
  r := PM
  iseqv := PM.equivalence
  mul' := by
    unfold Setoid.r PM
    simp
    intro _ _ _ _ g h
    match g with
      | Or.inl g₁ => 
        match h with
          | Or.inl h₁ =>
            left
            rw [g₁, h₁]
          | Or.inr h₂ =>
            right
            rw [g₁, h₂]
            exact mul_neg _ _
      | Or.inr g₂ => 
        match h with
          | Or.inl h₁ =>
            right
            rw [g₂, h₁]
            exact neg_mul _ _
          | Or.inr h₂ =>
            left
            rw[g₂, h₂]
            exact neg_mul_neg _ _

end PM

def Proj := Con.Quotient PM.con

namespace Proj

instance : MulOneClass Proj := Con.mulOneClass PM.con

instance : Group Proj := Con.group PM.con

instance : CommMonoid Proj := Con.commMonoid PM.con

instance : CommGroup Proj where
  mul_comm := instCommMonoidProj.mul_comm

end Proj

def Dir.toProj (v : Dir) : Proj := ⟦v⟧

instance : Coe Dir Proj where
  coe v := v.toProj

def StdR2.toProj_of_nonzero (v : ℝ × ℝ) (h : v ≠ 0) : Proj := (Vec.normalize v h : Proj) 

theorem normalize_eq_mul_pos_normalize {u v : ℝ × ℝ} (hu : u ≠ 0) (hv : v ≠ 0) {t : ℝ} (h : v = t • u) (ht : t > 0) : Vec.normalize u hu = Vec.normalize v hv := by
  sorry

theorem eq_toProj_of_smul {u v : ℝ × ℝ} (hu : u ≠ 0) (hv : v ≠ 0) {t : ℝ} (h : v = t • u) : StdR2.toProj_of_nonzero v hv = StdR2.toProj_of_nonzero u hu := by
  sorry 

end EuclidGeom
