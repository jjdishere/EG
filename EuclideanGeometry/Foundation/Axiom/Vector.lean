import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Standard ℝ²

This file defines the standard inner product real vector space of dimension two.

## Important definitions

* `UniVec` : the class of unit vectors in the 2d real vector space

## Notation

## Implementation Notes

In section `StdR2`, we define all of the sturctures on the standard 2d inner product real vector space `ℝ × ℝ`. We use defs and do NOT use instances here in order to avoid conflicts to existing instance of such stuctures on `ℝ × ℝ` which is based on `L^∞` norm of the product space. Then we define the angle of two vectors, which takes value in `(-π, π]`. Notice that if any one of the two vector is `0`, the angle is defined to be `0`.

Then we define the class `UniVec` of vectors of unit length. 

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
    let hx1 := sq_nonneg x.1
    let hx2 := sq_nonneg x.2
    ext
    · by_contra h₁
      simp at h₁
      rw [← Ne.def] at h₁
      have h11 := sq_pos_of_ne_zero _ h₁
      linarith
    · by_contra h₁
      simp at h₁
      rw [← Ne.def] at h₁
      have h21 := sq_pos_of_ne_zero _ h₁
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
    sorry
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

end StdR2
@[ext]
class UniVec where
  vec : ℝ × ℝ 
  unit : StdR2.InnerProductSpace.Core.inner vec vec = 1 

-- Should change UniVec into the following UniVec'to use all instances on UniVec'
def UniVec' := @Metric.sphere _ StdR2.PseudoMetricSpace (0: ℝ × ℝ) 1

-- Or alternatively, define CommGroup instance on UniVec
namespace UniVec

instance : Neg UniVec where
  neg := fun x => {
      vec := -x.vec
      unit := by 
        rw [← unit]
        exact @inner_neg_neg _ _ _ StdR2.NormedAddCommGroup StdR2.InnerProductSpace _ _
    }

def normalize (x : ℝ × ℝ) (h : x ≠ 0) : UniVec where
  vec := (StdR2.NormedAddCommGroup.norm x)⁻¹ • x 
  unit := by 
    rw [@real_inner_smul_left _ StdR2.NormedAddCommGroup StdR2.InnerProductSpace _ _ _, @real_inner_smul_right _ StdR2.NormedAddCommGroup StdR2.InnerProductSpace _ _ _, @inner_self_eq_norm_sq_to_K _ _ _ StdR2.NormedAddCommGroup StdR2.InnerProductSpace]
    dsimp
    rw [pow_two]
    rw [← mul_assoc _ _ (@norm (ℝ × ℝ) StdR2.NormedAddCommGroup.toNorm x)]
    simp only [ne_eq, inv_mul_mul_self]
    rw [inv_mul_cancel ((@norm_ne_zero_iff _ StdR2.NormedAddGroup).mpr h)]

def UniVec.mk_angle (θ : ℝ) : UniVec where
  vec := (Real.cos θ, Real.sin θ)
  unit := by 
    rw [← Real.cos_sq_add_sin_sq θ]
    rw [pow_two, pow_two]
    rfl

instance : Mul UniVec where
  mul := fun z w => {
    vec := (z.vec.1 * w.vec.1 - z.vec.2 * w.vec.2, z.vec.1 * w.vec.2 + z.vec.2 * w.vec.1)
    unit := by
      unfold Inner.inner StdR2.InnerProductSpace.Core
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

instance : CommGroup UniVec where
  mul := Mul.mul
  mul_assoc := sorry
  one := {
    vec := (1,0)
    unit := by 
      unfold Inner.inner StdR2.InnerProductSpace.Core
      simp
  }
  one_mul := fun a => by
    ext : 1
    unfold UniVec.vec HMul.hMul instHMul Mul.mul Semigroup.toMul instMulUniVec
    simp only
    sorry
  mul_one := sorry
  npow := sorry
  npow_zero := sorry
  npow_succ := sorry
  inv := sorry
  div := sorry
  div_eq_mul_inv := sorry
  zpow := sorry
  zpow_zero' := sorry
  zpow_succ' := sorry
  zpow_neg' := sorry
  mul_left_inv := sorry
  mul_comm := sorry

instance : HasDistribNeg UniVec where
  neg := Neg.neg
  neg_neg := sorry
  neg_mul := sorry
  mul_neg := sorry

end UniVec

end EuclidGeom