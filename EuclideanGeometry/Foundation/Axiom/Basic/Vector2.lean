import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
/-!
# Standard Vector Space

This file defines the standard inner product real vector space of dimension two, but we will build this on the complex numbers. 

## Important definitions

* `Vec` : The class of "2d vectors", `ℂ`, with a typical inner product space structure which is NOT instancialized. 
* `Vec_nd` : The class of nonzero vectors, `nd` for nondegenerate. 
* `Dir` : The class of `Vec_nd` quotient by `ℝ⁺`. 
* `Proj` : the class of `Dir` quotient by `±1`, in other words, `ℝP¹` . 

## Notation

## Implementation Notes

Then we define the class `Dir` of vectors of unit length. We equip it with the structure of commutative group. The quotient `Proj` of `Dir` by `±1` is automatically a commutative group.

## Further Works

-/

noncomputable section
namespace EuclidGeom

scoped notation "π" => Real.pi

-- #synth InnerProductSpace ℝ ℂ 
-- InnerProductSpace.complexToReal


/- the notation for the class of vectors -/
scoped notation "Vec" => ℂ 

/- the class of non-degenerate vectors -/
def Vec_nd := {z : ℂ // z ≠ 0}

instance : Coe Vec_nd Vec where
  coe := fun z => z.1

namespace Vec_nd

instance : Mul Vec_nd where
  mul z w := ⟨z * w, mul_ne_zero_iff.2 ⟨z.2, w.2⟩⟩

instance : Semigroup Vec_nd where
  mul_assoc := fun _ _ _ => Subtype.ext (mul_assoc _ _ _)

instance : Monoid Vec_nd where
  one := ⟨1, one_ne_zero⟩
  one_mul := fun _ => Subtype.ext (one_mul _)
  mul_one := fun _ => Subtype.ext (mul_one _)

instance : CommGroup Vec_nd where
  inv := fun z => ⟨z⁻¹, inv_ne_zero z.2⟩
  mul_left_inv := fun z => Subtype.ext (inv_mul_cancel z.2)
  mul_comm := fun z w => Subtype.ext (mul_comm z.1 w.1)

instance : HasDistribNeg Vec_nd where
  neg := fun z => ⟨-z, neg_ne_zero.2 z.2⟩
  neg_neg := fun _ => Subtype.ext (neg_neg _)
  neg_mul := fun _ _ => Subtype.ext (neg_mul _ _)
  mul_neg := fun _ _ => Subtype.ext (mul_neg _ _)

end Vec_nd

def Vec.norm (x : Vec) := Complex.abs x

def Vec_nd.norm (x : Vec_nd) := Complex.abs x

theorem Vec_nd.norm_ne_zero (z : Vec_nd) : Vec_nd.norm z ≠ 0 := norm_ne_zero_iff.2 z.2

theorem Vec_nd.ne_zero_of_ne_zero_smul (z : Vec_nd) {t : ℝ} (h : t ≠ 0) : t • z.1 ≠ 0 := by
  simp only [ne_eq, smul_eq_zero, h, z.2, or_self, not_false_eq_true]

def Vec_nd.normalize' (z : Vec_nd) : Vec_nd := ⟨(Vec_nd.norm z)⁻¹ • z.1, Vec_nd.ne_zero_of_ne_zero_smul z (inv_ne_zero (Vec_nd.norm_ne_zero z))⟩

theorem Vec_nd.ne_zero_of_neg (z : Vec_nd) : - z.1 ≠ 0 := by 
  simp only [ne_eq, neg_eq_zero, z.2, not_false_eq_true]

@[simp]
theorem fst_of_one_toVec_eq_one : (1 : Vec_nd).1 = 1 := rfl

@[simp]
theorem fst_neg_Vec_nd_is_neg_fst_Vec_nd (z : Vec_nd) : (-z).1 = -(z.1) := rfl

@[simp]
theorem ne_zero_of_Vec_nd (z : Vec_nd) : z.1 ≠ 0 := z.2

@[simp]
theorem real_smul_Vec_eq_mul_of (z : Vec) (r : ℝ) : r • z = r * z := rfl

@[simp]
theorem fst_of_mul_eq_fst_mul_fst (z w : Vec_nd) : (z * w).1 = z.1 * w.1 := by rfl

def PScaling : Vec_nd → Vec_nd → Prop :=
  fun z w => ∃ t : ℝ, (0 < t) ∧ (w.1 = t • z.1)

def PScaling.equivalence : Equivalence PScaling where
  refl x := by
    use 1
    simp only [zero_lt_one, ne_eq, one_smul, and_self]
  symm := fun ⟨t, ⟨ht, h⟩⟩ =>
    Exists.intro t⁻¹ ⟨Iff.mpr inv_pos ht, Eq.symm (Iff.mpr (inv_smul_eq_iff₀ (ne_of_gt ht)) h)⟩
  trans h := fun ⟨t, ⟨ht, h₂⟩⟩ => by
    rcases h with ⟨s, ⟨hs, h₁⟩⟩
    use t * s
    simp only [gt_iff_lt, ht, zero_lt_mul_left, hs, ne_eq, h₂, h₁, Complex.real_smul, Complex.ofReal_mul, mul_assoc, and_self]

instance PScaling.con : Con Vec_nd where
  r := PScaling
  iseqv := PScaling.equivalence
  mul' := by
    intro z₁ z₂ w₁ w₂ ⟨s, hs, e₁⟩ ⟨t, ht, e₂⟩
    use s * t
    constructor
    exact (zero_lt_mul_left hs).2 ht
    simp only [ne_eq, fst_of_mul_eq_fst_mul_fst, e₁, Complex.real_smul, e₂, Complex.ofReal_mul]
    ring

def Vec_nd.normalize : Vec_nd →* Vec_nd where
  toFun := Vec_nd.normalize'
  map_one' := by
    apply Subtype.ext
    unfold normalize' norm
    simp only [ne_eq, fst_of_one_toVec_eq_one, map_one, inv_one, one_smul]
  map_mul' x y := by
    apply Subtype.ext
    unfold normalize' norm
    simp only [ne_eq, fst_of_mul_eq_fst_mul_fst, map_mul, mul_inv_rev, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_inv]
    ring

def Dir := Con.Quotient PScaling.con

namespace Dir

instance : MulOneClass Dir := Con.mulOneClass PScaling.con

instance : Group Dir := Con.group PScaling.con

instance : CommMonoid Dir := Con.commMonoid PScaling.con

instance : CommGroup Dir where
  mul_comm := instCommMonoidDir.mul_comm

end Dir

def Vec_nd.toDir (z : Vec_nd) := (⟦z⟧ : Dir)

#check Con.lift

def Dir.toVec_nd  : (Dir →* Vec_nd) := by
  let g := Con.lift PScaling.con Vec_nd.normalize
  exact g sorry
/-

def Proj := Con.Quotient PM.con

-- We can take quotient from Dir to get Proj. 

namespace Proj

instance : MulOneClass Proj := Con.mulOneClass PM.con

instance : Group Proj := Con.group PM.con

instance : CommMonoid Proj := Con.commMonoid PM.con

instance : CommGroup Proj where
  mul_comm := instCommMonoidProj.mul_comm



@[ext]
class Dir where
  toVec : Vec
  unit : Vec.InnerProductSpace.Core.inner toVec toVec= 1

def Vec_nd.normalize (x : Vec_nd) : Dir where
  toVec := (Vec.norm x.1)⁻¹ • x.1
  unit := by 
    rw [@real_inner_smul_left _ Vec.NormedAddCommGroup Vec.InnerProductSpace _ _ _, @real_inner_smul_right _ Vec.NormedAddCommGroup Vec.InnerProductSpace _ _ _, @inner_self_eq_norm_sq_to_K _ _ _ Vec.NormedAddCommGroup Vec.InnerProductSpace]
    dsimp
    rw [pow_two]
    rw [← mul_assoc _ _ (@norm (ℝ × ℝ) Vec.NormedAddCommGroup.toNorm x.1)]
    simp only [Vec.norm, ne_eq, inv_mul_mul_self]
    rw [inv_mul_cancel ((@norm_ne_zero_iff _ Vec.NormedAddGroup).mpr x.2)]

-- Basic facts about Dir, the group structure, neg, and the fact that we can make angle using Dir. There are a lot of relevant (probably easy) theorems under the following namespace. 

namespace Dir

/- the CommGroup instance on `Dir` -/

instance : Neg Dir where
  neg := fun x => {
      toVec := -x.toVec
      unit := by 
        rw [← unit]
        exact @inner_neg_neg _ _ _ Vec.NormedAddCommGroup Vec.InnerProductSpace _ _
    }

instance : Mul Dir where
  mul := fun z w => {
    toVec := Complex.toVec (Vec.toComplex z.toVec * Vec.toComplex w.toVec)
    unit := by
      unfold Inner.inner Vec.InnerProductSpace.Core Complex.toVec Vec.toComplex
      simp
      ring_nf
      calc 
        _ = (z.toVec.1 ^ 2 + z.toVec.2 ^ 2) * (w.toVec.1 ^ 2 + w.toVec.2 ^ 2) := by
          ring
        _ = 1 * 1 := by 
          simp only [pow_two]
          congr 1
          · exact z.unit
          · exact w.unit
        _ = 1 := one_mul 1
  } 

instance : One Dir where
  one := {
    toVec := (1, 0)
    unit := by 
      unfold Inner.inner Vec.InnerProductSpace.Core
      simp
  }

/- Put tautological theorems into simp -/
@[simp]
theorem fst_of_one_eq_one : (1 : Dir).1.fst = 1 := rfl

@[simp]
theorem snd_of_one_eq_zero : (1 : Dir).1.snd = 0 := rfl

@[simp]
theorem one_eq_one_toComplex : Vec.toComplex (1 : Dir).toVec = 1 := rfl

@[simp]
theorem toVec_sq_add_sq_eq_one (x : Dir) : x.toVec.1 ^ 2 + x.toVec.2 ^ 2 = 1 := by
  rw [pow_two, pow_two]
  exact x.unit

-- Give a CommGroup structure to Dir by the mul structure of ℂ

instance : Semigroup Dir where
  mul_assoc _ _ _ := by
    ext : 1
    unfold toVec HMul.hMul instHMul Mul.mul instMulDir Complex.toVec Vec.toComplex
    simp
    ring_nf

instance : Monoid Dir where
  one_mul := fun _ => by
    ext : 1
    unfold toVec HMul.hMul instHMul Mul.mul Semigroup.toMul instSemigroupDir instMulDir
    simp only [Dir.one_eq_one_toComplex, one_mul, eq_self_toComplex_toVec]
    rfl
  mul_one := fun _ => by
    ext : 1
    unfold toVec HMul.hMul instHMul Mul.mul Semigroup.toMul instSemigroupDir instMulDir
    simp only [Dir.one_eq_one_toComplex, mul_one, eq_self_toComplex_toVec]
    rfl

instance : CommGroup Dir where
  inv := fun x => {
    toVec := (x.1.fst, -x.1.snd)
    unit := by
      unfold inner Vec.InnerProductSpace.Core
      simp
      exact x.2
  }
  mul_left_inv _ := by
    ext : 1
    unfold HMul.hMul Inv.inv instHMul Mul.mul Semigroup.toMul Monoid.toSemigroup instMonoidDir instSemigroupDir instMulDir Vec.toComplex Complex.toVec
    simp
    ring_nf
    ext
    simp only [toVec_sq_add_sq_eq_one, Dir.fst_of_one_eq_one]
    simp only [Dir.snd_of_one_eq_zero]
    
  mul_comm _ _ := by
    ext : 1
    unfold toVec HMul.hMul instHMul Mul.mul Semigroup.toMul Monoid.toSemigroup instMonoidDir instSemigroupDir instMulDir
    simp
    ring_nf

instance : HasDistribNeg Dir where
  neg := Neg.neg
  neg_neg _ := by
    unfold Neg.neg instNegDir
    simp
  neg_mul _ _ := by
    ext : 1
    unfold Neg.neg instNegDir toVec HMul.hMul instHMul Mul.mul instMulDir Vec.toComplex Complex.toVec toVec
    simp
    ring_nf
  mul_neg _ _ := by
    ext : 1
    unfold Neg.neg instNegDir toVec HMul.hMul instHMul Mul.mul instMulDir Vec.toComplex Complex.toVec toVec
    simp
    ring_nf

@[simp]
theorem toVec_neg_eq_neg_toVec (x : Dir) : (-x).toVec = -(x.toVec) := by
  ext
  unfold Neg.neg instNegDir toVec Prod.instNeg
  simp only
  unfold Neg.neg instNegDir toVec Prod.instNeg
  simp only

@[simp]
theorem fst_of_neg_one_eq_neg_one : (-1 : Dir).toVec.1 = -1 := rfl

@[simp]
theorem snd_of_neg_one_eq_zero : (-1 : Dir).toVec.2 = 0 := by
  unfold toVec Neg.neg instNegDir
  simp only [Prod.snd_neg, Dir.snd_of_one_eq_zero, neg_zero]

def angle (x y : Dir) := Complex.arg (Vec.toComplex (y * (x⁻¹)).toVec)

theorem fst_of_angle_toVec (x y : Dir) : (y * (x⁻¹)).1.1 = x.1.1 * y.1.1 + x.1.2 * y.1.2 := by
  have h : x.1.1 * y.1.1 + x.1.2 * y.1.2 = y.1.1 * x.1.1 - y.1.2 * (-x.1.2) := by ring
  rw [h]
  rfl

def mk_angle (θ : ℝ) : Dir where
  toVec := (Real.cos θ, Real.sin θ)
  unit := by 
    rw [← Real.cos_sq_add_sin_sq θ]
    rw [pow_two, pow_two]
    rfl

theorem toVec_ne_zero (x : Dir) : x.toVec ≠ 0 := by
  by_contra h
  have h' : Vec.InnerProductSpace.Core.inner x.toVec x.toVec = 0 := by
    rw [h]
    unfold Vec.InnerProductSpace.Core
    simp only [Prod.fst_zero, mul_zero, Prod.snd_zero, add_zero]
  let g := x.unit
  rw [h'] at g
  exact zero_ne_one g

def toVec_nd (x : Dir) : Vec_nd := ⟨x.toVec, toVec_ne_zero x⟩

@[simp]
theorem norm_of_dir_toVec_eq_one (x : Dir) : Vec.norm x.toVec = 1 := by
  exact Iff.mpr Real.sqrt_eq_one x.unit

@[simp]
theorem dir_toVec_nd_normalize_eq_self (x : Dir) : Vec_nd.normalize (⟨x.toVec, toVec_ne_zero x⟩ : Vec_nd) = x := by
  ext : 1
  unfold Vec_nd.normalize
  simp only [norm_of_dir_toVec_eq_one, inv_one, one_smul]

/- The direction `Dir.I`, defined as `(0, 1)`, the direction of y-axis. It will be used in section perpendicular. -/
def I : Dir where
  toVec := (0, 1)
  unit := by
    unfold inner Vec.InnerProductSpace.Core
    simp only [mul_zero, mul_one, zero_add]

@[simp]
theorem fst_of_I_eq_zero : I.1.1 = 0 := rfl

@[simp]
theorem snd_of_I_eq_one : I.1.2 = 1 := rfl

@[simp]
theorem I_toComplex_eq_I : Vec.toComplex I.1 = Complex.I := by
  unfold Vec.toComplex
  ext
  simp only [fst_of_I_eq_zero, Complex.I_re]
  simp only [snd_of_I_eq_one, Complex.I_im]

@[simp]
theorem neg_I_toComplex_eq_neg_I : Vec.toComplex (-I).1 = -Complex.I := by
  ext
  rw [Complex.neg_re Complex.I]
  unfold Vec.toComplex Neg.neg instNegDir
  simp
  exact Eq.symm neg_zero
  simp

@[simp]
theorem I_mul_I_eq_neg_one : I * I = -(1 : Dir) := by
  ext : 1
  unfold HMul.hMul instHMul Mul.mul instMulDir
  simp only [I_toComplex_eq_I, Complex.I_mul_I, toVec_neg_eq_neg_toVec]
  ext
  rfl
  rfl

@[simp]
theorem inv_of_I_eq_neg_I : I⁻¹ = - I := by
  apply @mul_right_cancel _ _ _ _ I _
  simp only [mul_left_inv, neg_mul, I_mul_I_eq_neg_one, neg_neg]

section Make_angle_theorems

@[simp]
theorem mk_angle_arg_toComplex_of_nonzero_eq_normalize (x : Vec_nd) : mk_angle (Complex.arg (Vec.toComplex x.1)) = Vec_nd.normalize x := by
  ext : 1
  unfold Vec_nd.normalize toVec mk_angle HSMul.hSMul instHSMul SMul.smul Prod.smul
  simp
  rw [Vec.norm_eq_abs_toComplex]
  constructor
  · rw [Complex.cos_arg, mul_comm]
    rfl
    intro h
    exact ne_zero_of_Vec_nd_toComplex _ h
  · rw [Complex.sin_arg, mul_comm]
    rfl

@[simp]
theorem mk_angle_arg_toComplex_of_Dir_eq_self (x: Dir) : mk_angle (Complex.arg (Vec.toComplex x.toVec)) = x := by
  have w : Complex.abs (Vec.toComplex x.1) = 1 := by
    unfold toVec Vec.toComplex Complex.abs
    simp only [AbsoluteValue.coe_mk, MulHom.coe_mk, Complex.normSq_mk, Real.sqrt_eq_one]
    exact x.unit
  ext : 1
  unfold mk_angle
  simp
  rw [Complex.cos_arg, Complex.sin_arg, w]
  unfold toVec
  ext : 1
  simp only [re_of_toComplex_eq_fst, div_one]
  simp only [im_of_toComplex_eq_snd, div_one]
  by_contra h
  rw [eq_zero_of_toComplex_eq_zero h] at w
  simp only [toComplex_zero_eq_zero, map_zero, zero_ne_one] at w 

@[simp]
theorem mk_angle_zero_eq_one : mk_angle 0 = 1 := by
  unfold mk_angle
  ext
  simp only [Real.cos_zero, Real.sin_zero, Dir.fst_of_one_eq_one]
  simp only [Real.cos_zero, Real.sin_zero, Dir.snd_of_one_eq_zero]

@[simp]
theorem mk_angle_pi_eq_neg_one : mk_angle π = -1 := by
  unfold mk_angle
  ext
  simp only [Real.cos_pi, Real.sin_pi, toVec_neg_eq_neg_toVec, Prod.fst_neg, Dir.fst_of_one_eq_one]
  simp only [Real.cos_pi, Real.sin_pi, toVec_neg_eq_neg_toVec, Prod.snd_neg, Dir.snd_of_one_eq_zero, neg_zero]

@[simp]
theorem mk_angle_neg_pi_eq_neg_one : mk_angle (-π) = -1 := by
  unfold mk_angle
  ext
  simp only [Real.cos_neg, Real.cos_pi, Real.sin_neg, Real.sin_pi, neg_zero, toVec_neg_eq_neg_toVec, Prod.fst_neg,
    Dir.fst_of_one_eq_one]
  simp only [Real.cos_neg, Real.cos_pi, Real.sin_neg, Real.sin_pi, neg_zero, toVec_neg_eq_neg_toVec, Prod.snd_neg,
    Dir.snd_of_one_eq_zero]

theorem mk_angle_neg_mul_mk_angle_eq_one (x : ℝ) : mk_angle (-x) * mk_angle x = 1 := by
  ext
  unfold toVec mk_angle HMul.hMul instHMul Mul.mul instMulDir Vec.toComplex Complex.toVec
  simp only [Real.cos_neg, Real.sin_neg, Complex.mul_re, neg_mul, sub_neg_eq_add]
  rw [← pow_two, ← pow_two, Real.cos_sq_add_sin_sq x]
  rfl
  unfold toVec mk_angle HMul.hMul instHMul Mul.mul instMulDir Vec.toComplex Complex.toVec
  simp only [Real.cos_neg, Real.sin_neg, Complex.mul_im, neg_mul]
  rw [mul_comm, add_right_neg]
  rfl

@[simp]
theorem mk_angle_neg_eq_mk_angle_inv (x : ℝ) : mk_angle (-x) = (mk_angle x)⁻¹ := by
  rw [← one_mul (mk_angle x)⁻¹, ← mk_angle_neg_mul_mk_angle_eq_one x, mul_assoc, mul_right_inv, mul_one]

@[simp]
theorem mk_angle_pi_div_two_eq_I : mk_angle (π / 2) = I := by
  unfold mk_angle
  ext
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, fst_of_I_eq_zero]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, snd_of_I_eq_one]

@[simp]
theorem mk_angle_neg_pi_div_two_eq_neg_I : mk_angle (-(π / 2)) = -I := by
  unfold mk_angle
  ext
  simp only [Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two, toVec_neg_eq_neg_toVec, Prod.fst_neg,
    fst_of_I_eq_zero, neg_zero]
  simp only [Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two, toVec_neg_eq_neg_toVec, Prod.snd_neg,
    snd_of_I_eq_one]

@[simp]
theorem mk_angle_neg_pi_div_two_eq_neg_I' : mk_angle ((-π) / 2) = -I := by
  rw [neg_div]
  simp only [mk_angle_neg_pi_div_two_eq_neg_I]

end Make_angle_theorems

end Dir

def PM : Dir → Dir → Prop :=
fun x y => x = y ∨ x = -y

-- Now define the equivalence PM. 

namespace PM

def equivalence : Equivalence PM where
  refl _ := by simp [PM]
  symm := fun h => 
    match h with
      | Or.inl h₁ => Or.inl (Eq.symm h₁)
      | Or.inr h₂ => Or.inr (Iff.mp neg_eq_iff_eq_neg (id (Eq.symm h₂)))
  trans := by
    intro _ _ _ g h
    unfold PM
    match g with
      | Or.inl g₁ => 
          rw [← g₁] at h
          exact h
      | Or.inr g₂ => 
          match h with
            | Or.inl h₁ =>
              right
              rw [← h₁, g₂]
            | Or.inr h₂ =>
              left
              rw [g₂, h₂, ← Iff.mp neg_eq_iff_eq_neg rfl]

instance con : Con Dir where
  r := PM
  iseqv := PM.equivalence
  mul' := by
    unfold Setoid.r PM
    intro _ x _ z g h
    match g with
      | Or.inl g₁ => 
        match h with
          | Or.inl h₁ =>
            left
            rw [g₁, h₁]
          | Or.inr h₂ =>
            right
            rw [g₁, h₂, ← mul_neg _ _]
      | Or.inr g₂ => 
        match h with
          | Or.inl h₁ =>
            right
            rw [g₂, h₁, ← neg_mul _ _]
          | Or.inr h₂ =>
            left
            rw[g₂, h₂, ← neg_mul_neg x z]

end PM

def Proj := Con.Quotient PM.con

-- We can take quotient from Dir to get Proj. 

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

def Vec_nd.toProj (v : Vec_nd) : Proj := (Vec_nd.normalize v : Proj) 

-- Coincidence of toProj gives rise to important results, especially that two Vec_nd-s have the same toProj iff they are equal by taking a real (nonzero) scaler. We will prove this statement in the following section. 

section Vec_nd_toProj

theorem normalize_eq_normalize_smul_pos (u v : Vec_nd) {t : ℝ} (h : v.1 = t • u.1) (ht : 0 < t) : Vec_nd.normalize u = Vec_nd.normalize v := by
  ext : 1
  unfold Vec_nd.normalize Dir.toVec
  simp only [ne_eq]
  have hv₁ : Vec.norm v.1 ≠ 0 := Iff.mpr (@norm_ne_zero_iff _ Vec.NormedAddGroup v.1) v.2
  have g : (Vec.norm v.1) • u.1 = (Vec.norm u.1) • v.1 := by
    have w₁ : (Vec.norm (t • u.1)) = ‖t‖ * (Vec.norm u.1) := @norm_smul _ _ _ Vec.SeminormedAddGroup _ Vec.BoundedSMul t u.1
    have w₂ : ‖t‖ = t := abs_of_pos ht
    rw [h, w₁, w₂, mul_comm]
    exact mul_smul (Vec.norm u.1) t u.1
  have g₁ : (Vec.norm u.1)⁻¹ • (Vec.norm v.1) • u.1 = v.1 := Iff.mpr (inv_smul_eq_iff₀ (Iff.mpr (@norm_ne_zero_iff _ Vec.NormedAddGroup _) u.2)) g
  rw [smul_algebra_smul_comm _ _ _] at g₁
  rw [← Iff.mpr (inv_smul_eq_iff₀ hv₁) (Eq.symm g₁)]

theorem neg_normalize_eq_normalize_smul_neg (u v : Vec_nd) {t : ℝ} (h : v.1 = t • u.1) (ht : t < 0) : -Vec_nd.normalize u = Vec_nd.normalize v := by
  ext : 1
  unfold Vec_nd.normalize
  simp only [ne_eq, Dir.toVec_neg_eq_neg_toVec]
  have g : (-Vec.norm v.1) • u.1 = (Vec.norm u.1) • v.1 := by
    have w₁ : (Vec.norm (t • u.1)) = ‖t‖ * (Vec.norm u.1) := @norm_smul _ _ _ Vec.SeminormedAddGroup _ Vec.BoundedSMul t u.1
    have w₂ : ‖t‖ = -t := abs_of_neg ht
    rw [h, w₁, w₂, neg_mul, neg_neg, mul_comm]
    exact mul_smul (Vec.norm u.1) t u.1
  have g₁ : (Vec.norm u.1)⁻¹ • (-Vec.norm v.1) • u.1 = v.1 := (Iff.mpr (inv_smul_eq_iff₀ (Iff.mpr (@norm_ne_zero_iff _ Vec.NormedAddGroup _) u.2)) g)
  rw [smul_algebra_smul_comm _ _ _] at g₁
  rw [neg_eq_iff_eq_neg, ← neg_smul _ _, ← inv_neg, ← Iff.mpr (inv_smul_eq_iff₀ (Iff.mpr neg_ne_zero (Iff.mpr (@norm_ne_zero_iff _ Vec.NormedAddGroup _) v.2))) (Eq.symm g₁)]

theorem eq_toProj_of_smul (u v : Vec_nd) {t : ℝ} (h : v.1 = t • u.1) : Vec_nd.toProj u = Vec_nd.toProj v := by
  have ht : t ≠ 0 := by
    by_contra ht'
    rw [ht', zero_smul ℝ u.1] at h
    exact v.2 h
  have ht₁ : (0 < t) ∨ (t < 0) := Ne.lt_or_lt (Ne.symm ht)
  unfold Vec_nd.toProj Dir.toProj
  apply Quotient.sound
  unfold HasEquiv.Equiv instHasEquiv PM.con PM
  simp only [Con.rel_eq_coe, Con.rel_mk]
  match ht₁ with
    | Or.inl ht₂ =>
      left
      exact normalize_eq_normalize_smul_pos u v h ht₂
    | Or.inr ht₃ =>
      right
      exact Iff.mp neg_eq_iff_eq_neg (neg_normalize_eq_normalize_smul_neg u v h ht₃)

theorem smul_of_eq_toProj (u v : Vec_nd) (h : Vec_nd.toProj u = Vec_nd.toProj v) : ∃ (t : ℝ), v.1 = t • u.1 := by
  let h' := Quotient.exact h
  unfold HasEquiv.Equiv instHasEquiv PM.con PM at h'
  simp only [Con.rel_eq_coe, Con.rel_mk] at h' 
  match h' with
    | Or.inl h₁ =>
      rw [Dir.ext_iff] at h₁
      use (Vec.norm v.1) * (Vec.norm u.1)⁻¹
      have w₁ : (Vec.norm v.1)⁻¹ • v.1 = (Vec.norm u.1)⁻¹ • u.1 ↔ v.1 = (Vec.norm v.1) • (Vec.norm u.1)⁻¹ • u.1 := inv_smul_eq_iff₀ (Iff.mpr (@norm_ne_zero_iff _ Vec.NormedAddGroup v.1) v.2)
      rw [mul_smul]
      exact (w₁.mp (Eq.symm h₁))
    | Or.inr h₂ =>
      rw [Dir.ext_iff] at h₂
      use (-Vec.norm v.1) * (Vec.norm u.1)⁻¹
      have w₂ : (-Vec.norm v.1)⁻¹ • v.1 = (Vec.norm u.1)⁻¹ • u.1 ↔ v.1 = (-Vec.norm v.1) • (Vec.norm u.1)⁻¹ • u.1 := inv_smul_eq_iff₀ (Iff.mpr neg_ne_zero (Iff.mpr (@norm_ne_zero_iff _ Vec.NormedAddGroup v.1) v.2))
      rw [mul_smul]
      refine (w₂.mp (Eq.symm ?_))
      rw [← neg_inv, neg_smul]
      exact h₂

-- The main theorem of Vec_nd.toProj
theorem Vec_nd.eq_toProj_iff (u v : Vec_nd) : (Vec_nd.toProj u = Vec_nd.toProj v) ↔ ∃ (t : ℝ), v.1 = t • u.1 := by
  constructor
  · intro h
    exact smul_of_eq_toProj _ _ h
  · intro h'
    rcases h' with ⟨t, h⟩ 
    exact eq_toProj_of_smul _ _ h

end Vec_nd_toProj

section Perpendicular

namespace Proj

def I : Proj := Dir.I

@[simp]
theorem neg_one_eq_one_of_Proj : ((-1 : Dir) : Proj) = (1 : Proj) := by
  unfold Dir.toProj
  apply Quotient.sound
  unfold HasEquiv.Equiv instHasEquiv PM.con PM
  simp only [Con.rel_eq_coe, Con.rel_mk, or_true]

@[simp]
theorem I_mul_I_eq_one_of_Proj : I * I = 1 := by
  have h : Dir.toProj (Dir.I * Dir.I) = (Dir.toProj Dir.I) * (Dir.toProj Dir.I):= rfl
  have h' : Dir.toProj Dir.I = (I : Proj) := rfl
  rw [← neg_one_eq_one_of_Proj, ← Dir.I_mul_I_eq_neg_one, h, h']

def perp : Proj → Proj := fun x => I * x

@[simp]
theorem perp_perp_eq_self (x : Proj) : x.perp.perp = x := by
  unfold perp
  rw [← mul_assoc]
  simp only [I_mul_I_eq_one_of_Proj, one_mul]

end Proj

end Perpendicular

-- Our aim is to prove the Cosine value of the angle of two Vec_nd-s, their norm and inner product satisfy THE EQUALITY. We will use this to prove the Cosine theorem of Triangle, which is in the file Trigonometric

section Cosine_theorem_for_Vec_nd

theorem Vec_nd.norm_smul_normalize_eq_self (v : Vec_nd) : Vec.norm v.1 • (Vec_nd.normalize v).toVec = v := by
  symm
  apply (inv_smul_eq_iff₀ (Iff.mpr (@norm_ne_zero_iff _ Vec.NormedAddGroup v.1) v.2)).1
  rfl

def Vec_nd.angle (v₁ v₂ : Vec_nd) := Dir.angle (Vec_nd.normalize v₁) (Vec_nd.normalize v₂)

theorem cos_arg_of_dir_eq_fst (x : Dir) : Real.cos (Complex.arg (Vec.toComplex x.1)) = x.1.1 := by
  have w₁ : (Dir.mk_angle (Complex.arg (Vec.toComplex x.1))).1.1 = Real.cos (Complex.arg (Vec.toComplex x.1)) := rfl
  simp only [← w₁, Dir.mk_angle_arg_toComplex_of_Dir_eq_self]

/-
theorem sin_arg_of_dir_eq_fst (x : Dir) : Real.sin (Complex.arg (Vec.toComplex x.1)) = x.1.2 := by
  have w₁ : (Dir.mk_angle (Complex.arg (Vec.toComplex x.1))).1.2 = Real.sin (Complex.arg (Vec.toComplex x.1)) := rfl
  simp only [← w₁, Dir.mk_angle_arg_toComplex_of_Dir_eq_self]
-/

theorem cos_angle_of_dir_dir_eq_inner (d₁ d₂ : Dir) : Real.cos (Dir.angle d₁ d₂) = Vec.InnerProductSpace.Core.inner d₁.1 d₂.1 := by
  unfold Dir.angle
  rw [cos_arg_of_dir_eq_fst]
  exact (Dir.fst_of_angle_toVec d₁ d₂)

theorem norm_mul_norm_mul_cos_angle_eq_inner_of_Vec_nd (v₁ v₂ : Vec_nd) : (Vec.norm v₁) * (Vec.norm v₂) * Real.cos (Vec_nd.angle v₁ v₂) = Vec.InnerProductSpace.Core.inner v₁.1 v₂.1 := by
  nth_rw 2 [← Vec_nd.norm_smul_normalize_eq_self v₁, ← Vec_nd.norm_smul_normalize_eq_self v₂]
  rw [Vec.InnerProductSpace.Core.inner_smul_left, Vec.InnerProductSpace.Core.inner_smul_right, ← cos_angle_of_dir_dir_eq_inner, mul_assoc]
  rfl

theorem perp_iff_angle_eq_pi_div_two_or_angle_eq_neg_pi_div_two (v₁ v₂ : Vec_nd) : v₁.toProj = v₂.toProj.perp ↔ (Vec_nd.angle v₁ v₂ = π / 2) ∨ (Vec_nd.angle v₁ v₂ = -(π / 2)) := by
  let d₁ := Vec_nd.normalize v₁
  let d₂ := Vec_nd.normalize v₂
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
  · have w : Dir.mk_angle (Dir.angle d₁ d₂) = Dir.mk_angle (π / 2) := by
      rw [h]
    unfold Dir.angle at w
    simp only [Dir.mk_angle_arg_toComplex_of_Dir_eq_self, Dir.mk_angle_pi_div_two_eq_I] at w
    unfold Vec_nd.toProj Proj.perp
    have e : Vec_nd.normalize v₂ = d₂ := rfl
    have e' : d₂ = Dir.I * d₁ := by
      exact eq_mul_of_div_eq w
    have e'' : Dir.toProj (Dir.I * d₁) = Proj.I * d₁.toProj := rfl
    rw [e, e', e'', ← mul_assoc]
    simp only [Proj.I_mul_I_eq_one_of_Proj, one_mul]
  · have w : Dir.mk_angle (Dir.angle d₁ d₂) = Dir.mk_angle (-(π / 2)) := by
      have w' : Dir.angle d₁ d₂ = -(π / 2) := by tauto
      rw [w']
    unfold Dir.angle at w
    simp only [Dir.mk_angle_arg_toComplex_of_Dir_eq_self, Dir.mk_angle_neg_eq_mk_angle_inv,
      Dir.mk_angle_pi_div_two_eq_I, Dir.inv_of_I_eq_neg_I] at w
    unfold Vec_nd.toProj Proj.perp
    have e : Vec_nd.normalize v₁ = d₁ := rfl
    have e' : d₁ = Dir.I * d₂ := by
      rw [← Dir.inv_of_I_eq_neg_I] at w
      exact eq_mul_of_inv_mul_eq (mul_eq_of_eq_div (Eq.symm w))
    rw [e, e']
    rfl

end Cosine_theorem_for_Vec_nd

-- Our aim is to prove nonparallel lines have common point, but in this section, we will only form the theorem in a Linear algebraic way by proving two Vec_nd-s could span the space with different toProj, which is the main theorem about toProj we will use in the proof of the intersection theorem. 

section Linear_Algebra

theorem det_eq_zero_iff_eq_smul (u v : ℝ × ℝ) (hu : u ≠ 0) : u.1 * v.2 - u.2 * v.1 = 0 ↔ (∃ (t : ℝ), v = t • u) := by
  have h : (u.fst ≠ 0) ∨ (u.snd ≠ 0) := by
    by_contra _
    have h₁ : u.fst = 0 := by tauto
    have h₂ : u.snd = 0 := by tauto
    have hu' : u = (0, 0) := by exact Prod.ext h₁ h₂
    tauto
  constructor
  · intro e
    match h with 
    | Or.inl h₁ =>
      use v.fst * (u.fst⁻¹)
      unfold HSMul.hSMul instHSMul SMul.smul Prod.smul
      ext
      simp only [smul_eq_mul, ne_eq]
      exact Iff.mp (div_eq_iff h₁) rfl
      simp only [smul_eq_mul]
      rw [mul_comm v.fst u.fst⁻¹, mul_assoc, mul_comm v.fst u.snd]
      rw [sub_eq_zero] at e
      exact Iff.mpr (eq_inv_mul_iff_mul_eq₀ h₁) e
    | Or.inr h₂ =>
      use v.snd * (u.snd⁻¹)
      unfold HSMul.hSMul instHSMul SMul.smul Prod.smul
      ext
      simp only [smul_eq_mul]
      rw [mul_comm v.snd u.snd⁻¹, mul_assoc]
      rw [sub_eq_zero, mul_comm u.fst v.snd] at e
      exact Iff.mpr (eq_inv_mul_iff_mul_eq₀ h₂) (id (Eq.symm e))
      simp only [smul_eq_mul, ne_eq]
      exact Iff.mp (div_eq_iff h₂) rfl
  · intro e'
    rcases e' with ⟨t, e⟩
    unfold HSMul.hSMul instHSMul SMul.smul Prod.smul at e
    simp only [smul_eq_mul] at e 
    rcases e
    ring

theorem linear_combination_of_not_colinear {u v w : ℝ × ℝ} (hu : u ≠ 0) (h' : ¬(∃ (t : ℝ), v = t • u)) : ∃ (cu cv : ℝ), w = cu • u + cv • v := by
  have h₁ : (¬ (∃ (t : ℝ), v = t • u)) → (¬ (u.1 * v.2 - u.2 * v.1 = 0)) := by
    intro _
    by_contra h₂
    let _ := (det_eq_zero_iff_eq_smul u v hu).1 h₂
    tauto
  let d := u.1 * v.2 - u.2 * v.1
  have h₃ : d ≠ 0 := h₁ h'
  use d⁻¹ * (w.1 * v.2 - v.1 * w.2) 
  use d⁻¹ * (u.1 * w.2 - w.1 * u.2)
  symm
  rw [mul_smul, mul_smul, ← smul_add]
  apply ((inv_smul_eq_iff₀ h₃).2)
  unfold HSMul.hSMul instHSMul SMul.smul MulAction.toSMul Prod.mulAction Prod.smul
  ext
  simp only [smul_eq_mul, Prod.mk_add_mk]
  ring
  simp only [smul_eq_mul, Prod.mk_add_mk]
  ring

theorem linear_combination_of_not_colinear' {u v : Vec_nd} (w : ℝ × ℝ) (h' : Vec_nd.toProj u ≠ Vec_nd.toProj v) : ∃ (cᵤ cᵥ : ℝ), w = cᵤ • u.1 + cᵥ • v.1 := by
  have h₁ : (Vec_nd.toProj u ≠ Vec_nd.toProj v) → ¬(∃ (t : ℝ), v.1 = t • u.1) := by
    intro _
    by_contra h₂
    let _ := (Vec_nd.eq_toProj_iff u v).2 h₂
    tauto
  exact linear_combination_of_not_colinear u.2 (h₁ h')

end Linear_Algebra
-/

end EuclidGeom