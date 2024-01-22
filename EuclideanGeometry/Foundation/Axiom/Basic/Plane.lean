import EuclideanGeometry.Foundation.Axiom.Basic.Vector

/-!
# Euclidean Plane

This file defines the Euclidean Plane as an affine space, which admits an action of the standard inner product real vector space of dimension two.

## Important definitions

* `EuclideanPlane` : the class of Euclidean Plane

## Notation

* `VEC A B` : the vector `B -ᵥ A` in `Vec`

## Implementation Notes

For simplicity, we use the standard inner product real vector space of dimension two as the underlying `SeminormedAddCommGroup` of the `NormedAddTorsor` in the definition of `EuclideanPlane`.

Thus we define `EuclideanPlane P` as `NormedAddTorsor (ℝ × ℝ) P` and present instances involving `EuclideanPlane`.

## Further Works

The current definition is far from being general enough. Roughly speaking, it suffices to define the Euclidean Plane to be a `NormedAddTorsor` over any 2 dimensional normed real inner product spaces `V` with a choice of an orientation on `V`, rather than over the special `ℝ × ℝ`. All further generalizations in this file should be done together with Vector.lean.

-/

noncomputable section
namespace EuclidGeom

/- Define Euclidean plane as normed vector space over ℝ of dimension 2 -/
class EuclideanPlane (P : Type*) extends MetricSpace P, NormedAddTorsor Vec P

variable {P : Type*} [EuclideanPlane P]

def Vec.mkPtPt (A B : P) : Vec := (B -ᵥ A)

scoped notation "VEC" => Vec.mkPtPt

/- vector $AB +$ point $A =$ point $B$ -/
@[simp]
theorem start_vadd_vec_eq_end (A B : P) : VEC A B +ᵥ A = B := vsub_vadd B A

@[simp]
theorem vadd_eq_self_iff_vec_eq_zero {A : P} {v : Vec} : v +ᵥ A = A ↔ v = 0 := by
  rw [eq_comm, eq_vadd_iff_vsub_eq, vsub_self, eq_comm]

@[simp]
theorem vec_same_eq_zero (A : P) : VEC A A = 0 := by
  rw [Vec.mkPtPt, vsub_self]

@[simp]
theorem neg_vec (A B : P) : - VEC A B = VEC B A := by
  rw [Vec.mkPtPt, Vec.mkPtPt, neg_vsub_eq_vsub_rev]

@[simp]
theorem neg_vec_norm_eq (A B : P) : ‖- VEC A B‖ = ‖VEC A B‖ := by
  rw [norm_neg]

theorem vec_norm_eq_rev (A B : P) : ‖VEC A B‖ = ‖VEC B A‖ := by
  rw [← neg_vec, neg_vec_norm_eq]

theorem eq_iff_vec_eq_zero {A B : P} : B = A ↔ VEC A B = 0 := vsub_eq_zero_iff_eq.symm

theorem ne_iff_vec_ne_zero {A B : P} : B ≠ A ↔ VEC A B ≠ 0 := eq_iff_vec_eq_zero.not

@[simp]
theorem vec_add_vec (A B C : P) : VEC A B + VEC B C = VEC A C := by
  rw [add_comm, Vec.mkPtPt, Vec.mkPtPt, Vec.mkPtPt, vsub_add_vsub_cancel]

@[simp]
theorem vec_of_pt_vadd_pt_eq_vec (A : P) (v : Vec) : VEC A (v +ᵥ A) = v := vadd_vsub v A

@[simp]
theorem vec_of_vadd_pt_pt_eq_neg_vec (A : P) (v : Vec) : VEC (v +ᵥ A) A = - v := by
  rw [← neg_vec]
  congr
  exact vec_of_pt_vadd_pt_eq_vec _ _

@[simp]
theorem vec_sub_vec (O A B: P) : VEC O B - VEC O A = VEC A B := by
  rw [Vec.mkPtPt, Vec.mkPtPt, Vec.mkPtPt, vsub_sub_vsub_cancel_right]

@[simp]
theorem vec_sub_vec' (O A B: P) : VEC A O - VEC B O = VEC A B := by
  rw [Vec.mkPtPt, Vec.mkPtPt, Vec.mkPtPt, vsub_sub_vsub_cancel_left]

theorem pt_eq_pt_of_eq_smul_smul {O A B : P} {v : Vec} {tA tB : ℝ} (h : tA = tB) (ha : VEC O A = tA • v) (hb : VEC O B = tB • v) : A = B := by
  have hc : VEC A B = VEC O B - VEC O A := (vec_sub_vec O A B).symm
  rw [ha, hb, ← sub_smul, Iff.mpr sub_eq_zero h.symm, zero_smul] at hc
  exact (eq_iff_vec_eq_zero.2 hc).symm


def VecND.mkPtPt (A B : P) (h : B ≠ A) : VecND := ⟨Vec.mkPtPt A B, ne_iff_vec_ne_zero.mp h⟩

@[inherit_doc VecND.mkPtPt]
scoped syntax "VEC_nd" ws term:max ws term:max (ws term:max)? : term

macro_rules
  | `(VEC_nd $A $B) => `(VecND.mkPtPt $A $B (@Fact.out _ inferInstance))
  | `(VEC_nd $A $B $h) => `(VecND.mkPtPt $A $B $h)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `VecND.mkPtPt` -/
@[delab app.EuclidGeom.VecND.mkPtPt]
def delabVecNDMkPtPt : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``VecND.mkPtPt 5
  let A ← withNaryArg 2 delab
  let B ← withNaryArg 3 delab
  withNaryArg 4 do
    if (← getExpr).isAppOfArity' ``Fact.out 2 then
      `(VEC_nd $A $B)
    else
      `(VEC_nd $A $B $(← delab))

@[simp]
lemma VecND.coe_mkPtPt (A B : P) [_h : Fact (B ≠ A)] : VEC_nd A B = VEC A B := rfl

@[simp low]
theorem VecND.neg_vecND (A B : P) [_h : Fact (B ≠ A)] : (- VEC_nd A B)= VEC_nd B A _h.1.symm := by
  haveI : Fact (A ≠ B) := ⟨_h.1.symm⟩
  ext
  simp only [ne_eq, RayVector.coe_neg, coe_mkPtPt, neg_vec]

end EuclidGeom
