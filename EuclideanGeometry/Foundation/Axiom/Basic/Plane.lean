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
class EuclideanPlane (P : Type _) extends MetricSpace P, @NormedAddTorsor Vec P _ _

variable  {P : Type _} [EuclideanPlane P] 

def Vec.mk_pt_pt (A B : P) : (Vec) := (B -ᵥ A)

scoped notation "VEC" => Vec.mk_pt_pt

instance : EuclideanPlane (Vec) where
  toMetricSpace := _
  toNormedAddTorsor := @SeminormedAddCommGroup.toNormedAddTorsor _ _

instance : @NormedAddTorsor (Vec) P _ _ := EuclideanPlane.toNormedAddTorsor

instance : AddTorsor (Vec) P := by infer_instance

/- vector $AB +$ point $A =$ point $B$ -/
@[simp]
theorem start_vadd_vec_eq_end (A B : P) : (VEC A B) +ᵥ A = B := by
   rw[Vec.mk_pt_pt]
   exact vsub_vadd B A

@[simp]
theorem vadd_eq_self_iff_vec_eq_zero {A : P} {v : Vec} : v +ᵥ A = A ↔ v = 0 := by
  constructor
  intro h
  have k:v +ᵥ A -ᵥ A = A-ᵥ A:= by
    rw[h]
  have u:v +ᵥ A -ᵥ A = v:= by
    simp
  rw[u] at k
  simp at k
  exact k
  intro h
  rw[h]
  simp

@[simp]
theorem vec_same_eq_zero (A : P) : VEC A A = 0 := by
  rw[Vec.mk_pt_pt]
  simp

theorem neg_vec (A B : P) : - VEC A B = VEC B A := by
  rw[Vec.mk_pt_pt]
  rw[Vec.mk_pt_pt]
  simp

theorem eq_iff_vec_eq_zero (A B : P) : B = A ↔ VEC A B = 0 := by
  constructor
  intro h
  rw[Vec.mk_pt_pt]
  simp
  exact h
  intro h
  rw[Vec.mk_pt_pt] at h
  simp at h
  exact h

theorem ne_iff_vec_ne_zero (A B : P) : B ≠ A ↔ (VEC A B) ≠ 0 := by
  constructor
  intro h a
  apply h
  rw[Vec.mk_pt_pt] at a
  simp at a
  exact a
  intro h a
  apply h
  rw[Vec.mk_pt_pt]
  simp
  exact a

@[simp]
theorem vec_add_vec (A B C : P) : VEC A B + VEC B C = VEC A C := by
  sorry

@[simp]
theorem vec_of_pt_vadd_pt_eq_vec (A : P) (v : Vec) : (VEC A (v +ᵥ A)) = v := by
  rw[Vec.mk_pt_pt]
  simp

@[simp]
theorem vec_sub_vec (O A B: P) : VEC O B - VEC O A = VEC A B := by
  rw[Vec.mk_pt_pt]
  rw[Vec.mk_pt_pt]
  rw[Vec.mk_pt_pt]
  simp

theorem pt_eq_pt_of_eq_smul_smul {O A B : P} {v : Vec} {tA tB : ℝ} (h : tA = tB) (ha : VEC O A = tA • v) (hb : VEC O B = tB • v) : A = B := by
  have hc : VEC A B = VEC O B - VEC O A := Eq.symm (vec_sub_vec O A B)
  rw [ha, hb, ← sub_smul, Iff.mpr sub_eq_zero (Eq.symm h), zero_smul] at hc
  exact Eq.symm ((eq_iff_vec_eq_zero A B).2 hc)

theorem eq_of_smul_Vec_nd_eq_smul_Vec_nd {v : Vec_nd} {tA tB : ℝ} (e : tA • v.1 = tB • v.1) : tA = tB := by
  
  sorry

end EuclidGeom