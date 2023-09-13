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
class EuclideanPlane (H : Type _) extends MetricSpace H, @NormedAddTorsor (Vec) H Vec.SeminormedAddCommGroup _

def Vec.mk_pt_pt {H : Type _} [EuclideanPlane H] (A B : H) : (Vec) := (B -ᵥ A)

scoped notation "VEC" => Vec.mk_pt_pt

instance : EuclideanPlane (Vec) where
  toMetricSpace := Vec.MetricSpace
  toNormedAddTorsor := @SeminormedAddCommGroup.toNormedAddTorsor _ Vec.SeminormedAddCommGroup

instance {H : Type _} [EuclideanPlane H] : @NormedAddTorsor (Vec) H Vec.SeminormedAddCommGroup _ := EuclideanPlane.toNormedAddTorsor

instance {H : Type _} [EuclideanPlane H] : AddTorsor (Vec) H := by infer_instance

@[simp]
theorem start_vadd_vec_eq_end {H : Type _} [EuclideanPlane H] (A B : H) : (VEC A B) +ᵥ A = B := sorry

@[simp]
theorem vadd_eq_self_iff_vec_eq_zero {H : Type _} [EuclideanPlane H] {A : H} {v : Vec} : v +ᵥ A = A ↔ v = 0 := sorry

@[simp]
theorem vec_same_eq_zero {H : Type _} [EuclideanPlane H] (A : H) : VEC A A = 0 := sorry

theorem neg_vec {H : Type _} [EuclideanPlane H] (A B : H) : - VEC A B = VEC B A := sorry

theorem eq_iff_vec_eq_zero {H : Type _} [EuclideanPlane H] (A B : H) : B = A ↔ VEC A B = 0 := sorry

theorem ne_iff_vec_ne_zero {H : Type _} [EuclideanPlane H] (A B : H) : B ≠ A ↔ (VEC A B) ≠ 0 := sorry

@[simp]
theorem vec_add_vec {H : Type _} [EuclideanPlane H] (A B C : H) : VEC A B + VEC B C = VEC A C := sorry

@[simp]
theorem vec_of_pt_vadd_pt_eq_vec {H : Type _} [EuclideanPlane H] (A : H) (v : Vec) : (VEC A (v +ᵥ A)) = v := sorry

@[simp]
theorem vec_sub_vec {H : Type _} [EuclideanPlane H] (O A B: H) : VEC O B - VEC O A = VEC A B := sorry

end EuclidGeom