import Mathlib.Analysis.InnerProductSpace.PiL2
import EuclideanGeometry.Foundation.Axiom.Vector

/-!
# Euclidean Plane

This file defines the Euclidean Plane as an affine space, which admits an action of the standard inner product real vector space of dimension two.

## Important definitions

* `EuclideanPlane` : the class of Euclidean Plane

## Notation

* `Vec A B` : the vector in `ℝ × ℝ` from `A` to `B`

## Implementation Notes

For simplicity, we use the standard inner product real vector space of dimension two as the underlying `SeminormedAddCommGroup` of the `NormedAddTorsor` in the definition of `EuclideanPlane`. 

Thus we define `EuclideanPlane P` as `NormedAddTorsor (ℝ × ℝ) P` and present instances involving `EuclideanPlane`.

## Further Works

The current definition is far from being general enough. Roughly speaking, it suffices to define the Euclidean Plane to be a `NormedAddTorsor` over any 2 dimensional normed real inner product spaces `V` with a choice of an orientation on `V`, rather than over the special `ℝ × ℝ`. All further generalizations in this file should be done together with Vector.lean.

-/

noncomputable section
namespace EuclidGeom
    
/- Define Euclidean plane as normed vector space over ℝ of dimension 2 -/
class EuclideanPlane (H : Type _) extends MetricSpace H, @NormedAddTorsor (ℝ × ℝ) H StdR2.SeminormedAddCommGroup _

def Vec {H : Type _} [EuclideanPlane H] (A B : H) : (ℝ × ℝ) := (B -ᵥ A)

instance : EuclideanPlane (ℝ × ℝ) where
  toMetricSpace := StdR2.MetricSpace
  toNormedAddTorsor := @SeminormedAddCommGroup.toNormedAddTorsor _ StdR2.SeminormedAddCommGroup

instance [EuclideanPlane H] : @NormedAddTorsor (ℝ × ℝ) H StdR2.SeminormedAddCommGroup _ := EuclideanPlane.toNormedAddTorsor

instance [EuclideanPlane H] : AddTorsor (ℝ × ℝ) H := by infer_instance

theorem start_vadd_vec_eq_end {H : Type _} [EuclideanPlane H] (A B : H) : (Vec A B) +ᵥ A = B := sorry

end EuclidGeom





