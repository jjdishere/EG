import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean Plane

This file defines the Euclidean Plane as an affine space, admits an action of the standard inner product real vector space of dimension two.

## Important definitions

* `UniVec` : the class of unit vectors in the 2d real vector space
* `EuclideanPlane` : the class of Euclidean Plane

## Notation

## Implementation Notes

For simplicity, we use the standard inner product real vector space of dimension two as the underlying `SeminormedAddCommGroup` of the `NormedAddTorsor` in the definition of `EuclideanPlane`. 

In section `StdR2`, we define all of the sturctures on the standard 2d inner product real vector space `ℝ × ℝ`. We use defs and do NOT use instances here in order to avoid conflicts to existing instance of such stuctures on `ℝ × ℝ` which is based on `L^∞` norm of the product space.

Then we define `EuclideanPlane P` as `NormedAddTorsor (ℝ × ℝ) P` and present instances involving `EuclideanPlane`.

## Further Works

The current definition is far from being general enough. Roughly speaking, it suffices to define the Euclidean Plane to be a `NormedAddTorsor` over any 2 dimensional normed real inner product spaces `V` with a choice of an orientation on `V`.

-/


namespace EuclidGeom

/- structures on `ℝ × ℝ`-/
namespace StdR2

protected noncomputable def AddGroupNorm : AddGroupNorm (ℝ × ℝ) where
  toFun := fun x => Real.sqrt (x.1 * x.1 + x.2 * x.2)
  map_zero' := by simp
  add_le' := fun x y => by 
    simp
    sorry
  neg' := fun _ => by simp
  eq_zero_of_map_eq_zero' := fun x => by 
    simp
    sorry

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
protected noncomputable def NormedAddCommGroup : NormedAddCommGroup (ℝ × ℝ) := AddGroupNorm.toNormedAddCommGroup StdR2.AddGroupNorm

protected noncomputable def InnerProductSpace : @InnerProductSpace ℝ (ℝ × ℝ) _ StdR2.NormedAddCommGroup := InnerProductSpace.ofCore StdR2.InnerProductSpace.Core

protected noncomputable def SeminormedAddCommGroup := @NormedAddCommGroup.toSeminormedAddCommGroup _ (StdR2.InnerProductSpace.Core.toNormedAddCommGroup)

protected noncomputable def MetricSpace := @NormedAddCommGroup.toMetricSpace _ (StdR2.InnerProductSpace.Core.toNormedAddCommGroup)

protected noncomputable def PseudoMetricSpace := @MetricSpace.toPseudoMetricSpace _ StdR2.MetricSpace

protected def toComplex (x : ℝ × ℝ) : ℂ := ⟨x.1, x.2⟩ 

end StdR2

class UniVec where
  vec : ℝ × ℝ 
  unit : StdR2.InnerProductSpace.Core.inner vec vec = 1 

/- Define Euclidean plane as normed vector space over ℝ of dimension 2 -/
class EuclideanPlane (H : Type _) extends MetricSpace H, @NormedAddTorsor (ℝ × ℝ) H StdR2.SeminormedAddCommGroup _

noncomputable instance : EuclideanPlane (ℝ × ℝ) where
  toMetricSpace := StdR2.MetricSpace
  toNormedAddTorsor := @SeminormedAddCommGroup.toNormedAddTorsor _ StdR2.SeminormedAddCommGroup

instance [EuclideanPlane H] : @NormedAddTorsor (ℝ × ℝ) H StdR2.SeminormedAddCommGroup _ := EuclideanPlane.toNormedAddTorsor

instance [EuclideanPlane H] : AddTorsor (ℝ × ℝ) H := by infer_instance

end EuclidGeom





