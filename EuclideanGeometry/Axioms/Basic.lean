import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Euclidean Plane

This file defines the Euclidean Plane as an affine space, admits an action of an inner product real vector space of dimension two equipped with a basis.

## Important definitions

* `EuclideanPlane` : the class of Euclidean Plane
* `x_coordinate` : the x coordiante of a point
* `y_coordinate` : the y coordiante of a point

## Notation

We introduce the notation `x(p)`, `y(p)` for the x,y coordinates of a point `p` on a Euclidean Plane.

## Implementation Notes

## Further Works

-/


/- Define Euclidean plane as normed vector space over ℝ of dimension 2 -/
namespace EuclidGeom

-- class Cartesian2dVectorSpace (V : Type _)  extends  NormedAddCommGroup V, InnerProductSpace ℝ V where
--   dim_two : FiniteDimensional.finrank ℝ V = 2
--   basis : Basis (Fin 2) ℝ V
--   orthonormal : Orthonormal ℝ basis

-- variable {V : Type _} [h : Cartesian2dVectorSpace V]

-- def x_coordinate (v : V) := (Basis.coord h.basis 0).toFun v

-- def y_coordinate (v : V) := (Basis.coord h.basis 1).toFun v

-- notation "x("v")" => x_coordinate v
-- notation "y("v")" => y_coordinate v

-- theorem eq_of_coord_eq {v₁ : V} {v₂ : V} (hx : x(v₁) = x(v₂)) (hy : y(v₁) = y(v₂)) : v₁ = v₂ := by 
--   rw [Basis.ext_elem_iff h.basis, Fin.forall_iff]
--   intro i hi
--   cases i with 
--   | zero => exact hx  
--   | succ i' => 
--     cases i' with 
--     | zero => exact hy
--     | succ => linarith

-- /- theorem norm v = sqrt x(v)^2 + y(v)^2-/
-- noncomputable def vector_of_coord (x : ℝ) (y : ℝ) : V := x • (h.basis 0) + y • (h.basis 1)

-- notation "v("x"," y ")" => vector_of_coord x y
-- theorem eq (x : ℝ) (y : ℝ) : x(v(x, y)) = x := sorry
-- #check ℝ × ℝ 
-- variable (v : ℝ × ℝ)

instance : NormedAddCommGroup (ℝ × ℝ)  := by infer_instance

-- #check v.2
-- #check ((0 : ℝ), (1 : ℝ))

class UniVec where
  vec : ℝ × ℝ 
  unit : NormedAddCommGroup.toNorm.norm vec = 1 



class EuclideanPlane (H : Type _) extends MetricSpace H, NormedAddTorsor (ℝ × ℝ) H

-- instance EuclideanPlanetoVAdd {P : Type _} [h : EuclideanPlane P]: VAdd (ℝ × ℝ) P := by infer_instance


instance : EuclideanPlane (ℝ × ℝ) where
  toNormedAddTorsor := by infer_instance

end EuclidGeom





