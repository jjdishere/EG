import Mathlib.Analysis.InnerProductSpace.PiL2

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

section Vectors

class EuclideanVectorSpace (V : Type _)  extends  NormedAddCommGroup V, InnerProductSpace ℝ V where
  dim_two : FiniteDimensional.finrank ℝ V = 2
  basis : Basis (Fin 2) ℝ V

variable {V : Type _} [h : EuclideanVectorSpace V]

def x_coordinate (v : V) := (Basis.coord h.basis 0).toFun v

def y_coordinate (v : V) := (Basis.coord h.basis 1).toFun v

notation "x("v")" => x_coordinate v
notation "y("v")" => y_coordinate v

theorem eq_of_coord_eq {v₁ : V} {v₂ : V} (hx : x(v₁) = x(v₂)) (hy : y(v₁) = y(v₂)) : v₁ = v₂ := by 
  rw [Basis.ext_elem_iff h.basis, Fin.forall_iff]
  intro i hi
  cases i with 
  | zero => exact hx  
  | succ i' => 
    cases i' with 
    | zero => exact hy
    | succ => linarith

end Vectors

section Plane

class EuclideanPlane (H : Type _) extends MetricSpace H where 
  V : Type _
  VectorSpace : EuclideanVectorSpace V
  toNormedAddTorsor : NormedAddTorsor V H

end Plane

instance EuclideanVectorSpace.toEuclideanPlane (V : Type _) [h : EuclideanVectorSpace V] : EuclideanPlane V where
  V := V
  VectorSpace := h
  toNormedAddTorsor := by infer_instance

end EuclidGeom



