import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean Plane

This file defines the Euclidean Plane as a inner product real vector space equipped with a basis.

## Important definitions

* `EuclideanPlane` : the class of Euclidean Plane
* `x_coordinate` : the x coordiante of a point
* `y_coordinate` : the y coordiante of a point

## Notation

We introduce the notation `x(p)`, `y(p)` for the x,y coordinates of a point `p` on a Euclidean Plane.

-/


/- Define Euclidean plane as normed vector space over ℝ of dimension 2 -/
namespace EuclidGeom

class EuclideanPlane (V : Type _)  extends  NormedAddCommGroup V, InnerProductSpace ℝ V where
  dim_two : FiniteDimensional.finrank ℝ V = 2
  basis : Basis (Fin 2) ℝ V

variable {V : Type _} [h : EuclideanPlane V] (p : V) 

def x_coordinate := (Basis.coord h.basis 0).toFun

def y_coordinate := (Basis.coord h.basis 1).toFun

notation "x("p")" => x_coordinate p
notation "y("p")" => y_coordinate p

end EuclidGeom



