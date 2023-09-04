/- Here stores unused codes-/
import Mathlib.Analysis.InnerProductSpace.PiL2

import EuclideanGeometry.Foundation.Axiom.Basic
import EuclideanGeometry.Foundation.Axiom.Ray
import EuclideanGeometry.Foundation.Axiom.Angle

namespace EuclidGeom
/- Another way of defining 2DVecSpace before define EuclideanPlane，-/
section Cartesian2dVectorSpace

class Cartesian2dVectorSpace (V : Type _)  extends  NormedAddCommGroup V, InnerProductSpace ℝ V where
  dim_two : FiniteDimensional.finrank ℝ V = 2
  basis : Basis (Fin 2) ℝ V
  orthonormal : Orthonormal ℝ basis

variable {V : Type _} [h : Cartesian2dVectorSpace V]

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

theorem norm (v : V) : norm v = Real.sqrt (x(v)^2 + y(v)^2) := sorry

noncomputable def vector_of_coord (x : ℝ) (y : ℝ) : V := x • (h.basis 0) + y • (h.basis 1)

notation "v("x"," y ")" => vector_of_coord x y

theorem x_coord_of_vector_of_coord (x : ℝ) (y : ℝ) : x(vector_of_coord (h := h) x y) = x := sorry

end Cartesian2dVectorSpace

/- unused sketch of undirected lines, segments-/
section undirected

class Line' (P : Type _) [EuclideanPlane P] where
-- What is a line??? to be affine subspaces of dimension 1, citing affine vector spaces?
-- carrier : Set P
-- linearity

class GSeg' (P : Type _) [EuclideanPlane P] where
-- a multiset of 2 points? or just never mention this?

class Seg' (P : Type _) [EuclideanPlane P] where
-- a multiset of 2 diff points? or just never mention this?
-- carrier

def IsOnLine' {P : Type _} [EuclideanPlane P] (a : P) (l : Line' P) : Prop := sorry

infixl : 50 "LiesOnLine" => IsOnLine'

instance {P : Type _} [EuclideanPlane P] : Coe (Ray P) (Line' P) where
  coe := sorry

end undirected

section angle
namespace OAngle
open Classical

noncomputable def angle_of_three_points' {P : Type _} [h : EuclideanPlane P] (A O B : P) : ℝ := if ((A = O) ∨ (B = O)) then 0 else Real.Angle.toReal (value (mk' A O B sorry sorry))
end OAngle
end angle





end EuclidGeom
