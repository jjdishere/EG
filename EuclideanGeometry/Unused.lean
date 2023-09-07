/- Here stores unused codes-/
import Mathlib.Analysis.InnerProductSpace.PiL2

import EuclideanGeometry.Foundation.Axiom.Plane
import EuclideanGeometry.Foundation.Axiom.Ray
import EuclideanGeometry.Foundation.Axiom.Angle
import EuclideanGeometry.Foundation.Axiom.Ray_ex
import EuclideanGeometry.Foundation.Axiom.Translation_ex
import EuclideanGeometry.Foundation.Axiom.Position

noncomputable section
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

noncomputable def angle_of_three_points' {P : Type _} [h : EuclideanPlane P] (A O B : P) : ℝ := if ((A = O) ∨ (B = O)) then 0 else Real.Angle.toReal (value (mk_pt_pt_pt A O B sorry sorry))
end OAngle
end angle

section nondeg

/- Directed segment -/
class DSeg (P : Type _) [EuclideanPlane P] extends Ray P, Seg P where
  on_ray : IsOnRay target toRay 
  non_triv : target ≠ source

/- Define a point lies on an oriented segment, a line, a segment, immediate consequences -/
def IsOnDSeg {P : Type _} [EuclideanPlane P] (a : P) (l : DSeg P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧ a = t • (l.target -ᵥ l.source) +ᵥ l.source

end nondeg

scoped infix : 50 "LiesOnDSeg" => IsOnDSeg

section nondeg

instance {P : Type _} [EuclideanPlane P] : Coe (DSeg P) (Seg P) where
  coe := fun _ => DSeg.toSeg

/- def of DirSeg from GDirSeg if length ≠ 0 -/
def Seg.toDSeg_of_nontriv {P : Type _} [EuclideanPlane P] (l : Seg P) (nontriv : l.target ≠ l.source): DSeg P where
  source := l.source
  target := l.target
  toDir := Vec.normalize (l.target -ᵥ l.source) (vsub_ne_zero.mpr nontriv)
  on_ray := sorry
  non_triv := sorry

-- theorems "if p LiesOnDSeg l, then p LiesOnRay l.toRay and p LiesOnSeg l.toSeg"

theorem DSeg.pt_on_toRay_of_pt_on_DSeg {P : Type _} [EuclideanPlane P] (p : P) (l : DSeg P) (lieson : p LiesOnDSeg l) : p LiesOnRay l.toRay := sorry

theorem DSeg.pt_on_toSeg_of_pt_on_DSeg {P : Type _} [EuclideanPlane P] (p : P) (l : DSeg P) (lieson : p LiesOnDSeg l) : p LiesOnSeg l.toSeg := sorry

-- mk method of DirSeg giving 2 distinct point
def DSeg.mk_pt_pt {P : Type _} [EuclideanPlane P] (A B : P) (h : B ≠ A) : DSeg P := sorry  

namespace DSeg

variable {P: Type _} [EuclideanPlane P] (seg : DSeg P) (gseg : Seg P)

-- source and targets are on generalized directed segments
theorem source_lies_on_seg : seg.source LiesOnDSeg seg := by sorry


theorem target_lies_on_seg : seg.target LiesOnDSeg seg := by sorry

-- definition of the reversion of the toDir of a directed segment
def reverse : DSeg P where
  source := seg.target
  target := seg.source
  toDir := -seg.toDir
  on_ray := sorry
  non_triv := sorry

-- double reverse a directed segment gets back to itself
theorem double_rev_eq_self  : seg.reverse.reverse = seg := sorry

-- reversing the toDir does not change the property that a point lies on the directed segments.
theorem IsOnDSeg_of_rev_of_IsOnDSeg (a : P) (lieson : a LiesOnDSeg seg) : a LiesOnDSeg seg.reverse := sorry

-- the operation of reversing the toDir commutes with coersion between directed segments and generalized directed segments.
theorem DSeg.rev_toSeg_eq_toSeg_rev : seg.reverse.toSeg = (seg.toSeg).reverse := sorry

theorem Seg.rev_toDSeg_eq_toDSeg_rev (nontriv : gseg.target ≠ gseg.source) : (gseg.reverse).toDSeg_of_nontriv (Seg.nontriv_of_rev_of_nontriv gseg nontriv) = (gseg.toDSeg_of_nontriv nontriv).reverse := sorry

variable {P: Type _} [EuclideanPlane P] (v : ℝ × ℝ) (seg : DSeg P)

-- parallel translate a directed segments

def translate (seg : DSeg P) (v : ℝ × ℝ) : DSeg P where
  source := sorry
  target := v +ᵥ seg.target
  toDir := sorry
  on_ray := sorry
  non_triv := sorry


end DSeg

end nondeg


section pos_neg_ray
variable {P : Type _} [EuclideanPlane P]

def IsOnPosSide (A : P) (ray : Ray P) : Prop := by
  by_cases A = ray.source
  · exact False
  · exact (OAngle.mk ray (Ray.mk_pt_pt ray.source A h ) rfl).value = 0 

def IsOnNegSide (A : P) (ray : Ray P) : Prop := by
  by_cases A = ray.source
  · exact False
  · exact (OAngle.mk ray (Ray.mk_pt_pt ray.source A h ) rfl).value = π 

def IsSource (A : P) (ray : Ray P) : Prop := ray.source = A

scoped infix : 50 "LiesOnPos" => IsOnPosSide 
scoped infix : 50 "LiesOnNeg" => IsOnNegSide
scoped infix : 50 "LiesAtSource" => IsSource

end pos_neg_ray

section nondeg_tri
open Classical

/- Class of generalized triangles -/
class Triangle (P : Type _) [EuclideanPlane P] where 
  point₁ : P
  point₂ : P
  point₃ : P
  nontriv : ¬ colinear point₁ point₂ point₃

namespace Triangle

variable {P : Type _} [EuclideanPlane P]

def nontriv₁ (tr : Triangle P) := (ne_of_not_colinear tr.nontriv).1

def nontriv₂ (tr : Triangle P) := (ne_of_not_colinear tr.nontriv).2.1

def nontriv₃ (tr : Triangle P) := (ne_of_not_colinear tr.nontriv).2.2

def is_cclock (tr : Triangle P): Prop := tr.3 LiesOnLeft (Ray.mk_pt_pt tr.1 tr.2 tr.nontriv₃)

--implies  1 left of 23, 2 left of 31

-- not is_cclock implies 1 right of 23, ..., ...

def edge₁ (tr : Triangle P) : DSeg P:= DSeg.mk_pt_pt tr.2 tr.3 tr.nontriv₁

def edge₂ (tr : Triangle P) : DSeg P:= DSeg.mk_pt_pt tr.3 tr.1 tr.nontriv₂

def edge₃ (tr : Triangle P) : DSeg P:= DSeg.mk_pt_pt tr.1 tr.2 tr.nontriv₃

def IsInside  (A : P) (tr : Triangle P) : Prop := if tr.is_cclock then A LiesOnLeft tr.edge₁.toRay ∧ A LiesOnLeft tr.edge₂.toRay ∧ A LiesOnLeft tr.edge₃.toRay else A LiesOnRight tr.edge₁.toRay ∧ A LiesOnRight tr.edge₂.toRay ∧ A LiesOnRight tr.edge₃.toRay

def area (tr : Triangle P) : ℝ := sorry 

end Triangle

scoped infix : 50 "IsInsideLTriangle" => Triangle.IsInside

end nondeg_tri

section colinear

variable {P : Type _} [EuclideanPlane P]

theorem colinear_ACB_of_colinear_ABC {A B C : P} (h : colinear A B C): colinear A C B := sorry

theorem colinear_BAC_of_colinear_ABC {A B C : P} (h : colinear A B C): colinear B A C := sorry

theorem colinear_BCA_of_colinear_ABC {A B C : P} (h : colinear A B C): colinear B C A := sorry

theorem colinear_CAB_of_colinear_ABC {A B C : P} (h : colinear A B C): colinear C A B := sorry

theorem colinear_CBA_of_colinear_ABC {A B C : P} (h : colinear A B C): colinear C B A := sorry
end colinear

end EuclidGeom
