/- Here stores unused codes -/
import Mathlib.Analysis.InnerProductSpace.PiL2

import EuclideanGeometry.Foundation.Index

noncomputable section
namespace EuclidGeom
/- Another way of defining 2DVecSpace before define EuclideanPlane，-/
section Cartesian2dVectorSpace
/- -/
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

-- Unused section Pythagoras in Vector

-- Our aim is to prove Pythagoras theorem in the file Perpendicular, but in this section, we will only prove that the inner product of to VecND having same toProj is zero, which is the main theorem about toProj we will use in the proof of Pythagoras theorem.

/-!
section Pythagoras

theorem Dir.inner_eq_zero_of_toProj_eq_toProj_perp (d₁ d₂ : Dir) (h : d₁.toProj.perp = d₂.toProj) : Vec.InnerProductSpace.Core.inner d₁.toVec d₂.toVec = 0 := by
  let h' := Quotient.exact h
  unfold HasEquiv.Equiv instHasEquiv PM.con PM at h'
  simp only [Con.rel_eq_coe, Con.rel_mk] at h'
  by_cases Dir.I * d₁ = d₂
  · rw [← h]
    unfold Dir.I HMul.hMul instHMul Mul.mul Dir.instMulDir Vec.toComplex Complex.toVec Vec.InnerProductSpace.Core
    simp only [Complex.mul_re, Complex.mul_im, zero_mul, one_mul, zero_sub, zero_add, mul_neg]
    ring
  · have h : Dir.I * d₁ = -d₂ := by tauto
    have h' : - (Dir.I * d₁) = - - d₂ := by
      rw [← h]
    rw [← Iff.mp neg_eq_iff_eq_neg rfl] at h'
    rw [← h']
    unfold Neg.neg Dir.instNegDir Dir.I HMul.hMul instHMul Mul.mul Dir.instMulDir Vec.toComplex Complex.toVec Vec.InnerProductSpace.Core
    simp only [Complex.mul_re, Complex.mul_im, zero_mul, one_mul, zero_sub, zero_add, Prod.neg_mk, neg_neg, mul_neg]
    ring

theorem inner_eq_zero_of_toProj_perp_eq_toProj (v₁ v₂ : VecND) (h : v₁.toProj.perp = v₂.toProj) : Vec.InnerProductSpace.Core.inner v₁.1 v₂.1 = 0 := by
  rw [← VecND.norm_smul_toDir_eq_self v₁, ← VecND.norm_smul_toDir_eq_self v₂]
  let g := Dir.inner_eq_zero_of_toProj_eq_toProj_perp (VecND.toDir v₁) (VecND.toDir v₂) h
  unfold Vec.InnerProductSpace.Core at g
  simp only at g
  unfold Vec.InnerProductSpace.Core
  simp only [ne_eq, Prod.smul_fst, smul_eq_mul, Prod.smul_snd]
  rw [← mul_zero (Vec.norm v₁.1 * Vec.norm v₂.1), ← g]
  simp only [ne_eq]
  ring

end Pythagoras
-/

/- Unused section Pythagoras in Perpendicular

section Pythagoras

theorem Pythagoras_of_ne_ne_perp' (P : Type _) [EuclideanPlane P] {A B C : P} (hab : B ≠ A) (hac : C ≠ A) (h : (SegND.toProj ⟨SEG A B, hab⟩).perp = (SegND.toProj ⟨SEG A C, hac⟩)) : (SEG A B).length ^ 2 + (SEG A C).length ^ 2 = (SEG B C).length ^ 2 := by
  have i : Vec.InnerProductSpace.Core.inner (VEC A B) (VEC A C) = 0 := inner_eq_zero_of_toProj_perp_eq_toProj (SegND.toVecND ⟨SEG A B, hab⟩) (SegND.toVecND ⟨SEG A C, hac⟩) h
  rw [Seg.length_sq_eq_inner_toVec_toVec (SEG A B), Seg.length_sq_eq_inner_toVec_toVec (SEG A C), Seg.length_sq_eq_inner_toVec_toVec (SEG B C)]
  simp only [seg_toVec_eq_vec]
  rw [← vec_sub_vec A B C]
  unfold Vec.InnerProductSpace.Core at i
  simp only at i
  unfold Vec.InnerProductSpace.Core
  simp only [HSub.hSub, Sub.sub]
  rw [← zero_add ((VEC A B).fst * (VEC A B).fst), ← zero_add ((VEC A B).fst * (VEC A B).fst), ← neg_zero, ← i]
  ring

theorem Pythagoras_of_perp_foot' (P : Type _) [EuclideanPlane P] (A B : P) {l : Line P} (h : B LiesOn l) : (SEG A (perp_foot A l)).length ^ 2 + (SEG B (perp_foot A l)).length ^ 2 = (SEG A B).length ^ 2 := by
  sorry

end Pythagoras
-/
/-!
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

infixl : 50 "LiesOn" => IsOnLine'

instance {P : Type _} [EuclideanPlane P] : Coe (Ray P) (Line' P) where
  coe := sorry

end undirected

section angle
namespace Angle
open Classical

noncomputable def angle_of_three_points' {P : Type _} [h : EuclideanPlane P] (A O B : P) : ℝ := if ((A = O) ∨ (B = O)) then 0 else AngValue.toReal (value (mk_pt_pt_pt A O B sorry sorry))
end Angle
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

-- def Seg.toDSeg_of_nontriv {P : Type _} [EuclideanPlane P] (l : Seg P) (nontriv : l.target ≠ l.source): DSeg P where
--   source := l.source
--   target := l.target
--   toDir := Vec.toDir (l.target -ᵥ l.source) (vsub_ne_zero.mpr nontriv)
--   on_ray := sorry
--   non_triv := sorry

-- theorems "if p LiesOnDSeg l, then p LiesOn l.toRay and p LiesOn l.toSeg"

-- theorem DSeg.pt_on_toray_of_pt_on_DSeg {P : Type _} [EuclideanPlane P] (p : P) (l : DSeg P) (lieson : p LiesOnDSeg l) : p LiesOn l.toRay := sorry

theorem DSeg.pt_on_toseg_of_pt_on_DSeg {P : Type _} [EuclideanPlane P] (p : P) (l : DSeg P) (lieson : p LiesOnDSeg l) : p LiesOn l.toSeg := sorry

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

-- the operation of reversing the toDir commutes with coercion between directed segments and generalized directed segments.
theorem DSeg.rev_toseg_eq_toseg_rev : seg.reverse.toSeg = (seg.toSeg).reverse := sorry

-- theorem Seg.rev_toDSeg_eq_toDSeg_rev (nontriv : gseg.target ≠ gseg.source) : (gseg.reverse).toDSeg_of_nontriv (Seg.nontriv_of_rev_of_nontriv gseg nontriv) = (gseg.toDSeg_of_nontriv nontriv).reverse := sorry

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
  · exact (Angle.mk ray (Ray.mk_pt_pt ray.source A h ) rfl).value = 0

def IsOnNegSide (A : P) (ray : Ray P) : Prop := by
  by_cases A = ray.source
  · exact False
  · exact (Angle.mk ray (Ray.mk_pt_pt ray.source A h ) rfl).value = π

def IsSource (A : P) (ray : Ray P) : Prop := ray.source = A

scoped infix : 50 "LiesOnPos" => IsOnPosSide
scoped infix : 50 "LiesOnNeg" => IsOnNegSide
scoped infix : 50 "LiesAtSource" => IsSource

end pos_neg_ray
-/

section nondeg_tri
open Classical

/- Class of generalized triangles -/
/-
class Triangle' (P : Type _) [EuclideanPlane P] where
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

-/

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

/-!
section HasFallsOn

class HasFallsOn (α β : Type _) [HasLiesOn P α] [HasLiesOn P β] where
  falls_on : α → β → Prop
  lies_on_falls_on : ∀ (p : P) (A : α) (B : β), HasLiesOn.lies_on p A → falls_on A B → HasLiesOn.lies_on p B

class HasFallsIn (α β : Type _) [HasLiesIn P α] [HasLiesIn P β] where
  falls_in : α → β → Prop
  lies_in_falls_in : ∀ (p : P) (A : α) (B : β), HasLiesIn.lies_in p A → falls_in A B → HasLiesIn.lies_in p B

scoped notation A "FallsOn" B => HasFallsOn.falls_on A B
scoped notation A "FallsIn" B => HasFallsIn.falls_in A B

end HasFallsOn
-/

/-!

-- scoped notation A "LiesInt" F => HasLiesInt.lies_int A F

def IsFallsOn {α β : Type _} (A : α) (B : β) [HasLiesOn P α] [HasLiesOn P β] : Prop := ∀ (A : P), (A LiesOn A) → (A LiesOn B)

def IsFallsIn {α β : Type _} (A : α) (B : β) [HasLiesIn P α] [HasLiesIn P β] : Prop := ∀ (A : P), (A LiesIn A) → (A LiesIn B)

-- LiesOn → LiesInt is FallsInt ?

scoped notation A "FallsOn" B "Over" P => IsFallsOn P A B
scoped notation A "FallsIn" B "Over" P => IsFallsIn P A B

namespace IsFallsOn

protected theorem refl {P : Type _} {α : Type _} (A : α) [HasLiesOn P α] : A FallsOn A Over P := by tauto

protected theorem trans {P : Type _} {α β γ : Type _} (A : α) (B : β) (C : γ) [HasLiesOn P α] [HasLiesOn P β] [HasLiesOn P γ] : (A FallsOn B Over P) → (B FallsOn C Over P) → (A FallsOn C Over P)   := by tauto

end IsFallsOn

namespace IsFallsIn

protected theorem refl {P : Type _} {α : Type _} (A : α) [HasLiesIn P α] : A FallsIn A Over P := by tauto

protected theorem trans {P : Type _} {α β γ : Type _} (A : α) (B : β) (C : γ) [HasLiesIn P α] [HasLiesIn P β] [HasLiesIn P γ] : (A FallsIn B Over P) → (B FallsIn C Over P) → (A FallsIn C Over P)   := by tauto

end IsFallsIn

def IsIntersectionPoint {P : Type _} {α β : Type _} (A : P) (A : α) (B : β) [HasLiesOn P α] [HasLiesOn P β] := (A LiesOn A) ∧ (A LiesOn B)

scoped notation p "IsIntersectionOf" A B => IsIntersectionPoint p A B

/-
class HasProj (α : Type _) where
  toProj : (α → Proj)

def parallel {α β : Type _} (A : α) (B : β) [HasProj α] [HasProj β] : Prop := HasProj.toProj A = HasProj.toProj B

scoped notation A "IsParallelTo" B => parallel A B
scoped notation A "∥" B => parallel A B

namespace parallel

protected theorem refl {α : Type _} (A : α) [HasProj α] : A ∥ A := rfl

protected theorem symm {α β : Type _} (A : α) (B : β) [HasProj α] [HasProj β] : (A ∥ B) → (B ∥ A) := Eq.symm

protected theorem trans {α β γ : Type _} (A : α) (B : β) (C : γ) [HasProj α] [HasProj β] [HasProj γ]: (A ∥ B) → (B ∥ C) → (A ∥ C) := Eq.trans

end parallel

def perpendicular {α β : Type _} (A : α) (B : β) [HasProj α] [HasProj β] : Prop := sorry

scoped notation A "IsPerpendicularTo" B => perpendicular A B
scoped notation A "⟂" B => perpendicular A B

namespace perpendicular

protected theorem irrefl {α : Type _} (A : α) [HasProj α] : ¬ (A ⟂ A) := by sorry

protected theorem symm {α β : Type _} (A : α) (B : β) [HasProj α] [HasProj β] : (A ⟂ B) → (B ⟂ A) := sorry

end perpendicular

theorem parallel_of_perp_perp {α β γ : Type _} (A : α) (B : β) (C : γ) [HasProj α] [HasProj β] [HasProj γ] : (A ⟂ B) → (B ⟂ C) → (A ∥ C)  := sorry
-/ -/

structure IsAngBis {P : Type _} [EuclideanPlane P] (ang : Angle P) (ray : Ray P) : Prop where intro ::
  eq_vtx : ang.source = ray.source
  bisect_ang : 2 * (Angle.mk ang.start_ray ray eq_vtx).value = ang.value

end EuclidGeom
