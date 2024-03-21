import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex_trash

noncomputable section

namespace EuclidGeom

namespace Schaum

namespace Problem1_9

open Angle

/-
Let $\triangle ABC$ be an isoceles triangle in which $AB = AC$. Let $E$ be a point on the extension of $BA$.Let X be a point on the ray through $A$ with the same direction to $\vec{BC}$.

Prove that $\angle EAX = \angle XAC$.
-/

structure Setting1 (Plane : Type*) [EuclideanPlane Plane] where
-- Let $\triangle ABC$ be an isoceles triangle in which $AB = AC$.
  A : Plane
  B : Plane
  C : Plane
  not_collinear_ABC : ¬ Collinear A B C
  isoceles_ABC : (▵ A B C).IsIsoceles
-- Claim $B \ne A$.
  B_ne_A : PtNe B A :=
    -- This is because vertices $A, B$ of a nondegenerate triangle are distinct.
    ⟨(ne_of_not_collinear not_collinear_ABC).2.2⟩
-- denote the extension of $BA$ as $BA_ext$.
  BA_ext : Ray Plane
  hlba : BA_ext = (SEG_nd B A B_ne_A.out.symm).extension
-- Let $E$ be a point on the extension of $BA$.
  E : Plane
  E_int_ext : E LiesInt BA_ext
-- Claim $C \ne B$.
  C_ne_B : PtNe C B :=
  -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    ⟨(ne_of_not_collinear not_collinear_ABC).1⟩
-- Claim $C \ne A$.
  C_ne_A : PtNe C A :=
  -- This is because vertices $A, C$ of a nondegenerate triangle are distinct.
    ⟨(ne_of_not_collinear not_collinear_ABC).2.1.symm⟩
-- denote segment $BC$ as $BC$.
  BC : SegND Plane
  hbc : BC = (SEG_nd B C C_ne_B.out)
-- denote the ray from $A$ which has the same direction as $BC$ as $l_a$.
  l_a : Ray Plane
  hla : l_a = Ray.mk A (BC.toDir)
-- Let $X$ be a point on $l_a$.
  X : Plane
  X_int_la : X LiesInt l_a
-- Claim $E \ne A$
lemma E_ne_A {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : e.E ≠ e.A := by
  -- This is because $E$ lies on the extension of $BA$ and $A$ is the source of that ray.
  -- We have $E$ is not equal to the source of the extension of $BA$, since $E$ lies on the extension of $BA$.
  have h1 : e.E ≠ e.BA_ext.source := e.E_int_ext.2
  -- We have $A$ is the source of the extension of $BA$ by definition.
  have h2 : e.A = e.BA_ext.source := by simp only [e.hlba]; rfl
  simp only [h2]; exact h1
-- Claim : $X \ne A$
lemma X_ne_A {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : e.X ≠ e.A := by
  -- This is because $X$ lies on $l_a$ and $A$ is the source of that ray.
  -- We have $X$ is not equal to the source $l_a$, since $X$ lies on the extension of $BA$.
  have h1 : e.X ≠ e.l_a.source := e.X_int_la.2
  -- We have $A$ is the source of $l_a$ by definition.
  have h2 : e.A = (e.l_a).source := by simp only [e.hla]
  simp only [h2]; exact h1
structure Setting2 (Plane : Type*) [EuclideanPlane Plane] extends Setting1 Plane where
  E_ne_A : PtNe E A := ⟨E_ne_A⟩
  X_ne_A : PtNe X A := ⟨X_ne_A⟩

attribute [instance] Setting1.B_ne_A Setting1.C_ne_A Setting1.C_ne_B Setting2.E_ne_A Setting2.X_ne_A
-- Prove that $\angle EAX = \angle XAC$
theorem result {Plane : Type*} [EuclideanPlane Plane] (e : Setting2 Plane) : ∠ e.E e.A e.X = ∠ e.X e.A e.C:= by
/-
As $AX$ has the same direction as $BC$ and that $E$ is on the extension of $BA$, we know that $\angle EAX = \angle ABC$.
In isoceles triangle $ABC$, $\angle ABC = - \angle ACB$.
As $AX$ has the opposite direction of $CB$ and $AC$ has the opposite direction of $CA$, we have $\angle ACB = - \angle XAC$
Therefore, $\angle EAX = \angle ABC = - \angle ACB = \angle XAC$.
-/
-- We have that the direction of $AE$ is the same as the direction of $BA$.
  have dir_AE_eq_dir_BA : (RAY e.A e.E).toDir = (RAY e.B e.A).toDir :=
    calc
    (RAY e.A e.E).toDir
    -- We have that the direction of $AE$ is the same as the direction of the extension of $BA$, since $E$ lies on the extension of $BA$ and $A$ is the source of which.
    _= (e.BA_ext).toDir := by
      have : e.E LiesInt (SEG_nd e.B e.A).extension := by
        simp only [e.hlba.symm]; exact e.E_int_ext
      simp only [e.hlba]
      exact Ray.pt_pt_toDir_eq_ray_toDir this
    -- We have that the direction of the extension of $BA$ is the same as the direction of $BA$ by definition.
    _= (RAY e.B e.A).toDir := by
      simp only [e.hlba, SegND.extn_toDir, SegND.mkPtPt_toDir, Ray.mkPtPt_toDir]
  -- We have that the direction of $AX$ is the same as the direction of $CB$.
  have dir_AX_eq_dir_BC : (RAY e.A e.X).toDir = (RAY e.B e.C).toDir :=
    calc
    (RAY e.A e.X).toDir
    -- We have that the direction of $AX$ is the same as the direction of $l_a$, since $X$ lies on the $l_a$ and $A$ is the source of which.
    _= e.l_a.toDir := by
      have : e.A = e.l_a.source := by simp only [e.hla]
      simp only [this]
      exact Ray.pt_pt_toDir_eq_ray_toDir e.X_int_la
    -- We have that the direction of $l_a$ is the same as the direction of the segment $BC$ by definition.
    _= e.BC.toDir := by simp only [e.hla]
    -- We have that the direction of the segment $BC$ is the same as the direction of ray $BC$ by definition.
    _= (RAY e.B e.C).toDir := by
      simp only [e.hbc, SegND.mkPtPt_toDir, Ray.mkPtPt_toDir]
  -- We have that the direction of $AC$ is opposite to the direction of $CA$ by symmetry.
  have dir_AC_eq_neg_dir_CA : (RAY e.C e.A).toDir = - (RAY e.A e.C).toDir := Ray.toDir_eq_neg_toDir_of_mk_pt_pt
  -- We have that the direction of $CB$ is opposite to the direction of $BC$ by symmetry.
  have dir_CB_eq_neg_dir_BC : (RAY e.C e.B).toDir = - (RAY e.B e.C).toDir := Ray.toDir_eq_neg_toDir_of_mk_pt_pt
  -- We have that the direction of $CB$ is opposite to the direction of $AX$ because $AX$ has the same direction as $BC$ and $BC$ has the direction opposite to $CB$.
  have dir_CB_eq_neg_dir_AX : (RAY e.C e.B).toDir = - (RAY e.A e.X).toDir := by simp only [dir_AX_eq_dir_BC]; exact dir_CB_eq_neg_dir_BC

  calc
  (∠ e.E e.A e.X)
  -- As $AE$ has the same direction as $BA$ and that $AX$ has the same direction as $BC$, we know that $\angle EAX = \angle ABC$,
  _= ∠ e.A e.B e.C := value_eq_of_dir_eq dir_AE_eq_dir_BA dir_AX_eq_dir_BC
  -- $\angle ABC = - \angle CBA$ by symmetry,
  _= - ∠ e.C e.B e.A := by apply Angle.neg_value_of_rev_ang
  -- $ - \angle CBA = - \angle ACB$ because $\angle CBA = \angle ACB$ in the isoceles triangle $ABC$,
  _= - ∠ e.A e.C e.B := by
    simp only [neg_inj] ; exact is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := (TRI_nd e.A e.B e.C e.not_collinear_ABC)).mp e.isoceles_ABC
  -- as $AC$ has the opposite direction of $CA$ and $AX$ has the opposite direction of $CB$, we have $\angle ACB = - \angle XAC$,
  _= - ∠ e.C e.A e.X := by
    simp only [neg_inj] ; exact ang_eq_ang_of_toDir_eq_neg_toDir dir_AC_eq_neg_dir_CA dir_CB_eq_neg_dir_AX
  -- $ - \angle CAX = \angle XAC$ by symmetry.
  _= ∠ e.X e.A e.C := by symm; apply Angle.neg_value_of_rev_ang
end Problem1_9

end Schaum
