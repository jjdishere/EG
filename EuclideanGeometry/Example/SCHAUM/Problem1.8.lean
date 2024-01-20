import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash

noncomputable section

namespace EuclidGeom

namespace Schaum

namespace Problem1_8

/-
Let $\triangle ABC$ be a regular triangle. Let $D$, $E$ be points on the extensions of $BC$ and $CA$, respectively,
such that $CD = AE$.

Prove that $AD = BE$
-/
structure Setting (Plane : Type*) [EuclideanPlane Plane] where
--Let $\triangle ABC$ be a regular triangle.
  A : Plane
  B : Plane
  C : Plane
  not_collinear_ABC : ¬ Collinear A B C
  regular_ABC : (▵ A B C).IsRegular
--Claim $A \ne B$
  A_ne_B : A ≠ B :=
  -- This is because vertices $A, B$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.2.symm
--Claim $B \ne C$
  B_ne_C : B ≠ C :=
  -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).1.symm
--Claim $C \ne A$
  C_ne_A : C ≠ A :=
  -- This is because vertices $A, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.1.symm
--let $D$ be point on the extension of $BC$
  D : Plane
  D_int_BC_ext : D LiesInt (SEG_nd B C B_ne_C.symm).extension
--let $E$ be point on the extension of $CA$
  E : Plane
  E_int_CA_ext : E LiesInt (SEG_nd C A C_ne_A.symm).extension
--such that $CD = AE$
  CD_eq_AE : ((SEG C D).length = (SEG A E).length)
--Prove that $AD = BE$
theorem result {Plane : Type*} [EuclideanPlane Plane] (e : Setting Plane) : ((SEG e.A e.D).length = (SEG e.B e.E).length):= by
/-
In regular triangle $ABC$, $\angle ABC = \angle BCA$.
Since $D$ lies on the extension of $BC$, we know that $\angle ABD$ is the same as $\angle ABC$.
Since $E$ lies on the extension of $CA$, we know that $\angle BCE$ is the same as $\angle BCA$.
Therefore, $\angle ABD = \angle ABC = \angle BCA = \angle BCE$.
In regular triangle $ABC$, $AB = BC$.
In regular triangle $ABC$, $BC = CA$.
So we have $BD = BC + CD = CA + AE = CE$.
In $\triangle BDA$ and $\triangle CEB$,
$\cdot AB = BC$
$\cdot \angle ABD = \angle BCE$
$\cdot BD = CE$
Thus, $\triangle BDA \cong \triangle CEB$ (by SAS).
Therefore, $BD = CE$.
-/
  --We have that $B, D, A$ is not collinear.
  have not_collinear_BDA : ¬ Collinear e.B e.D e.A := by sorry
  --We have that $C, E, B$ is not collinear.
  have not_collinear_CEB : ¬ Collinear e.C e.E e.B := by sorry
  --We have $D \ne B$.
  have D_ne_B : e.D ≠ e.B := by sorry
  --We have $A \ne B$.
  have A_ne_B : e.A ≠ e.B := by sorry
  --We have $E \ne C$.
  have E_ne_C : e.E ≠ e.C := by sorry
  --We have $B \ne C$.
  have B_ne_C : e.B ≠ e.C := by sorry
  --We have $A \ne C$.
  have A_ne_C : e.A ≠ e.C := by sorry
  --We have $AB = BC$ because triangle $ABC$ is a regular triangle.
  have AB_eq_BC : (SEG e.A e.B).length = (SEG e.B e.C).length := e.regular_ABC.2.symm
  --We have $BC = CA$ because triangle $ABC$ is a regular triangle.
  have BC_eq_CA : (SEG e.B e.C).length = (SEG e.C e.A).length := e.regular_ABC.1
  --We have $C$ lies on $BD$.
  have C_on_BD : e.C LiesOn (SEG e.B e.D) := by sorry
  --We have $A$ lies on $CE$.
  have A_on_CE : e.A LiesOn (SEG e.C e.E) := by sorry
  -- We have $\angle DBA = \angle ECB$.
  have angle_DBA_eq_angle_ECB : ∠ e.D e.B e.A D_ne_B e.A_ne_B = ∠ e.E e.C e.B E_ne_C e.B_ne_C := by
    calc
    ∠ e.D e.B e.A D_ne_B e.A_ne_B
    -- Since $D$ lies on the extension of $BC$, we know that $\angle DBA$ is the same as $\angle CBA$.
    _= ∠ e.C e.B e.A B_ne_C.symm e.A_ne_B := by
      symm;
      apply Angle.value_eq_of_lies_on_ray_pt_pt e.A_ne_B D_ne_B e.A_ne_B
      · exact lies_int_toRay_of_lies_int_extn e.B e.C e.D e.B_ne_C.symm e.D_int_BC_ext
      · exact Ray.snd_pt_lies_int_mk_pt_pt e.B e.A e.A_ne_B
    -- In regular triangle $ABC$, $\angle CBA = \angle ACB$.
    _= ∠ e.A e.C e.B A_ne_C e.B_ne_C := by
      apply (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := (TRI_nd e.A e.B e.C e.not_collinear_ABC))).mp
      exact Triangle.isoceles_of_regular (▵ e.A e.B e.C) e.regular_ABC
    -- Since $E$ lies on the extension of $CA$, we know that $\angle BCA$ is the same as $\angle ECB$.
    _= ∠ e.E e.C e.B E_ne_C e.B_ne_C := by
      apply Angle.value_eq_of_lies_on_ray_pt_pt A_ne_C e.B_ne_C E_ne_C e.B_ne_C
      · exact lies_int_toRay_of_lies_int_extn e.C e.A e.E A_ne_C e.E_int_CA_ext
      · exact Ray.snd_pt_lies_int_mk_pt_pt e.C e.B e.B_ne_C
  -- We have $BD = CE$.
  have BD_eq_CE : (SEG e.B e.D).length = (SEG e.C e.E).length := by
    calc
    (SEG e.B e.D).length
    -- $BD = BC + CD$ because $C$ lies on segment $BD$,
    _= (SEG e.B e.C).length + (SEG e.C e.D).length := by
      apply length_eq_length_add_length
      exact C_on_BD
    -- $BC + CD = CA + AE$ because $BC = CA$ and $CD = AE$.
    _= (SEG e.C e.A).length + (SEG e.A e.E).length := by simp only [BC_eq_CA, e.CD_eq_AE]
    -- $CA + AE = CE$ because $A$ lies on segment $CE$.
    _= (SEG e.C e.E).length := by
      symm;apply length_eq_length_add_length
      exact A_on_CE
  -- We have $\triangle ABD \cong \triangle BCE$ (by SAS).
  have triangle_BDA_congr_triangle_CEB : TriangleND.IsCongr (TRI_nd e.B e.D e.A not_collinear_BDA) (TRI_nd e.C e.E e.B not_collinear_CEB) := by
    apply TriangleND.congr_of_SAS
    -- $\cdot AB = BC$
    · exact AB_eq_BC
    -- $\cdot \angle ABD = \angle BCE$
    · exact angle_DBA_eq_angle_ECB
    -- $\cdot BD = CE$
    · exact BD_eq_CE
  calc
  -- $AD = DA$ by symmetry,
  (SEG e.A e.D).length = (SEG e.D e.A).length := by apply length_of_rev_eq_length'
  -- $DA = EB$ because $\triangle ABD \cong \triangle BCE$,
  _= (SEG e.E e.B).length := triangle_BDA_congr_triangle_CEB.edge₁
  -- $EB = BE$ by symmetry.
  _= (SEG e.B e.E).length := by apply length_of_rev_eq_length'

end Problem1_8
end Schaum
end EuclidGeom
