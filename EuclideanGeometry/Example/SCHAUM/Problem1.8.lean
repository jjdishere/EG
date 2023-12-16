import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace Problem1_8_

/-
Let $\triangle ABC$ be a regular triangle. Let $D$, $E$ be points on the extensions of $BC$ and $CA$, respectively,
such that $CD = AE$.

Prove that $AD = BE$
-/

--Let $\triangle ABC$ be a regular triangle.
variable {A B C : Plane} {not_colinear_ABC : ¬ colinear A B C} {hreg : (▵ A B C).IsRegular}
--Claim $A \ne B$
lemma A_ne_B : A ≠ B := (ne_of_not_colinear not_colinear_ABC).2.2.symm
--Claim $B \ne C$
lemma B_ne_C : B ≠ C := (ne_of_not_colinear not_colinear_ABC).1.symm
--Claim $C \ne A$
lemma C_ne_A : C ≠ A := (ne_of_not_colinear not_colinear_ABC).2.1.symm
--let $D$ be point on the extension of $BC$
variable {D : Plane} {D_int_BC_ext : D LiesInt (SEG_nd B C (B_ne_C (hnd:=hnd)).symm).extension}
--let $E$ be point on the extension of $CA$
variable {E : Plane} {E_int_CA_ext : E LiesInt (SEG_nd C A (C_ne_A (hnd:=hnd)).symm).extension}
--such that $CD = AE$
variable {CD_eq_AE : ((SEG C D).length = (SEG A E).length)}
--Prove that $AD = BE$
theorem Problem1_8_ : ((SEG A D).length = (SEG B E).length):= by
/-
In regular triangle $ABC$, $\angle ABC = \angle BCA$.
Since $D$ lies on the extension of $BC$, we know that $\angle ABD$ is the same as $\angle ABC$.
Since $E$ lies on the extension of $CA$, we know that $\angle BCE$ is the same as $\angle BCA$.
Therefore, $\angle ABD = \angle ABC = \angle BCA = \angle BCE$.
In regular triangle $ABC$, $AB = BC$.
In regular triangle $ABC$, $BC = CA$.
So we have $BD = BC + CD = CA + AE = CE$.
In $\triangle BDA$ and $\triangle CEB$,
$\cdot BD = CE$
$\cdot \angle ABD = \angle BCE$
$\cdot AB = BC$
Thus, $\triangle ABD \cong \triangle BCE$ (by SAS).
Therefore, $BD = CE$.
-/
  have not_colinear_BDA : ¬ colinear B D A := by sorry
  have not_colinear_CEB : ¬ colinear C E B := by sorry
  have D_ne_B : D ≠ B := by sorry
  have A_ne_B : A ≠ B := by sorry
  have E_ne_C : E ≠ C := by sorry
  have B_ne_C : B ≠ C := by sorry
  have A_ne_C : A ≠ C := by sorry
  have AB_eq_BC : (SEG A B).length = (SEG B C).length := hreg.2.symm
  have BC_eq_CA : (SEG B C).length = (SEG C A).length := hreg.1
  have C_on_BD : C LiesOn (SEG B D) := by sorry
  have A_on_CE : A LiesOn (SEG C E) := by sorry
  have angle_DBA_eq_angle_ECB : ∠ D B A D_ne_B A_ne_B = ∠ E C B E_ne_C B_ne_C := by
    calc
    ∠ D B A D_ne_B A_ne_B
    _= ∠ C B A B_ne_C.symm A_ne_B := by
      symm;
      apply eq_ang_val_of_lieson_lieson (B_ne_C.symm) A_ne_B D_ne_B A_ne_B
      · exact lies_int_toray_of_lies_int_ext_of_seg_nd B C D B_ne_C.symm D_int_BC_ext
      · exact Ray.snd_pt_lies_int_mk_pt_pt B A A_ne_B
    _= ∠ A C B A_ne_C B_ne_C := by
      apply (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := (TRI_nd A B C not_colinear_ABC))).mp
      exact Triangle.isoceles_of_regular (▵ A B C) hreg
    _= ∠ E C B E_ne_C B_ne_C := by
      apply eq_ang_val_of_lieson_lieson A_ne_C B_ne_C E_ne_C B_ne_C
      · exact lies_int_toray_of_lies_int_ext_of_seg_nd C A E A_ne_C E_int_CA_ext
      · exact Ray.snd_pt_lies_int_mk_pt_pt C B B_ne_C
  have BD_eq_CE : (SEG B D).length = (SEG C E).length := by
    calc
    (SEG B D).length
    _= (SEG B C).length + (SEG C D).length := by
      apply length_eq_length_add_length
      exact C_on_BD
    _= (SEG C A).length + (SEG C D).length := by rw [BC_eq_CA]
    _= (SEG C A).length + (SEG A E).length := by rw [CD_eq_AE]
    _= (SEG C E).length := by
      symm;apply length_eq_length_add_length
      exact A_on_CE
  have trngl_BDA_congr_trngl_CEB : TriangleND.IsCongr (TRI_nd B D A not_colinear_BDA) (TRI_nd C E B not_colinear_CEB) := by
    apply TriangleND.congr_of_SAS
    · exact AB_eq_BC
    · exact angle_DBA_eq_angle_ECB
    · exact BD_eq_CE
  calc
  (SEG A D).length = (SEG D A).length := by apply length_of_rev_eq_length'
  _= (SEG E B).length := trngl_BDA_congr_trngl_CEB.edge₁
  _= (SEG B E).length := by apply length_of_rev_eq_length'
end Problem1_8_
