import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash

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
variable {A B C : Plane} {hnd : ¬ colinear A B C} {hreg : (▵ A B C).IsRegular}
--Claim $A \ne B$
lemma A_ne_B : A ≠ B := (ne_of_not_colinear hnd).2.2.symm
--Claim $B \ne C$
lemma B_ne_C : B ≠ C := (ne_of_not_colinear hnd).1.symm
--Claim $C \ne A$
lemma c_ne_a : C ≠ A := (ne_of_not_colinear hnd).2.1.symm
--let $D$ be point on the extension of $BC$
variable {D : Plane} {D_int_BC_ext : D LiesInt (SEG_nd B C B_ne_C.symm).extension}
--let $E$ be point on the extension of $CA$
variable {E : Plane} {E_int_CA_ext : E LiesInt (SEG_nd C A c_ne_a.symm).extension}
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
In $\triangle ABD$ and $\triangle BCE$,
$\cdot AB = BC$
$\cdot \angle ABD = \angle BCE$
$\cdot BD = CE$
Thus, $\triangle ABD \cong \triangle BCE$ (by SAS).
Therefore, $BD = CE$.
-/
  have ad_eq_be : (SEG A D).length = (SEG B E).length := by
    have hnd_bda : ¬ colinear B D A := by sorry
    have hnd_ceb : ¬ colinear C E B := by sorry
    have d_ne_B : D ≠ B := by sorry
    have A_ne_B : A ≠ B := by sorry
    have e_ne_C : E ≠ C := by sorry
    have B_ne_C : B ≠ C := by sorry
    have A_ne_C : A ≠ C := by sorry
    have ab_eq_bc : (SEG A B).length = (SEG B C).length := hreg.2.symm
    have bc_eq_ca : (SEG B C).length = (SEG C A).length := hreg.1
    have c_lieson_bd : C LiesOn (SEG B D) := by sorry
    have a_lieson_ce : A LiesOn (SEG C E) := by sorry
    let angle_dba := Angle.mk_pt_pt_pt D B A d_ne_B A_ne_B
    let angle_ecb := Angle.mk_pt_pt_pt E C B e_ne_C B_ne_C
    have angle_dba_eq_angle_ecb : Angle.value angle_dba = Angle.value angle_ecb := by
      calc
      Angle.value angle_dba
      _= ∠ C B A B_ne_C.symm A_ne_B:= by sorry
      _= ∠ A C B A_ne_C B_ne_C := by
        exact is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mp isoceles_of_regular hreg
      _= Angle.value angle_ecb := by sorry
    have bd_eq_ce : (SEG B D).length = (SEG C E).length := by
      calc
      (SEG B D).length
      _= (SEG B C).length + (SEG C D).length := by
        apply length_eq_length_add_length
        exact c_lieson_bd
      _= (SEG C A).length + (SEG C D).length := by rw [bc_eq_ca]
      _= (SEG C A).length + (SEG A E).length := by rw [D_E_F_ray_position.1]
      _= (SEG C E).length := by
        symm;apply length_eq_length_add_length
        exact a_lieson_ce
    have trngl_abd_congr_trngl_bce : Triangle_nd.IsCongr (TRI_nd B D A hnd_bda) (TRI_nd C E B hnd_ceb) := by
      apply Triangle_nd.congr_of_SAS
      · exact ab_eq_bc
      · exact angle_dba_eq_angle_ecb
      · exact bd_eq_ce
    calc
    (SEG A D).length = (SEG D A).length := by apply length_of_rev_eq_length'
    _= (SEG E B).length := trngl_abd_congr_trngl_bce.edge₁
    _= (SEG B E).length := by apply length_of_rev_eq_length'
end Problem1_8_
