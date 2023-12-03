import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Construction.Polygon.Parallelogram_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace Problem1_5_

/-
Let $ABCD$ be a parallelogram, and let $P$, $Q$, $R$, $S$ be points on the segments $AB$, $BC$, $CD$, $DA$, respectively,
such that $AP = CR$ and $AS = CQ$.

Prove that $PQRS$ is a parallelogram.
-/

--Let $ABCD$ be a parallelogram
variable {A B C D : Plane} {hprgnd : (QDR A B C D) IsPRG_nd}
--let $P$ be point on the segment $AB$
variable {P : Plane} {P_int_AB : P LiesInt (SEG A B)}
--let $Q$ be point on the segment $BC$
variable {Q : Plane} {Q_int_BC : Q LiesInt (SEG B C)}
--let $R$ be point on the segment $CD$
variable {R : Plane} {R_int_CD : R LiesInt (SEG C D)}
--let $S$ be point on the segment $DA$
variable {S : Plane} {S_int_DA : S LiesInt (SEG D A)}
--such that $AP = CR$
variable {AP_eq_CR : (SEG A P).length = (SEG C R).length}
--such that $AS = CQ$
variable {AS_eq_CQ : (SEG A S).length = (SEG C Q).length}
--Prove that $PQRS$ is a parallelogram
theorem Problem1_5_ : (QDR P Q R S) IsPRG_nd := by
/-
In parallelogram $ABCD$, we have $AB, DC$ are of the same direction.
Since $P$ lies on $AB$, we have $AP, AB$ are of the same direction.
Since $R$ lies on $CD$, we have $RC, DC$ are of the same direction.
Therefore, $AP, RC$ are of the same direction.
With $AP = CR$, we know that $APCR$ is a parallelogram.

In parallelogram $ABCD$, we have $AD, BC$ are of the same direction.
Since $S$ lies on $AD$, we have $AS, AD$ are of the same direction.
Since $Q$ lies on $BC$, we have $QC, BC$ are of the same direction.
Therefore, $AS, QC$ are of the same direction.
With $AS = CQ$, we know that $ASCQ$ is a parallelogram.

Since $APCR$ is a parallelogram, we know that the midpoint of $PR$ is the same as the midpoint of $AC$.
Since $ASCQ$ is a parallelogram, we know that the midpoint of $QS$ is the same as the midpoint of $AC$.
Therefore, the midpoint of $PR$ is the same as the midpoint of $QS$.
As a consequence, we know that $PQRS$ is a parallelogram.
-/
  have P_ne_A : P ≠ A := by sorry
  have R_ne_C : R ≠ C := by sorry
  have S_ne_A : S ≠ A := by sorry
  have Q_ne_C : Q ≠ C := by sorry
  have B_ne_A : B ≠ A := by sorry
  have C_ne_D : C ≠ D := by sorry
  have not_colinear_APC : ¬ colinear A P C := by sorry
  have isprgnd_APCR : (QDR A P C R) IsPRG_nd := by
    have dir_ap_eq_dir_rc_rev : (SEG_nd A P P_ne_A).toDir = (SEG_nd R C R_ne_C.symm).toDir := by
      calc
      (SEG_nd A P P_ne_A).toDir
      _= (SEG_nd A B B_ne_A).toDir := by sorry
      _= (SEG_nd D C C_ne_D).toDir := by sorry
      _= - (SEG_nd C D C_ne_D.symm).toDir := by apply Seg_nd.todir_of_rev_eq_neg_todir (seg_nd := (SEG_nd C D C_ne_D.symm))
      _= - (SEG_nd C R R_ne_C).toDir := by sorry
      _= (SEG_nd R C R_ne_C.symm).toDir := by symm; apply Seg_nd.todir_of_rev_eq_neg_todir (seg_nd := (SEG_nd C R R_ne_C))
    have AP_eq_RC : (SEG A P).length = (SEG R C).length := by
      calc
      (SEG A P).length = (SEG C R).length := AP_eq_CR
      _= (SEG R C).length := by exact length_of_rev_eq_length' (A := R) (B := C)
    have isprg_APCR : (QDR A P C R) IsPRG := by exact prg_trash.vec_eq_of_eq_dir_and_eq_length P_ne_A R_ne_C.symm dir_ap_eq_dir_rc_rev AP_eq_RC
    exact is_prg_nd_of_is_prg_not_colinear₁₂₃ (QDR A P C R) isprg_APCR not_colinear_APC
  have isprgnd_ASCQ : (QDR A S C Q) IsPRG_nd := by
    sorry
  have midpr_eq_midac : (SEG P R).midpoint = (SEG A C).midpoint := by
    calc
    (SEG P R).midpoint
    _= Quadrilateral_cvx.diag_inx (QDR_cvx A P C R (is_convex_of_is_prg_nd_variant isprgnd_APCR)) := by
      exact (eq_midpt_of_diag_inx_of_is_prg_nd'_variant isprgnd_APCR).symm
    _= (SEG A C).midpoint := by
      exact eq_midpt_of_diag_inx_of_is_prg_nd_variant isprgnd_APCR
  have midac_eq_midqs : (SEG A C).midpoint = (SEG Q S).midpoint := by
    calc
    (SEG A C).midpoint
    _= Quadrilateral_cvx.diag_inx (QDR_cvx A S C Q (is_convex_of_is_prg_nd_variant isprgnd_ASCQ)) := by
      symm
      apply (eq_midpt_of_diag_inx_of_is_prg_nd_variant)
      exact isprgnd_ASCQ
    _= (SEG S Q).midpoint := by
      exact eq_midpt_of_diag_inx_of_is_prg_nd'_variant isprgnd_ASCQ
    _= (SEG Q S).midpoint := midpt_of_rev_eq_midpt S Q
  have isprg_PQRS : (QDR P Q R S) IsPRG := by
    apply prg_trash.is_prg_of_diag_inx_eq_mid_eq_mid_variant_1
    rw [midpr_eq_midac, midac_eq_midqs]
  have not_colinear_PQR : ¬ colinear P Q R := by sorry
  exact is_prg_nd_of_is_prg_not_colinear₁₂₃ (QDR P Q R S) isprg_PQRS not_colinear_PQR
end Problem1_5_
