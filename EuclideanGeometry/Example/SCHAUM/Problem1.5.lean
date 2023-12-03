import EuclideanGeometry.Foundation.Index

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
  have p_ne_a : P ≠ A := by sorry
  have r_ne_C : R ≠ C := by sorry
  have s_ne_a : S ≠ A := by sorry
  have q_ne_C : Q ≠ C := by sorry
  have isprg_apcr : (QDR A P C R) IsPRG := by
  --need thm : para_of_lieson_para
  --convex requirement needs to be removed from thm
    have ap_para_cr : (SEG_nd A P p_ne_a) ∥ (SEG_nd C R r_ne_C) := by sorry
    apply is_prg_of_para_eq_length_variant
    · sorry
    · exact P_R_position
  have isprg_ascq : (QDR A S C Q) IsPRG := by
    have as_para_cq : (SEG_nd A S s_ne_a) ∥ (SEG_nd C Q q_ne_C) := by sorry
    apply is_prg_of_para_eq_length_variant
    · sorry
    · exact S_Q_position
  have midpr_eq_midac : (SEG P R).midpoint = (SEG A C).midpoint := by
    calc
    (SEG P R).midpoint
    _= Quadrilateral_cvx.diag_inx (QDR_cvx A P C R (is_convex_of_is_prg_variant isprg_apcr)) := by
      exact (eq_midpt_of_diag_inx_of_is_prg'_variant isprg_apcr).symm
    _= (SEG A C).midpoint := by
      exact eq_midpt_of_diag_inx_of_is_prg_variant isprg_apcr
  have midac_eq_midqs : (SEG A C).midpoint = (SEG Q S).midpoint := by
    calc
    (SEG A C).midpoint
    _= Quadrilateral_cvx.diag_inx (QDR_cvx A S C Q (is_convex_of_is_prg_variant isprg_ascq)) := by
      symm
      apply (eq_midpt_of_diag_inx_of_is_prg_variant)
      exact isprg_ascq
    _= (SEG S Q).midpoint := by
      exact eq_midpt_of_diag_inx_of_is_prg'_variant isprg_ascq
    _= (SEG Q S).midpoint := by sorry
  apply is_prg_of_diag_inx_eq_mid_eq_mid_variant
  · sorry
  · rw [midpr_eq_midac, midac_eq_midqs]
end Problem1_5_
