import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Construction.Polygon.Parallelogram_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Line_trash
import EuclideanGeometry.Foundation.Axiom.Position.Convex_trash

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

  -- We have $P \ne A$.
  have P_ne_A : P ≠ A := by sorry
  -- We have $R \ne C$.
  have R_ne_C : R ≠ C := by sorry
  -- We have $S \ne A$.
  have S_ne_A : S ≠ A := by sorry
  -- We have $Q \ne C$.
  have Q_ne_C : Q ≠ C := by sorry
  -- We have $B \ne A$.
  have B_ne_A : B ≠ A := by sorry
  -- We have $C \ne D$.
  have C_ne_D : C ≠ D := by sorry
  -- We have $D \ne A$.
  have D_ne_A : D ≠ A := by sorry
  -- We have $C \ne B$.
  have C_ne_B : C ≠ B := by sorry
  -- We have that $A, P, C$ is not colinear.
  have not_colinear_APC : ¬ colinear A P C := by sorry
  -- We have that $A, S, C$ is not colinear.
  have not_colinear_ASC : ¬ colinear A S C := by sorry
  -- We have that $S$ lies on $AD$ by applying symmetry to the fact that $S$ lies on $DA$.
  have S_int_AD : S LiesInt (SEG A D) := Seg.lies_int_rev_iff_lies_int.mp S_int_DA
  -- We have that $Q$ lies on $CB$ by applying symmetry to the fact that $Q$ lies on $BC$.
  have Q_int_CB : Q LiesInt (SEG C B) := Seg.lies_int_rev_iff_lies_int.mp Q_int_BC
  -- We have that $APCR$ is a parallelogram.
  have isprgnd_APCR : (QDR A P C R) IsPRG_nd := by
    -- We have that $AP, RC$ are of the same direction.
    have dir_ap_eq_dir_rc_rev : (SEG_nd A P P_ne_A).toDir = (SEG_nd R C R_ne_C.symm).toDir := by
      calc
      (SEG_nd A P P_ne_A).toDir
      -- Since $P$ lies on $AB$, we have $AP, AB$ are of the same direction,
      _= (SEG_nd A B B_ne_A).toDir := by
        symm;
        exact eq_todir_of_lies_int_seg_nd A B P B_ne_A P_int_AB
      -- in parallelogram $ABCD$, we have $AB, DC$ are of the same direction,
      _= (SEG_nd D C C_ne_D).toDir := todir_eq_of_is_prg_nd A B C D hprgnd B_ne_A C_ne_D
      -- $CD, DC$ are of the opposite direction because of symmetry,
      _= - (SEG_nd C D C_ne_D.symm).toDir := by apply SegND.toDir_of_rev_eq_neg_toDir (seg_nd := (SEG_nd C D C_ne_D.symm))
      -- since $R$ lies on $CD$, we have $CR, CD$ are of the same direction,
      _= - (SEG_nd C R R_ne_C).toDir := by simp only [eq_todir_of_lies_int_seg_nd C D R C_ne_D.symm R_int_CD]
      -- $CR, RC$ are of the opposite direction because of symmetry.
      _= (SEG_nd R C R_ne_C.symm).toDir := by symm; apply SegND.toDir_of_rev_eq_neg_toDir (seg_nd := (SEG_nd C R R_ne_C))
    -- We have $AP = RC$.
    have AP_eq_RC : (SEG A P).length = (SEG R C).length := by
      calc
      (SEG A P).length
      -- $AP = CR$ according to our condition.
      _= (SEG C R).length := AP_eq_CR
      -- $CR = RC$ by symmetry.
      _= (SEG R C).length := by exact length_of_rev_eq_length' (A := R) (B := C)
    -- We have that $APCR$ is a parallelogram, because $AP, RC$ are of the same direction and $AP = RC$.
    have isprg_APCR : (QDR A P C R) IsPRG := by exact vec_eq_of_eq_dir_and_eq_length P_ne_A R_ne_C.symm dir_ap_eq_dir_rc_rev AP_eq_RC
    -- Since $A, P, C$ is not colinear, we know that the parallelogram $APCR$ is non-degenerate.
    exact is_prg_nd_of_is_prg_not_colinear₁₂₃ (QDR A P C R) isprg_APCR not_colinear_APC
  -- We have that $ASCQ$ is a parallelogram.
  have isprgnd_ASCQ : (QDR A S C Q) IsPRG_nd := by
    -- We have that $AS, QC$ are of the same direction.
    have dir_as_eq_dir_qc_rev : (SEG_nd A S S_ne_A).toDir = (SEG_nd Q C Q_ne_C.symm).toDir := by
      calc
      (SEG_nd A S S_ne_A).toDir
      -- Since $S$ lies on $AD$, we have $AS, AD$ are of the same direction,
      _= (SEG_nd A D D_ne_A).toDir := by
        symm;
        exact eq_todir_of_lies_int_seg_nd A D S D_ne_A S_int_AD
      -- in parallelogram $ABCD$, we have $AD, BC$ are of the same direction,
      _= (SEG_nd B C C_ne_B).toDir := todir_eq_of_is_prg_nd_variant A B C D hprgnd D_ne_A C_ne_B
      -- $BC, CB$ are of the opposite direction because of symmetry,
      _= - (SEG_nd C B C_ne_B.symm).toDir := by apply SegND.toDir_of_rev_eq_neg_toDir (seg_nd := (SEG_nd C B C_ne_B.symm))
      -- since $Q$ lies on $CB$, we have $CQ, CB$ are of the same direction,
      _= - (SEG_nd C Q Q_ne_C).toDir := by simp only [eq_todir_of_lies_int_seg_nd C B Q C_ne_B.symm Q_int_CB]
      -- $CQ, QC$ are of the opposite direction because of symmetry.
      _= (SEG_nd Q C Q_ne_C.symm).toDir := by symm; apply SegND.toDir_of_rev_eq_neg_toDir (seg_nd := (SEG_nd C Q Q_ne_C))
    -- We have $AS = QC$.
    have AS_eq_QC : (SEG A S).length = (SEG Q C).length := by
      calc
      (SEG A S).length
      -- $AS = CQ$ according to our condition.
      _= (SEG C Q).length := AS_eq_CQ
      -- $CR = RC$ by symmetry.
      _= (SEG Q C).length := by exact length_of_rev_eq_length' (A := Q) (B := C)
    -- We have that $ASCQ$ is a parallelogram, because $AS, QC$ are of the same direction and $AS = QC$.
    have isprg_ASCQ : (QDR A S C Q) IsPRG := by exact vec_eq_of_eq_dir_and_eq_length S_ne_A Q_ne_C.symm dir_as_eq_dir_qc_rev AS_eq_QC
    -- Since $A, S, C$ is not colinear, we know that the parallelogram $ASCQ$ is non-degenerate.
    exact is_prg_nd_of_is_prg_not_colinear₁₂₃ (QDR A S C Q) isprg_ASCQ not_colinear_ASC
  -- We have that the midpoint of $PR$ is the same as the midpoint of $AC$.
  have midpr_eq_midac : (SEG P R).midpoint = (SEG A C).midpoint := by
    calc
    (SEG P R).midpoint
    -- As $APCR$ is a parallelogram, we know that the midpoint of $PR$ is the same as the intersection of the diagonals of $APCR$,
    _= Quadrilateral_cvx.diag_inx (QDR_cvx A P C R (is_convex_of_is_prg_nd_variant isprgnd_APCR)) := by
      exact (eq_midpt_of_diag_inx_of_is_prg_nd'_variant isprgnd_APCR).symm
    -- as $APCR$ is a parallelogram, we know that the intersection of the diagonals of $APCR$ is the same as the midpoint of $AC$.
    _= (SEG A C).midpoint := by
      exact eq_midpt_of_diag_inx_of_is_prg_nd_variant isprgnd_APCR
  -- We have that the midpoint of $AC$ is the same as the midpoint of $QS$.
  have midac_eq_midqs : (SEG A C).midpoint = (SEG Q S).midpoint := by
    calc
    -- As $ASCQ$ is a parallelogram, we know that the midpoint of $AC$ is the same as the intersection of the diagonals of $ASCQ$,
    (SEG A C).midpoint
    _= Quadrilateral_cvx.diag_inx (QDR_cvx A S C Q (is_convex_of_is_prg_nd_variant isprgnd_ASCQ)) := by
      symm
      apply (eq_midpt_of_diag_inx_of_is_prg_nd_variant)
      exact isprgnd_ASCQ
    -- as $ASCQ$ is a parallelogram, we know that the intersection of the diagonals of $ASCQ$ is the same as the midpoint of $SQ$,
    _= (SEG S Q).midpoint := by
      exact eq_midpt_of_diag_inx_of_is_prg_nd'_variant isprgnd_ASCQ
    -- the midpoint of $SQ$ is the same as the midpoint of $QS$ by symmetry.
    _= (SEG Q S).midpoint := midpt_of_rev_eq_midpt S Q
  have cvx_ABCD : (QDR A B C D).IsConvex := by
    by_contra h; unfold Quadrilateral.IsParallelogram_nd at hprgnd;
    absurd hprgnd; simp only [h, dite_false, not_false_eq_true]
  -- We have that $PQRS$ is convex, since it's inscribed to the parallelogram $ABCD$ which is convex.
  have cvx_PQRS : (QDR P Q R S).IsConvex := cvx_of_inscribed_to_cvx cvx_ABCD P_int_AB Q_int_BC R_int_CD S_int_DA
  -- We have that $PQRS$ is a parallelogram because the the midpoint of $PR$ and the midpoint of $QS$ are both the same as the midpoint of $AC$.
  apply is_prg_nd_of_diag_inx_eq_mid_eq_mid_variant_1 cvx_PQRS
  simp only [midpr_eq_midac, midac_eq_midqs]
  -- Since $PQRS$ is convex, we know that the parallelogram $PQRS$ is non-degenerate.
end Problem1_5_
