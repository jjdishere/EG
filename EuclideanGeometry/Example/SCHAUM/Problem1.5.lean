import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Construction.Polygon.Parallelogram_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Line_trash
import EuclideanGeometry.Foundation.Axiom.Position.Convex_trash

noncomputable section

namespace EuclidGeom

namespace Schaum

namespace Problem1_5

/-
Let $ABCD$ be a parallelogram, and let $P$, $Q$, $R$, $S$ be points on the segments $AB$, $BC$, $CD$, $DA$, respectively,
such that $AP = CR$ and $AS = CQ$.

Prove that $PQRS$ is a parallelogram.
-/
structure Setting (Plane : Type*) [EuclideanPlane Plane] where
--Let $ABCD$ be a parallelogram
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  hprgnd : (QDR A B C D).IsParallelogram_nd
--let $P$ be point on the segment $AB$
  P : Plane
  P_int_AB : P LiesInt (SEG A B)
--let $Q$ be point on the segment $BC$
  Q : Plane
  Q_int_BC : Q LiesInt (SEG B C)
--let $R$ be point on the segment $CD$
  R : Plane
  R_int_CD : R LiesInt (SEG C D)
--let $S$ be point on the segment $DA$
  S : Plane
  S_int_DA : S LiesInt (SEG D A)
--such that $AP = CR$
  AP_eq_CR : (SEG A P).length = (SEG C R).length
--such that $AS = CQ$
  AS_eq_CQ : (SEG A S).length = (SEG C Q).length
--Prove that $PQRS$ is a parallelogram
theorem result {Plane : Type*} [EuclideanPlane Plane] (e : Setting Plane) : (QDR e.P e.Q e.R e.S).IsParallelogram_nd := by
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
  haveI P_ne_A : PtNe e.P e.A := by sorry
  -- We have $R \ne C$.
  haveI R_ne_C : PtNe e.R e.C := by sorry
  -- We have $S \ne A$.
  haveI S_ne_A : PtNe e.S e.A := by sorry
  -- We have $Q \ne C$.
  haveI Q_ne_C : PtNe e.Q e.C := by sorry
  -- We have $B \ne A$.
  haveI B_ne_A : PtNe e.B e.A := by sorry
  -- We have $C \ne D$.
  haveI C_ne_D : PtNe e.C e.D := by sorry
  -- We have $D \ne A$.
  haveI D_ne_A : PtNe e.D e.A := by sorry
  -- We have $C \ne B$.
  haveI C_ne_B : PtNe e.C e.B := by sorry
  -- We have that $A, P, C$ is not colinear.
  have not_colinear_APC : ¬ colinear e.A e.P e.C := by sorry
  -- We have that $A, S, C$ is not colinear.
  have not_colinear_ASC : ¬ colinear e.A e.S e.C := by sorry
  -- We have that $S$ lies on $AD$ by applying symmetry to the fact that $S$ lies on $DA$.
  have S_int_AD : e.S LiesInt (SEG e.A e.D) := Seg.lies_int_rev_iff_lies_int.mp e.S_int_DA
  -- We have that $Q$ lies on $CB$ by applying symmetry to the fact that $Q$ lies on $BC$.
  have Q_int_CB : e.Q LiesInt (SEG e.C e.B) := Seg.lies_int_rev_iff_lies_int.mp e.Q_int_BC
  -- We have that $APCR$ is a parallelogram.
  have isprgnd_APCR : (QDR e.A e.P e.C e.R).IsParallelogram_nd := by
    -- We have that $AP, RC$ are of the same direction.
    have dir_ap_eq_dir_rc_rev : (SEG_nd e.A e.P).toDir = (SEG_nd e.R e.C ).toDir := by
      calc
      (SEG_nd e.A e.P).toDir
      -- Since $P$ lies on $AB$, we have $AP, AB$ are of the same direction,
      _= (SEG_nd e.A e.B).toDir := by
        symm;
        exact eq_todir_of_lies_int_seg_nd e.A e.B e.P e.P_int_AB
      -- in parallelogram $ABCD$, we have $AB, DC$ are of the same direction,
      _= (SEG_nd e.D e.C).toDir := todir_eq_of_is_prg_nd e.A e.B e.C e.D e.hprgnd
      -- $CD, DC$ are of the opposite direction because of symmetry,
      _= - (SEG_nd e.C e.D).toDir := by apply SegND.toDir_of_rev_eq_neg_toDir (seg_nd := (SEG_nd e.C e.D))
      -- since $R$ lies on $CD$, we have $CR, CD$ are of the same direction,
      _= - (SEG_nd e.C e.R).toDir := by simp only [eq_toDir_of_lies_int_seg_nd e.C e.D e.R e.R_int_CD]
      -- $CR, RC$ are of the opposite direction because of symmetry.
      _= (SEG_nd e.R e.C).toDir := by symm; apply SegND.toDir_of_rev_eq_neg_toDir (seg_nd := (SEG_nd e.C e.R))
    -- We have $AP = RC$.
    have AP_eq_RC : (SEG e.A e.P).length = (SEG e.R e.C).length := by
      calc
      (SEG e.A e.P).length
      -- $AP = CR$ according to our condition.
      _= (SEG e.C e.R).length := e.AP_eq_CR
      -- $CR = RC$ by symmetry.
      _= (SEG e.R e.C).length := by exact length_of_rev_eq_length' (A := e.R) (B := e.C)
    -- We have that $APCR$ is a parallelogram, because $AP, RC$ are of the same direction and $AP = RC$.
    have isprg_APCR : (QDR e.A e.P e.C e.R).IsParallelogram := by exact vec_eq_of_eq_dir_and_eq_length dir_ap_eq_dir_rc_rev AP_eq_RC
    -- Since $A, P, C$ is not colinear, we know that the parallelogram $APCR$ is non-degenerate.
    exact is_prg_nd_of_is_prg_not_colinear₁₂₃ (QDR e.A e.P e.C e.R) isprg_APCR not_colinear_APC
  -- We have that $ASCQ$ is a parallelogram.
  have isprgnd_ASCQ : (QDR e.A e.S e.C e.Q) IsPRG_nd := by
    -- We have that $AS, QC$ are of the same direction.
    have dir_as_eq_dir_qc_rev : (SEG_nd e.A e.S).toDir = (SEG_nd e.Q e.C).toDir := by
      calc
      (SEG_nd e.A e.S).toDir
      -- Since $S$ lies on $AD$, we have $AS, AD$ are of the same direction,
      _= (SEG_nd e.A e.D).toDir := by
        symm;
        exact eq_todir_of_lies_int_seg_nd e.A e.D e.S S_int_AD
      -- in parallelogram $ABCD$, we have $AD, BC$ are of the same direction,
      _= (SEG_nd e.B e.C).toDir := todir_eq_of_is_prg_nd_variant e.A e.B e.C e.D e.hprgnd
      -- $BC, CB$ are of the opposite direction because of symmetry,
      _= - (SEG_nd e.C e.B).toDir := by apply SegND.toDir_of_rev_eq_neg_toDir (seg_nd := (SEG_nd e.C e.B))
      -- since $Q$ lies on $CB$, we have $CQ, CB$ are of the same direction,
      _= - (SEG_nd e.C e.Q).toDir := by simp only [eq_todir_of_lies_int_seg_nd e.C e.B e.Q Q_int_CB]
      -- $CQ, QC$ are of the opposite direction because of symmetry.
      _= (SEG_nd e.Q e.C).toDir := by symm; apply SegND.toDir_of_rev_eq_neg_toDir (seg_nd := (SEG_nd e.C e.Q))
    -- We have $AS = QC$.
    have AS_eq_QC : (SEG e.A e.S).length = (SEG e.Q e.C).length := by
      calc
      (SEG e.A e.S).length
      -- $AS = CQ$ according to our condition.
      _= (SEG e.C e.Q).length := e.AS_eq_CQ
      -- $CR = RC$ by symmetry.
      _= (SEG e.Q e.C).length := by exact length_of_rev_eq_length' (A := e.Q) (B := e.C)
    -- We have that $ASCQ$ is a parallelogram, because $AS, e.QC$ are of the same direction and $AS = QC$.
    have isprg_ASCQ : (QDR e.A e.S e.C e.Q).IsParallelogram_nd := by exact vec_eq_of_eq_dir_and_eq_length S_ne_A Q_ne_C.symm dir_as_eq_dir_qc_rev AS_eq_QC
    -- Since $A, S, C$ is not collinear, we know that the parallelogram $ASCQ$ is non-degenerate.
    exact is_prg_nd_of_is_prg_not_collinear₁₂₃ (QDR e.A e.S e.C e.Q) isprg_ASCQ not_collinear_ASC
  -- We have that the midpoint of $PR$ is the same as the midpoint of $AC$.
  have midpr_eq_midac : (SEG e.P e.R).midpoint = (SEG e.A e.C).midpoint := by
    calc
    (SEG e.P e.R).midpoint
    -- As $APCR$ is a parallelogram, we know that the midpoint of $PR$ is the same as the intersection of the diagonals of $APCR$,
    _= Quadrilateral_cvx.diag_inx (QDR_cvx e.A e.P e.C e.R (is_convex_of_is_prg_nd_variant isprgnd_APCR)) := by
      exact (eq_midpt_of_diag_inx_of_is_prg_nd'_variant isprgnd_APCR).symm
    -- as $APCR$ is a parallelogram, we know that the intersection of the diagonals of $APCR$ is the same as the midpoint of $AC$.
    _= (SEG e.A e.C).midpoint := by
      exact eq_midpt_of_diag_inx_of_is_prg_nd_variant isprgnd_APCR
  -- We have that the midpoint of $AC$ is the same as the midpoint of $QS$.
  have midac_eq_midqs : (SEG e.A e.C).midpoint = (SEG e.Q e.S).midpoint := by
    calc
    -- As $ASCQ$ is a parallelogram, we know that the midpoint of $AC$ is the same as the intersection of the diagonals of $ASCQ$,
    (SEG e.A e.C).midpoint
    _= Quadrilateral_cvx.diag_inx (QDR_cvx e.A e.S e.C e.Q (is_convex_of_is_prg_nd_variant isprgnd_ASCQ)) := by
      symm
      apply (eq_midpt_of_diag_inx_of_is_prg_nd_variant)
      exact isprgnd_ASCQ
    -- as $ASCQ$ is a parallelogram, we know that the intersection of the diagonals of $ASCQ$ is the same as the midpoint of $SQ$,
    _= (SEG e.S e.Q).midpoint := by
      exact eq_midpt_of_diag_inx_of_is_prg_nd'_variant isprgnd_ASCQ
    -- the midpoint of $SQ$ is the same as the midpoint of $QS$ by symmetry.
    _= (SEG e.Q e.S).midpoint := (SEG e.Q e.S).reverse_midpt_eq_midpt
  -- We have that $ABCD$ is convex, since it's a nondegenerate parallelogram.
  have hprgnd' : (QDR e.A e.B e.C e.D) IsPRG_nd := e.hprgnd
  have cvx_ABCD : (QDR e.A e.B e.C e.D).IsConvex := by
    by_contra h; unfold Quadrilateral.IsParallelogram_nd at hprgnd';
    absurd hprgnd'; simp only [h, dite_false, not_false_eq_true]
  -- We have that $PQRS$ is convex, since it's inscribed to the parallelogram $ABCD$ which is convex.
  have cvx_PQRS : (QDR e.P e.Q e.R e.S).IsConvex := cvx_of_inscribed_to_cvx cvx_ABCD e.P_int_AB e.Q_int_BC e.R_int_CD e.S_int_DA
  -- We have that $PQRS$ is a nondegenerate parallelogram because the the midpoint of $PR$ and the midpoint of $QS$ are both the same as the midpoint of $AC$, and that $PQRS$ is convex.
  apply is_prg_nd_of_diag_inx_eq_mid_eq_mid_variant_1 cvx_PQRS
  simp only [midpr_eq_midac, midac_eq_midqs]
end Problem1_5
