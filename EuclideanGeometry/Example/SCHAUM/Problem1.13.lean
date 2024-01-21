import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type*} [EuclideanPlane Plane]

namespace SCHAUM_Problem_1_13
/-
Let $ABCD$ be a parallelogram in which the diagonals $AC$ and $BD$ meet at $M$. Let $P$ and $Q$ be points on $AM$ and $MC$, respectively, such that $MP = MQ$.

Prove that $PBQD$ is a parallelogram.
-/

-- Let $ABCD$ be a parallelogram.
variable {A B C D : Plane} {hprg : Quadrilateral.IsParallelogram (QDR A B C D)}
-- The diagonals $AC$ and $BD$ meet at $M$.
variable {M : Plane} {hm : M = Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg hprg))}
-- Let $P$ and $Q$ be points on $AM$ and $MC$, respectively, such that $MP = MQ$.
variable {P Q : Plane} {hp : Seg.IsInt P (SEG A M)} {hq : Seg.IsInt Q (SEG M C)} {hpq : (SEG P M).length = (SEG M Q).length}
-- State the main goal.
theorem SCHAUM_Problem_1_13 : Quadrilateral.IsParallelogram (QDR P B Q D) := by
  have m1 : M = (SEG B D).midpoint := by
    rw [hm]
    sorry
    -- apply eq_midpt_of_diag_inx_of_is_prg'
    -- · sorry
    -- · exact hprg
  have m2 : M = (SEG P Q).midpoint := by
    sorry
    -- apply (eq_midpoint_iff_in_seg_and_dist_target_eq_dist_source M (SEG P Q)).mpr
    -- constructor
    -- · sorry
    -- · simp
    --   exact hpq
  sorry
  -- apply is_prg_of_diag_inx_eq_mid_eq_mid
  -- rw [← m1, ← m2]

end SCHAUM_Problem_1_13
