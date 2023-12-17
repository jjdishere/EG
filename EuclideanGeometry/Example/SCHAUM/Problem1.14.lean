import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel_trash

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace SCHAUM_Problem_1_14
/-
Let $ABCD$ be a parallelogram. Let $P$ and $Q$ be points on the segments $AB$ and $CD$, respectively, such that $BP = DQ$. Let $M$ be the foot of perpendicular from $P$ to the diagonal $BD$, and let $N$ be the foot of perpendicular from $Q$ to the diagonal $BD$

Prove that $PM = QN$ and $PM \parallel QN$.
-/

structure Setting1 (Plane : Type _) [EuclideanPlane Plane] where
  -- Let $ABCD$ be a parallelogram.
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  ABCD_IsPRG : (QDR A B C D) IsPRG_nd
  -- Let $P$ and $Q$ be points on the segments $AB$ and $CD$, respectively, such that $BP = DQ$.
  P : Plane
  Q : Plane
  P_int_AB : P LiesInt SEG A B
  Q_int_CD : Q LiesInt SEG C D
  BP_eq_DQ : (SEG B P).length = (SEG D Q).length
  D_ne_B : D ≠ B := nd₂₄_of_is_prg_nd (QDR A B C D) ABCD_IsPRG
  -- Let $M$ be the foot of perpendicular from $P$ to the diagonal $BD$.
  M : Plane
  perp_foot_M : M = perp_foot P (LIN B D D_ne_B)
  -- Let $N$ be the foot of perpendicular from $Q$ to the diagonal $BD$.
  N : Plane
  perp_foot_N : N = perp_foot Q (LIN B D D_ne_B)

-- Because $P$ is not on line $BD$, $M$, the foot of the perpendicular from $P$ to the diagonal $BD$ doesn't equal to $P$.
lemma not_P_lieson_BD {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : ¬ e.P LiesOn (LIN e.B e.D e.D_ne_B) := sorry
lemma not_Q_lieson_BD {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : ¬ e.Q LiesOn (LIN e.B e.D e.D_ne_B) := sorry
lemma M_ne_P {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : e.M ≠ e.P := by
  simp only [e.perp_foot_M]
  exact (perp_foot_eq_self_iff_lies_on e.P (LIN e.B e.D e.D_ne_B)).not.mpr (not_P_lieson_BD)
lemma N_ne_Q {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : e.N ≠ e.Q := by
  simp only [e.perp_foot_N]
  exact (perp_foot_eq_self_iff_lies_on e.Q (LIN e.B e.D e.D_ne_B)).not.mpr (not_Q_lieson_BD)

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends (Setting1 Plane) where
  not_P_lieson_BD : ¬ P LiesOn (LIN B D D_ne_B) := not_P_lieson_BD
  not_Q_lieson_BD : ¬ Q LiesOn (LIN B D D_ne_B) := not_Q_lieson_BD
  M_ne_P : M ≠ P := M_ne_P
  N_ne_Q : N ≠ Q := N_ne_Q

-- Prove that $PM = QN$.
theorem result1 {Plane : Type _} [EuclideanPlane Plane] (e : Setting2 Plane) : (SEG e.P e.M).length = (SEG e.Q e.N).length := by
  /- Because quadrilateral $ABCD$ is a parallelogram, $AB \parallel CD$, thus the alternate interior angle $\angle ABD = \angle CDB$,
  therefore $\angle PBM = \angle ABD = \angle CDB = \angle QDN$. Also, $\angle BMP = \pm\frac{\pi}{2}$, $\angle DNQ = \pm\frac{\pi}{2}$
  because $M$ and $N$ are the foot of perpendicular from $P$, $Q$ to $BD$, respectively.
  In $\triangle MBP$ and $\triangle NDQ$,
  $\bullet \qquad \angle BMP = \angle DNQ \mod \pi$
  $\bullet \qquad \angle PBM = \angle QDN$
  $\bullet \qquad BP = DQ$
  Thus $\triangle MBP \congr \triangle NCQ$ (by AAS),
  which implies $PM = QN$.
  -/
  have not_colinear_MBP : ¬ colinear e.M e.B e.P := by sorry
  have not_colinear_NDQ : ¬ colinear e.N e.D e.Q := by sorry
  have B_ne_M : e.B ≠ e.M := by sorry
  have P_ne_M : e.P ≠ e.M := by sorry
  have D_ne_N : e.D ≠ e.N := by sorry
  have Q_ne_N : e.Q ≠ e.N := by sorry
  -- have
  have ang_BMP_eq_ang_DNQ_mod_pi : (ANG e.B e.M e.P B_ne_M P_ne_M).dvalue = (ANG e.D e.N e.Q D_ne_N Q_ne_N).dvalue := by sorry

  have MBP_congr_NCQ : (TRI_nd e.M e.B e.P not_colinear_MBP).IsCongr (TRI_nd e.N e.D e.Q not_colinear_NDQ) := by sorry
  exact MBP_congr_NCQ.edge₂

-- Prove that $PM \parallel QN$.
theorem result2 {Plane : Type _} [EuclideanPlane Plane] (e : Setting2 Plane) : (LIN e.P e.M e.M_ne_P) ∥ (LIN e.Q e.N e.N_ne_Q) := by
  -- We have $PM \perp BD$ because $M$ is the perpendicular foot from $P$ to $BD$.
  have PM_perp_BD : LIN e.P e.M e.M_ne_P ⟂ LIN e.B e.D e.D_ne_B := by
    simp only [e.perp_foot_M]
    exact line_of_self_perp_foot_perp_line_of_not_lies_on e.not_P_lieson_BD
  -- We have $BD \perp QN$ because $N$ is the perpendicular foot from $Q$ to $BD$.
  have BD_perp_QN : LIN e.B e.D e.D_ne_B ⟂ LIN e.Q e.N e.N_ne_Q := by
    simp only [e.perp_foot_N]
    exact perpendicular.symm (line_of_self_perp_foot_perp_line_of_not_lies_on e.not_Q_lieson_BD)
  -- then $PM \perp QN$ because $PM \perp BD$ and $BD \perp QN$.
  exact parallel_of_perp_perp (l₂ := (LIN e.B e.D e.D_ne_B)) PM_perp_BD BD_perp_QN

end SCHAUM_Problem_1_14
