import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular_trash

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace SCHAUM_Problem_1_14
/-
Let $ABCD$ be a parallelogram. Let $P$ and $Q$ be points on the segments $AB$ and $CD$, respectively, such that $BP = DQ$. Let $M$ be the foot of the perpendicular from $P$ to the diagonal $BD$, and let $N$ be the foot of the perpendicular from $Q$ to the diagonal $BD$

Prove that $PM = QN$ and $PM \parallel QN$.
-/

structure Setting (Plane : Type _) [EuclideanPlane Plane] where
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
  -- Let $M$ be the foot of the perpendicular from $P$ to the diagonal $BD$.
  M : Plane
  perp_foot_M : M = perp_foot P (LIN B D D_ne_B)
  not_P_lieson_BD : ¬ P LiesOn (LIN B D D_ne_B) := sorry
  -- Let $N$ be the foot of the perpendicular from $Q$ to the diagonal $BD$.
  N : Plane
  perp_foot_N : N = perp_foot Q (LIN B D D_ne_B)

lemma not_P_lieson_BD {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : ¬ e.P LiesOn (LIN e.B e.D e.D_ne_B) := sorry
lemma not_Q_lieson_BD {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : ¬ e.Q LiesOn (LIN e.B e.D e.D_ne_B) := sorry
lemma M_ne_P {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : e.M ≠ e.P := by
  simp only [e.perp_foot_M]
  exact (perp_foot_eq_self_iff_lies_on e.P (LIN e.B e.D e.D_ne_B)).not.mpr (not_P_lieson_BD e)
lemma N_ne_Q {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : e.N ≠ e.Q := by
  simp only [e.perp_foot_N]
  exact (perp_foot_eq_self_iff_lies_on e.Q (LIN e.B e.D e.D_ne_B)).not.mpr (not_Q_lieson_BD e)

-- Prove that $PM = QN$ and $PM \parallel QN$.
theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : (SEG e.P e.M).length = (SEG e.Q e.N).length ∧ (SEG e.P e.M) ∥ (SEG e.Q e.N) := by
  sorry
/-
-- Let $ABCD$ be a parallelogram.
variable {A B C D : Plane} {hprg : Quadrilateral.IsParallelogram (QDR A B C D)}
-- Let $P$ and $Q$ be points on the segments $AB$ and $CD$, respectively, such that $BP = DQ$.
variable {P Q : Plane} {hp : Seg.IsInt P (SEG A B)} {hq : Seg.IsInt Q (SEG C D)} {hpq : (SEG B P).length = (SEG D Q).length}
-- Let $M$ be the foot of the perpendicular from $P$ to the diagonal $BD$.
lemma d_ne_b : D ≠ B := Quadrilateral_cvx.nd₂₄ (Quadrilateral_cvx.mk_is_convex (is_convex_of_is_prg (QDR A B C D) hprg))
lemma hp1 : ¬ (P LiesOn (LIN B D (d_ne_b (hprg := hprg)))) := by sorry
variable {M : Plane} {hm : M = perp_foot P (LIN B D (d_ne_b (hprg := hprg)))}
-- Let $N$ be the foot of the perpendicular from $Q$ to the diagonal $BD$.
lemma hp2 : ¬ (Q LiesOn (LIN B D (d_ne_b (hprg := hprg)))) := by sorry
variable {N : Plane} {hn : N = perp_foot Q (LIN B D (d_ne_b (hprg := hprg)))}
-- State the main goal.
lemma m_ne_p : M ≠ P := by sorry
lemma n_ne_q : N ≠ Q := by sorry
theorem SCHAUM_Problem_1_14 : (SEG P M).length = (SEG Q N).length ∧ ((SEG_nd P M m_ne_p) ∥ (SEG_nd Q N n_ne_q)) := by
  constructor
  · sorry
  · unfold parallel
    have h₁ : (LIN P M m_ne_p) ⟂ (LIN B D (d_ne_b (hprg := hprg))) := by
      rw [hm]
      apply pt_to_perp_foot_perp_line (hp1 (hprg := hprg))
    have h₂ : (LIN Q N m_ne_p) ⟂ (LIN B D (d_ne_b (hprg := hprg))) := by
      rw [hn]
      apply pt_to_perp_foot_perp_line (hp2 (hprg := hprg))
    calc
      _ = toProj (LIN P M m_ne_p) := by sorry
      _ = (toProj (LIN B D (d_ne_b (hprg := hprg)))).perp := h₁
      _ = toProj (LIN Q N n_ne_q) := by rw [← h₂]
      _ = toProj (SEG_nd Q N n_ne_q) := by sorry
-/
end SCHAUM_Problem_1_14
