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

/-
-- Let $ABCD$ be a parallelogram.
variable {A B C D : Plane} {hprg : Quadrilateral.IsParallelogram (QDR A B C D)}
-- Let $P$ and $Q$ be points on the segments $AB$ and $CD$, respectively, such that $BP = DQ$.
variable {P Q : Plane} {hp : Seg.IsInt P (SEG A B)} {hq : Seg.IsInt Q (SEG C D)} {hpq : (SEG B P).length = (SEG D Q).length}
-- Let $M$ be the foot of the perpendicular from $P$ to the diagonal $BD$.
lemma d_ne_b : D ≠ B := Quadrilateral_cvx.nd₂₄ (Quadrilateral_cvx.mk_is_convex (is_convex_of_is_prg hprg))
lemma hp1 : ¬ (P LiesOn (LIN B D (d_ne_b (hprg := hprg)))) := by sorry
variable {M : Plane} {hm : M = perp_foot P (LIN B D d_ne_b)}
-- Let $N$ be the foot of the perpendicular from $Q$ to the diagonal $BD$.
lemma hp2 : ¬ (Q LiesOn (LIN B D (d_ne_b (hprg := hprg)))) := by sorry
variable {N : Plane} {hn : N = perp_foot Q (LIN B D d_ne_b)}
-- State the main goal.
lemma m_ne_p : M ≠ P := by sorry
lemma n_ne_q : N ≠ Q := by sorry
theorem SCHAUM_Problem_1_14 : (SEG P M).length = (SEG Q N).length ∧ ((SEG_nd P M m_ne_p) ∥ (SEG_nd Q N n_ne_q)) := by
  constructor
  · sorry
  · unfold parallel
    have h₁ : (LIN P M m_ne_p) ⟂ (LIN B D (d_ne_b (hprg := hprg))) := by
      rw [hm]
      apply line_of_self_perp_foot_perp_line_of_not_lies_on (hp1 (hprg := hprg))
      · sorry
      · sorry
      · sorry
    have h₂ : (LIN Q N m_ne_p) ⟂ (LIN B D (d_ne_b (hprg := hprg))) := by sorry
    calc
      _ = toProj (LIN P M m_ne_p) := by sorry
      _ = (toProj (LIN B D (d_ne_b (hprg := hprg)))).perp := by sorry
      _ = toProj (LIN Q N n_ne_q) := by sorry
      _ = toProj (SEG_nd Q N n_ne_q) := by sorry
-/
end SCHAUM_Problem_1_14
