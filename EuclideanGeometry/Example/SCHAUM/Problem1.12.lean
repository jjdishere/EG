import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace SCHAUM_Problem_1_12
/-
Let $ABCD$ be a convex quadrilateral. Assume that the diagonal $BD \perp BC$ and $BD \perp DA$.
Suppose that $BC = DA$.

Prove that $ABCD$ is a parallelogram.
-/


structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  -- Let $ABCD$ be a convex quadrilateral.
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  ABCD_IsCvx : Quadrilateral.IsConvex (QDR A B C D)
  -- $A, B, C, D$ are pairwise distinct because $ABCD$ is convex.
  D_ne_B : D ≠ B := Quadrilateral_cvx.nd₂₄ (Quadrilateral_cvx.mk_is_convex ABCD_IsCvx)
  C_ne_B : C ≠ B := Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex ABCD_IsCvx)
  A_ne_D : A ≠ D := (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex ABCD_IsCvx)).symm
  -- Assume that the diagonal $BD \perp BC$ and $BD \perp DA$.
  BD_perp_BC : (SEG_nd B D D_ne_B) ⟂ (SEG_nd B C C_ne_B)
  BD_perp_DA : (SEG_nd B D D_ne_B) ⟂ (SEG_nd D A A_ne_D)
  -- Suppose that $BC = DA$.
  BC_eq_DA : (SEG B C).length = (SEG D A).length

-- Prove that $ABCD$ is a parallelogram.
theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : (QDR e.A e.B e.C e.D) IsPRG_nd := by
  sorry



-- Let $ABCD$ is a convex quadrilateral.
variable {A B C D : Plane} {hconv : Quadrilateral.IsConvex (QDR A B C D)}
-- The diagonal $BD \perp BC$.
lemma d_ne_b : D ≠ B := Quadrilateral_cvx.nd₂₄ (Quadrilateral_cvx.mk_is_convex hconv)
lemma c_ne_b : C ≠ B := Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex hconv)
variable {hperp1 : (SEG_nd B D (d_ne_b (hconv := hconv))) ⟂ (SEG_nd B C (c_ne_b (hconv := hconv)))}
-- The diagonal $BD \perp DA$.
lemma a_ne_d : A ≠ D := (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex hconv)).symm
variable {hperp2 : (SEG_nd B D (d_ne_b (hconv := hconv))) ⟂ (SEG_nd A D (a_ne_d (hconv := hconv)).symm)}
-- $BC = DA$.
variable {heq : (SEG B C).length = (SEG A D).length}
-- State the main goal.
theorem SCHAUM_Problem_1_12 : Quadrilateral.IsParallelogram (QDR A B C D) := by
  sorry
  /-
  apply is_prg_of_para_eq_length'
  · unfold perpendicular at *
    unfold parallel
    have h : toProj (SEG_nd B C (c_ne_b (hconv := hconv))) = toProj (SEG_nd A D (a_ne_d (hconv := hconv)).symm) := by
      calc
        _ = (toProj (SEG_nd B C (c_ne_b (hconv := hconv)))).perp.perp := by simp
        _ = (toProj (SEG_nd B D (d_ne_b (hconv := hconv)))).perp := by
          congr
          exact hperp1.symm
        _ = (toProj (SEG_nd A D (a_ne_d (hconv := hconv)).symm)).perp.perp := by congr
        _ = toProj (SEG_nd A D (a_ne_d (hconv := hconv)).symm) := by simp
    exact h.symm
  · exact heq.symm
  · exact hconv
  -/

end SCHAUM_Problem_1_12
