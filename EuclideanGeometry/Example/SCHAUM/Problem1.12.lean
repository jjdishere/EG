import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace SCHAUM_Problem_1_12
/-
Let $ABCD$ is a convex quadrilateral. Assume that the diagonal $BD \perp BC$ and $BD \perp DA$.
Suppose that $BC = DA$.

Prove that $ABCD$ is a parallelogram.
-/

-- Let $ABCD$ is a convex quadrilateral.
variable {A B C D : Plane} {hconv : Quadrilateral.IsConvex (QDR A B C D)}
-- The diagonal $BD \perp BC$.
lemma d_ne_B : D ≠ B := Quadrilateral_cvx.nd₂₄ (Quadrilateral_cvx.mk_is_convex hconv)
lemma c_ne_B : C ≠ B := Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex hconv)
variable {hperp1 : (SEG_nd B D (d_ne_B (hconv := hconv))) ⟂ (SEG_nd B C (c_ne_B (hconv := hconv)))}
-- The diagonal $BD \perp DA$.
lemma A_ne_d : A ≠ D := (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex hconv)).symm
variable {hperp2 : (SEG_nd B D (d_ne_B (hconv := hconv))) ⟂ (SEG_nd A D (A_ne_d (hconv := hconv)).symm)}
-- $BC = DA$.
variable {heq : (SEG B C).length = (SEG A D).length}
-- State the main goal.
theorem SCHAUM_Problem_1_12 : Quadrilateral.IsParallelogram (QDR A B C D) := by
  apply is_prg_of_para_eq_length'
  · unfold perpendicular at *
    unfold parallel
    have h : toProj (SEG_nd B C (c_ne_B (hconv := hconv))) = toProj (SEG_nd A D (A_ne_d (hconv := hconv)).symm) := by
      calc
        _ = (toProj (SEG_nd B C (c_ne_B (hconv := hconv)))).perp.perp := by simp
        _ = (toProj (SEG_nd B D (d_ne_B (hconv := hconv)))).perp := by
          congr
          exact hperp1.symm
        _ = (toProj (SEG_nd A D (A_ne_d (hconv := hconv)).symm)).perp.perp := by congr
        _ = toProj (SEG_nd A D (A_ne_d (hconv := hconv)).symm) := by simp
    exact h.symm
  · exact heq.symm
  · exact hconv

end SCHAUM_Problem_1_12
