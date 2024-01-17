import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Wuwowuji_Problem_1_6
/-
In $▵ ABC$, $D, E$ are two different points on side $BC$, $AD = AE$, $∠ BAD = -∠ CAE$.

Prove that $AB = AC$.
-/
-- Define $▵ ABC$.
variable {A B C : P} {hnd1 : ¬ Collinear A B C}
-- $D, E$ are two different points on side $BC$.
variable {D E : P} {hd : D LiesInt SEG B C} {he : E LiesInt SEG B C}
-- nondegenerate
lemma hnd2 : ¬ Collinear A D E := by sorry
lemma a_ne_b : A ≠ B := by sorry
lemma a_ne_d : A ≠ D := by sorry
lemma a_ne_c : A ≠ C := by sorry
lemma a_ne_e : A ≠ E := by sorry
-- $AD = AE$.
variable {hisoc : (TRI_nd A D E hnd2).1.IsIsoceles}
-- $∠ BAD = -∠ CAE$.
variable {hang : ∠ B A D a_ne_b a_ne_d = -∠ C A E a_ne_c a_ne_e}
-- State the main goal.
theorem Wuwowuji_Problem_1_6 : (SEG A B).length = (SEG A C).length := by
  -- nondegenerate
  have hnd3 : ¬ Collinear B D A := by sorry
  have hnd4 : ¬ Collinear C E A := by sorry
  -- Use ASA to prove $▵ BDA ≅ₐ ▵ CEA$.
  have h : (TRI_nd B D A hnd3) ≅ₐ (TRI_nd C E A hnd4) := by
    apply TriangleND.acongr_of_ASA
    · sorry
    · -- $DA = EA$ by condition.
      calc
        _ = (SEG A D).length := length_of_rev_eq_length'
        _ = _ := hisoc.symm
    · -- $∠ BAD = -∠ CAE$ by condition.
      exact hang
  -- $AB = AC$ follows from the congruence.
  exact h.edge₂

end Wuwowuji_Problem_1_6
