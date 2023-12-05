import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Problem_1_1
/-Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.Let $D$ be a point on $AB$.
Let $E$ be a point on $AC$ such that $AE = AD$. Let $M$ be the midpoint of $BC$.

Prove that $DM = EM$.
-/
--Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : P} {hnd: ¬ colinear A B C} {hisoc: (▵ A B C).IsIsoceles}
--Let $D$ be a point on $AB$.
variable {D : P} {D_on_seg: D LiesInt (SEG A B)}
--Let $E$ be a point on $AC$
variable {E : P} {E_on_seg: E LiesInt (SEG A C)}
--such that $AE = AD$.
variable {E_ray_position : (SEG A E).length = (SEG A D).length}
--Let $M$ be the midpoint of $BC$.
variable {M : P} {median_M_position : M = (SEG B C).midpoint}
--Prove that $DM = EM$.
theorem Problem_1_1 : (SEG D M).length = (SEG E M).length := by
  have h₀ : (SEG A B).length = (SEG A C).length := by
    calc
      _ = (SEG C A).length := hisoc.symm
      _ = (SEG A C).length := sorry -- length_eq_length_of_rev (SEG C A)
  have h₁ : ¬ colinear B D M := by sorry
  have h₂ : ¬ colinear C E M := by sorry
  --to confirm the definition of angle is not invalid
  have d_ne_B : D ≠ B := (ne_of_not_colinear h₁).2.2
  have m_ne_B : M ≠ B := (ne_of_not_colinear h₁).2.1.symm
  have e_ne_C : E ≠ C := (ne_of_not_colinear h₂).2.2
  have m_ne_C : M ≠ C := (ne_of_not_colinear h₂).2.1.symm
  have A_ne_B : A ≠ B := (ne_of_not_colinear hnd).2.2.symm
  have c_ne_B : C ≠ B := (ne_of_not_colinear hnd).1
  have A_ne_C : A ≠ C := (ne_of_not_colinear hnd).2.1
  have B_ne_C : B ≠ C := (ne_of_not_colinear hnd).1.symm
  --the second edge of congruence
  have h₃ : (SEG B D).length = (SEG C E).length := by
    calc
      (SEG B D).length = (SEG D B).length := sorry --length_eq_length_of_rev (SEG B D)
      _=(SEG A B).length - (SEG A D).length := by
        rw [← eq_sub_of_add_eq']
        rw []
        sorry -- exact (length_eq_length_add_length (SEG A B) D (D_on_seg)).symm
      _= (SEG A C).length - (SEG A D).length := by rw [h₀]
      _= (SEG A C).length - (SEG A E).length := by rw [E_ray_position]
      _= (SEG E C).length := by
        rw [← eq_sub_of_add_eq']
        sorry --exact (length_eq_length_add_length (SEG A C) E (E_on_seg)).symm
      _= (SEG C E).length := sorry -- length_eq_length_of_rev (SEG E C)
  have h₄ : (SEG M B).length = (SEG M C).length := by
    have h₄₁ : (SEG M B).length = (SEG B M).length := sorry --length_eq_length_of_rev (SEG M B)
    rw[h₄₁]
    rw [median_M_position]
    apply dist_target_eq_dist_source_of_midpt
  have h₅ : ∠ D B M (d_ne_B) (m_ne_B) = -∠ E C M (e_ne_C) (m_ne_C) := by
    have h₅₁ : -∠ E C M (e_ne_C) (m_ne_C) = -∠ A C B (A_ne_C) (B_ne_C) := by
      sorry
    rw [h₅₁]
    have h₅₂ : ∠ D B M (d_ne_B) (m_ne_B) = -∠ C B A (c_ne_B) (A_ne_B) := by
      sorry
    rw [h₅₂]
    have h₅₃ : ∠ C B A (c_ne_B) (A_ne_B) = ∠ A C B (A_ne_C) (B_ne_C) := by
      apply (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := ⟨▵ A B C, hnd⟩)).mp
      exact hisoc
    rw [h₅₃]
  have h₆ :  TRI_nd B D M h₁ ≅ₐ TRI_nd C E M h₂ := by
    apply Triangle_nd.acongr_of_SAS
    · exact h₄
    · exact h₅
    · exact h₃

  exact h₆.edge₁
end Problem_1_1
