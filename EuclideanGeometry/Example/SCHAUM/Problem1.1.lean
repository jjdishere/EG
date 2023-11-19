import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Problem1_1_
/-Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.Let $D$ be a point on $AB$.
Let $E$ be a point on $AC$ such that $AE = AD$. Let $M$ be the midpoint of $BC$.

Prove that $DM = EM$.
-/
--Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : P} {hnd: ¬ colinear A B C} {hisoc: (▵ A B C).IsIsoceles}
--Let $D$ be a point on $AB$.
variable {D : P} {D_on_seg: D LiesInt (SEG A B)}
--Let $E$ be a point on $AC$
variable {E : P} {E_on_seg: E LiesInt (SEG A B)}
--such that $AE = AD$.
variable {E_ray_position : (SEG A E).length = (SEG A D).length}
--Let $M$ be the midpoint of $BC$.
variable {M : P} {median_M_position : M = (SEG B C).midpoint}
--Prove that $DM = EM$.
theorem Problem1_1_ : (SEG D M).length = (SEG E M).length := by
  have h₀ : (SEG A B).length = (SEG A C).length := by sorry
  have h₁ : ¬ colinear B D M := by sorry
  have h₂ : ¬ colinear C E M := by sorry
  have d_ne_b : D ≠ B := (ne_of_not_colinear h₁).2.2
  have m_ne_b : M ≠ B := (ne_of_not_colinear h₁).2.1.symm
  have e_ne_c : E ≠ C := (ne_of_not_colinear h₂).2.2
  have m_ne_c : M ≠ C := (ne_of_not_colinear h₂).2.1.symm
  have h₃ : (SEG B D).length = (SEG C E).length := by
    calc
      (SEG B D).length = (SEG A B).length - (SEG A D).length := by
        have h₇ : (SEG A B).length = (SEG A D).length
        sorry
      _= (SEG A C).length - (SEG A D).length := by rw [h₀]
      _= (SEG A C).length - (SEG A E).length := by rw [E_ray_position]
      _= (SEG C E).length := by sorry
  have h₄ : (SEG M B).length = (SEG M C).length := by
    rw [median_M_position]
    sorry
  have h₅ : ∠ D B M (d_ne_b) (m_ne_b) = -∠ E C M (e_ne_c) (m_ne_c) := by sorry
  have h₆ :  TRI_nd B D M h₁ ≅ₐ TRI_nd C E M h₂ := by
    apply Triangle_nd.acongr_of_SAS
    · exact h₄
    · exact h₅
    · exact h₃
  have h : (SEG D M).length = (SEG E M).length := by
    exact h₆.edge₁
  exact h
end Problem1_1_
