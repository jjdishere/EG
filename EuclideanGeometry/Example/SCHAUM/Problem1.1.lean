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
  /-In the isoceles triangle $ABC$, we have $AB = AC$.
    Meanwhile $AE = AD$
    We have $BD = AB - AD = AC - AE = CE$.
    In the isoceles triangle $A B C$, we have $\angle A B C = -\angle A C B$.
    Because $\angle A B C = -\angle A C B$ we have $\angle D B M = -\angle E C M$
    Because M is the midpoint of BC, we have MB = MC.
    In $\triangle BDM$ and $\triangle CEM$,
    $\cdot BD = CE$
    $\cdot \angle DBM = - \angle ECM$
    $\cdot MB = MC$
    Thus $\triangle DBM \congr_a \triangle ECM$ (by SAS).
    We have $DM = EM$
  -/
  --In the isoceles triangle $ABC$ $AB = AC$.
  have h₀ : (SEG A B).length = (SEG A C).length := by
    calc
      _ = (SEG C A).length := hisoc.symm
      _ = (SEG A C).length := length_of_rev_eq_length'
  --Triangle B D M nondegenerate.
  have h₁ : ¬ colinear B D M := by sorry
  --Triangle C E M nondegenerate.
  have h₂ : ¬ colinear C E M := by sorry
  --Points not equal for the definition of angle is not invalid.
  --$D \ne B$ and $M \ne B$ for ∠ D B M.
  have d_ne_b : D ≠ B := (ne_of_not_colinear h₁).2.2
  have m_ne_b : M ≠ B := (ne_of_not_colinear h₁).2.1.symm
  --$E \ne C$ and $M \ne C$ for ∠ E C M
  have e_ne_c : E ≠ C := (ne_of_not_colinear h₂).2.2
  have m_ne_c : M ≠ C := (ne_of_not_colinear h₂).2.1.symm
  --$A \ne B$ and $C \ne B$ and $A \ne C$ and $B \ne C$ in nondegenerate triangle $A B C$.
  have a_ne_b : A ≠ B := (ne_of_not_colinear hnd).2.2.symm
  have c_ne_b : C ≠ B := (ne_of_not_colinear hnd).1
  have a_ne_c : A ≠ C := (ne_of_not_colinear hnd).2.1
  have b_ne_c : B ≠ C := (ne_of_not_colinear hnd).1.symm
  --We have $BD = AB - AD = AC - AE = CE$.
  have h₃ : (SEG B D).length = (SEG C E).length := by
    calc
      (SEG B D).length = (SEG D B).length := length_of_rev_eq_length' --$BD = DB$ by symmetry
      _=(SEG A B).length - (SEG A D).length := by -- $DB = AB - AD$ since $D$ lies on $AB$,
        rw [← eq_sub_of_add_eq']
        symm
        exact (length_eq_length_add_length (D_on_seg))
      _= (SEG A C).length - (SEG A D).length := by rw [h₀] --$AB = AC$
      _= (SEG A C).length - (SEG A E).length := by rw [E_ray_position] --We have $AB - AD = AC - AE$,because $AE = AD$
      _= (SEG E C).length := by -- $AC - AE = EC$ since $E$ lies on $AC$.
        rw [← eq_sub_of_add_eq']
        symm
        exact (length_eq_length_add_length (E_on_seg))
      _= (SEG C E).length := length_of_rev_eq_length' --$EC = CE$ by symmetry
  --Because M is the midpoint of BC, we have MB = MC.
  have h₄ : (SEG M B).length = (SEG M C).length := by
    have h₄₁ : (SEG M B).length = (SEG B M).length := length_of_rev_eq_length'
    rw[h₄₁]
    rw [median_M_position]
    apply dist_target_eq_dist_source_of_midpt
  --Because $\angle A B C = -\angle A C B$ we have $\angle D B M = -\angle E C M$
  have h₅₀ : ∠ C B A (c_ne_b) (a_ne_b) = ∠ A C B (a_ne_c) (b_ne_c) := by
      apply (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := ⟨▵ A B C, hnd⟩)).mp
      exact hisoc
  have h₅ : ∠ D B M (d_ne_b) (m_ne_b) = -∠ E C M (e_ne_c) (m_ne_c) := by
    have h₅₁ : -∠ E C M (e_ne_c) (m_ne_c) = -∠ A C B (a_ne_c) (b_ne_c) := by
      sorry
    have h₅₂ : ∠ D B M (d_ne_b) (m_ne_b) = -∠ C B A (c_ne_b) (a_ne_b) := by
      sorry
    rw [h₅₁]
    rw [h₅₂]
    rw [h₅₀]
  --Thus $\triangle DBM \congr_a \triangle ECM$ (by SAS).
  have h₆ :  TRI_nd B D M h₁ ≅ₐ TRI_nd C E M h₂ := by
    apply Triangle_nd.acongr_of_SAS
    · exact h₄
    · exact h₅
    · exact h₃
  --We have $DM = EM$
  exact h₆.edge₁
end Problem_1_1
