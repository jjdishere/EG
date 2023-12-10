import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Problem1_3_
/-Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
Let $D$ and $E$ be two points on $BC$,such that $BD=CE$

Prove that $∠DAB = ∠CAE$.
-/
--Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : P} {not_colinear_ABC: ¬ colinear A B C} {isoceles_ABC: (▵ A B C).IsIsoceles}
--Let $D$ and $E$ be two points on $BC$
variable {D : P} {D_on_seg: D LiesInt (SEG A B)}
variable {E : P} {E_on_seg: E LiesInt (SEG A B)}
--such that $BD = CE$.
variable {D_E_seg_position : (SEG B D).length = (SEG C E).length}
--lemma for existance of angle
--B ≠ A and C ≠ A by not_colinear_ABC
lemma B_ne_a : B ≠ A := (ne_of_not_colinear not_colinear_ABC).2.2
lemma c_ne_a : C ≠ A := (ne_of_not_colinear not_colinear_ABC).2.1.symm
lemma A_ne_B : A ≠ B := (ne_of_not_colinear not_colinear_ABC).2.2.symm
lemma A_ne_C : A ≠ C := (ne_of_not_colinear not_colinear_ABC).2.1
lemma B_ne_C : B ≠ C := (ne_of_not_colinear not_colinear_ABC).1.symm
lemma c_ne_B : C ≠ B := (ne_of_not_colinear not_colinear_ABC).1
--D ≠ A and E ≠ A
lemma d_ne_a : D ≠ A := sorry
lemma e_ne_a : E ≠ A := sorry
lemma d_ne_B : D ≠ B := sorry
lemma e_ne_C : E ≠ C := sorry
--Prove that $DM = EM$.
theorem Problem1_3_ : ∠ D A B (d_ne_a) (B_ne_a (not_colinear_ABC := not_colinear_ABC))= ∠ C A E (c_ne_a (not_colinear_ABC := not_colinear_ABC)) (e_ne_a) := by
  --the first edge of congruence
  have h₀ : (SEG B A).length = (SEG C A).length := by
    calc
      _= (SEG A B).length := sorry -- length_eq_length_of_rev (SEG B A)
      _= (SEG C A).length := isoceles_ABC.symm
  have not_colinear_ABC₁ : ¬ colinear B A D := by sorry
  have not_colinear_ABC₂ : ¬ colinear C A E := by sorry
  have h₁ : (SEG D B).length = (SEG E C).length := by
    calc
      _= (SEG B D).length := sorry -- length_eq_length_of_rev (SEG D B)
      _= (SEG C E).length := D_E_seg_position
      _= (SEG E C).length := sorry --length_eq_length_of_rev (SEG C E)
  have h₂ : ∠ A B D (a_ne_b (not_colinear_ABC := not_colinear_ABC)) (d_ne_b) = -∠ A C E (a_ne_c (not_colinear_ABC := not_colinear_ABC)) (e_ne_c) := by
    have h₂₁ : ∠ A B D (a_ne_b (not_colinear_ABC := not_colinear_ABC)) (d_ne_b) = -∠ C B A (c_ne_b (not_colinear_ABC := not_colinear_ABC)) (a_ne_b (not_colinear_ABC := not_colinear_ABC)) := by sorry
    have h₂₂ : ∠ A C E (a_ne_c (not_colinear_ABC := not_colinear_ABC)) (e_ne_c) = ∠ A C B (a_ne_c (not_colinear_ABC := not_colinear_ABC)) (b_ne_c (not_colinear_ABC := not_colinear_ABC)) := by sorry
    rw[h₂₁]
    rw[h₂₂]
    have h₂₀ : ∠ C B A (c_ne_B (not_colinear_ABC := not_colinear_ABC)) (A_ne_B (not_colinear_ABC := not_colinear_ABC)) = ∠ A C B (A_ne_C (not_colinear_ABC := not_colinear_ABC)) (B_ne_C (not_colinear_ABC := not_colinear_ABC)) := by
      apply (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := ⟨▵ A B C, not_colinear_ABC⟩)).mp
      exact isoceles_ABC
    rw[← h₂₀]
  have h₃ : TRI_nd B A D not_colinear_ABC₁ ≅ₐ TRI_nd C A E not_colinear_ABC₂ := by
    apply Triangle_nd.acongr_of_SAS
    · exact h₁
    · exact h₂
    · exact h₀
  have h₄ : ∠ D A B (d_ne_a) (B_ne_a (not_colinear_ABC := not_colinear_ABC))= -∠ E A C (e_ne_a) (c_ne_a (not_colinear_ABC := not_colinear_ABC)) := by
    exact h₃.angle₂
  rw[h₄]
  have h₅ : ∠ C A E (c_ne_a (not_colinear_ABC := not_colinear_ABC)) (e_ne_a) = -∠ E A C (e_ne_a) (c_ne_a (not_colinear_ABC := not_colinear_ABC)) := by
    exact neg_value_of_rev_ang (c_ne_a (not_colinear_ABC := not_colinear_ABC)) (e_ne_a)
  rw[h₅]
end Problem1_3_
