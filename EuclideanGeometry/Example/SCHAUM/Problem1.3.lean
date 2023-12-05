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
variable {A B C : P} {hnd: ¬ colinear A B C} {hisoc: (▵ A B C).IsIsoceles}
--Let $D$ and $E$ be two points on $BC$
variable {D : P} {D_on_seg: D LiesInt (SEG A B)}
variable {E : P} {E_on_seg: E LiesInt (SEG A B)}
--such that $BD = CE$.
variable {D_E_seg_position : (SEG B D).length = (SEG C E).length}
--lemma for existance of angle
--B ≠ A and C ≠ A by hnd
lemma B_ne_a : B ≠ A := (ne_of_not_colinear hnd).2.2
lemma c_ne_a : C ≠ A := (ne_of_not_colinear hnd).2.1.symm
lemma A_ne_B : A ≠ B := (ne_of_not_colinear hnd).2.2.symm
lemma A_ne_C : A ≠ C := (ne_of_not_colinear hnd).2.1
lemma B_ne_C : B ≠ C := (ne_of_not_colinear hnd).1.symm
lemma c_ne_B : C ≠ B := (ne_of_not_colinear hnd).1
--D ≠ A and E ≠ A
lemma d_ne_a : D ≠ A := sorry
lemma e_ne_a : E ≠ A := sorry
lemma d_ne_B : D ≠ B := sorry
lemma e_ne_C : E ≠ C := sorry
--Prove that $DM = EM$.
theorem Problem1_3_ : ∠ D A B (d_ne_a) (B_ne_a (hnd := hnd))= ∠ C A E (c_ne_a (hnd := hnd)) (e_ne_a) := by
  --the first edge of congruence
  have h₀ : (SEG B A).length = (SEG C A).length := by
    calc
      _= (SEG A B).length := sorry -- length_eq_length_of_rev (SEG B A)
      _= (SEG C A).length := hisoc.symm
  have hnd₁ : ¬ colinear B A D := by sorry
  have hnd₂ : ¬ colinear C A E := by sorry
  have h₁ : (SEG D B).length = (SEG E C).length := by
    calc
      _= (SEG B D).length := sorry -- length_eq_length_of_rev (SEG D B)
      _= (SEG C E).length := D_E_seg_position
      _= (SEG E C).length := sorry --length_eq_length_of_rev (SEG C E)
  have h₂ : ∠ A B D (a_ne_b (hnd := hnd)) (d_ne_b) = -∠ A C E (a_ne_c (hnd := hnd)) (e_ne_c) := by
    have h₂₁ : ∠ A B D (a_ne_b (hnd := hnd)) (d_ne_b) = -∠ C B A (c_ne_b (hnd := hnd)) (a_ne_b (hnd := hnd)) := by sorry
    have h₂₂ : ∠ A C E (a_ne_c (hnd := hnd)) (e_ne_c) = ∠ A C B (a_ne_c (hnd := hnd)) (b_ne_c (hnd := hnd)) := by sorry
    rw[h₂₁]
    rw[h₂₂]
    have h₂₀ : ∠ C B A (c_ne_B (hnd := hnd)) (A_ne_B (hnd := hnd)) = ∠ A C B (A_ne_C (hnd := hnd)) (B_ne_C (hnd := hnd)) := by
      apply (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := ⟨▵ A B C, hnd⟩)).mp
      exact hisoc
    rw[← h₂₀]
  have h₃ : TRI_nd B A D hnd₁ ≅ₐ TRI_nd C A E hnd₂ := by
    apply Triangle_nd.acongr_of_SAS
    · exact h₁
    · exact h₂
    · exact h₀
  have h₄ : ∠ D A B (d_ne_a) (B_ne_a (hnd := hnd))= -∠ E A C (e_ne_a) (c_ne_a (hnd := hnd)) := by
    exact h₃.angle₂
  rw[h₄]
  have h₅ : ∠ C A E (c_ne_a (hnd := hnd)) (e_ne_a) = -∠ E A C (e_ne_a) (c_ne_a (hnd := hnd)) := by
    exact neg_value_of_rev_ang (c_ne_a (hnd := hnd)) (e_ne_a)
  rw[h₅]
end Problem1_3_
