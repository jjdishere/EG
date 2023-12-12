import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

namespace Schaum

namespace Problem1_3_
/-Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
Let $D$ and $E$ be two points on $BC$,such that $BD=CE$

Prove that $∠DAB = ∠CAE$.
-/
/--/
--Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : P} {hnd: ¬ colinear A B C} {hisoc: (▵ A B C).IsIsoceles}
--Let $D$ and $E$ be two points on $BC$
variable {D : P} {D_Int_BC: D LiesInt (SEG B C)}
variable {E : P} {E_Int_BC: E LiesInt (SEG B C)}
--such that $BD = CE$.
variable {D_E_seg_position : (SEG B D).length = (SEG C E).length}
--lemma for existance of angle
--Because ▵ A B C is nondegrnerate, $A B C$ is pairwise distinct
lemma b_ne_a : B ≠ A := (ne_of_not_colinear hnd).2.2
lemma c_ne_a : C ≠ A := (ne_of_not_colinear hnd).2.1.symm
lemma a_ne_b : A ≠ B := (ne_of_not_colinear hnd).2.2.symm
lemma a_ne_c : A ≠ C := (ne_of_not_colinear hnd).2.1
lemma b_ne_c : B ≠ C := (ne_of_not_colinear hnd).1.symm
lemma c_ne_b : C ≠ B := (ne_of_not_colinear hnd).1
--Prove that $∠ D A B = ∠ C A E$.
-/
structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  --Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
  A : Plane
  B : Plane
  C : Plane
  not_colinear_ABC : ¬ colinear A B C
  isoc_ABC : (▵ A B C).IsIsoceles
  --Let $D$ and $E$ be two points on $BC$
  D : Plane
  E : Plane
  D_Int_BC : D LiesInt (SEG B C)
  E_Int_BC : E LiesInt (SEG B C)
  BD_eq_CE : (SEG B D).length = (SEG C E).length
  --lemma for existance of angle
  --Because ▵ A B C is nondegrnerate, $A B C$ is pairwise distinct
  B_ne_A : B ≠ A := (ne_of_not_colinear not_colinear_ABC).2.2
  C_ne_A : C ≠ A := (ne_of_not_colinear not_colinear_ABC).2.1.symm
  A_ne_B : A ≠ B := (ne_of_not_colinear not_colinear_ABC).2.2.symm
  A_ne_C : A ≠ C := (ne_of_not_colinear not_colinear_ABC).2.1
  B_ne_C : B ≠ C := (ne_of_not_colinear not_colinear_ABC).1.symm
  C_ne_B : C ≠ B := (ne_of_not_colinear not_colinear_ABC).1
--Points not equal for angles ∠ A B D and ∠ A C E
namespace Setting
lemma D_ne_A {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : e.D ≠ e.A := sorry
lemma E_ne_A {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : e.E ≠ e.A := sorry
lemma D_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : e.D ≠ e.B := e.D_Int_BC.2.1
lemma E_ne_C {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : e.E ≠ e.C := e.E_Int_BC.2.2
end Setting
--Prove that $∠ D A B = ∠ C A E$.
theorem Result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : ∠ e.D e.A e.B (e.D_ne_A) (e.B_ne_A)= ∠ e.C e.A e.E (e.C_ne_A) (e.E_ne_A) := by
  /-In the isoceles triangle $ABC$ we have $AB = AC$.
    Beacause $BD = CE$ we have $DB = EC$.
    In the isoceles triangle $A B C$, we have $\angle A B C = -\angle A C B$.
    Because $\angle A B C = -\angle A C B$ we have $\angle A B D = -\angle A C E$
    In In $\triangle B A D$ and $\triangle B A D$
    $\cdot DB = EC$
    $\cdot \angle A B D = -\angle A C E$
    $\cdot AB = AC$
    Then $\triangle B A D \congr_a \triangle B A D$ (by SAS)
    We have $\angle B A D = -\angle C A E$.
    We have $\angle D A B = \angle C A E$.
  -/
  --In the isoceles triangle $ABC$ $AB = AC$.
  have h₀ : (SEG e.B e.A).length = (SEG e.C e.A).length := by
    calc
      _= (SEG e.A e.B).length := length_of_rev_eq_length' --$BA = AB$ by symmetry
      _= (SEG e.C e.A).length := e.isoc_ABC.symm -- $AB = CA$ by isoceles.
  --Triangle B A D nondegenerate.
  have hnd₁ : ¬ colinear e.B e.A e.D := by sorry
  --Triangle C A E nondegenerate.
  have hnd₂ : ¬ colinear e.C e.A e.E := by sorry
  --Beacause $BD = CE$ we have $DB = EC$.
  have h₁ : (SEG e.D e.B).length = (SEG e.E e.C).length := by
    calc
      _= (SEG e.B e.D).length := length_of_rev_eq_length' --$DB = BD$ by symmetry
      _= (SEG e.C e.E).length := e.BD_eq_CE --$BD = CE$
      _= (SEG e.E e.C).length := length_of_rev_eq_length' --$CE = EC$ by symmetry
  --In the isoceles triangle $A B C$, we have $\angle A B C = -\angle A C B$.
  have h₂₀ : ∠ e.C e.B e.A (e.C_ne_B) (e.A_ne_B) = ∠ e.A e.C e.B (e.A_ne_C) (e.B_ne_C) := by
      apply (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := ⟨▵ e.A e.B e.C, e.not_colinear_ABC⟩)).mp
      exact e.isoc_ABC
  --Because $\angle A B C = -\angle A C B$ we have $\angle A B D = -\angle A C E$
  have A_int_ray_BA : e.A LiesInt (RAY e.B e.A e.A_ne_B) := by
    sorry
  have D_int_ray_BC : e.D LiesInt (RAY e.B e.C e.C_ne_B) := by
    rw [← pt_pt_seg_toRay_eq_pt_pt_ray]
    apply SegND.lies_int_toRay_of_lies_int
    exact e.D_Int_BC
  have A_int_ray_CA : e.A LiesInt (RAY e.C e.A e.A_ne_C) := by
    sorry
  have E_int_ray_CB : e.E LiesInt (RAY e.C e.B e.B_ne_C) := by
    rw [← pt_pt_seg_toRay_eq_pt_pt_ray]
    apply SegND.lies_int_toRay_of_lies_int
    apply SegND.lies_int_rev_iff_lies_int.mp
    exact e.E_Int_BC
  have h₂ : ∠ e.A e.B e.D (e.A_ne_B) (e.D_ne_B) = -∠ e.A e.C e.E (e.A_ne_C) (e.E_ne_C) := by
    have h₂₁ : ∠ e.A e.B e.D (e.A_ne_B) (e.D_ne_B) = -∠ e.C e.B e.A (e.C_ne_B) (e.A_ne_B) := by
      rw [← neg_value_of_rev_ang (e.A_ne_B) (e.C_ne_B)]
      have inner_h₂₁ : ∠  e.A e.B e.D (e.A_ne_B) (e.D_ne_B) = ∠  e.A e.B e.C (e.A_ne_B) (e.C_ne_B) := by
        symm
        apply eq_ang_val_of_lieson_lieson
        ·exact A_int_ray_BA
        .exact D_int_ray_BC
      simp only [inner_h₂₁]
    have h₂₂ : ∠ e.A e.C e.E (e.A_ne_C) (e.E_ne_C) = ∠ e.A e.C e.B (e.A_ne_C) (e.B_ne_C) := by
      have inner_h₂₂ : ∠  e.A e.C e.E (e.A_ne_C) (e.E_ne_C) = ∠  e.A e.C e.B (e.A_ne_C) (e.B_ne_C) := by
        symm
        apply eq_ang_val_of_lieson_lieson
        ·exact A_int_ray_CA
        ·exact E_int_ray_CB
      simp only [inner_h₂₂]
    simp only [h₂₁]
    simp only [h₂₂]
    simp only [← h₂₀]
  --Then $\triangle B A D \congr_a \triangle B A D$ (by SAS)
  have h₃ : TRI_nd e.B e.A e.D hnd₁ ≅ₐ TRI_nd e.C e.A e.E hnd₂ := by
    apply TriangleND.acongr_of_SAS
    · exact h₁
    · exact h₂
    · exact h₀
  --We have $\angle B A D = -\angle C A E$.
  have h₄ : ∠ e.D e.A e.B (e.D_ne_A) (e.B_ne_A) = -∠ e.E e.A e.C (e.E_ne_A) (e.C_ne_A) := by
    exact h₃.angle₂
  --We have $\angle D A B = \angle C A E$.
  have h₅ : ∠ e.D e.A e.B (e.D_ne_A) (e.B_ne_A) = ∠ e.C e.A e.E (e.C_ne_A) (e.E_ne_A) := by
    rw[h₄]
    symm
    exact neg_value_of_rev_ang (e.C_ne_A) (e.E_ne_A)
  exact h₅
end Problem1_3_
end Schaum
