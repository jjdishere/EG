import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Schaum

namespace Problem1_1
/-Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.Let $D$ be a point on $AB$.
Let $E$ be a point on $AC$ such that $AE = AD$. Let $M$ be the midpoint of $BC$.

Prove that $DM = EM$.
-/
/--/
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
-/
structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  --Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
  A : Plane
  B : Plane
  C : Plane
  not_colinear_ABC : ¬ colinear A B C
  isoc_ABC : (▵ A B C).IsIsoceles
  --Let $D$ be a point on $AB$.
  D : Plane
  D_Int_seg : D LiesInt (SEG A B)
  --Let $E$ be a point on $AC$
  E : Plane
  E_Int_seg : E LiesInt (SEG A C)
  --such that $AE = AD$.
  AE_eq_AD : (SEG A E).length = (SEG A D).length
  --Let $M$ be the midpoint of $BC$.
  M : Plane
  midpoint_M : M = (SEG B C).midpoint

--Prove that $DM = EM$.
theorem Result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : (SEG e.D e.M).length = (SEG e.E e.M).length := by
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
  have h₀ : (SEG e.A e.B).length = (SEG e.A e.C).length := by
    calc
      _ = (SEG e.C e.A).length := e.isoc_ABC.symm
      _ = (SEG e.A e.C).length := length_of_rev_eq_length'
  --Triangle B D M nondegenerate.
  have h₁ : ¬ colinear e.B e.D e.M := by sorry
  --Triangle C E M nondegenerate.
  have h₂ : ¬ colinear e.C e.E e.M := by sorry
  --Points not equal for the definition of angle is not invalid.
  --$D \ne B$ and $M \ne B$ for ∠ D B M.
  have d_ne_b : e.D ≠ e.B := (ne_of_not_colinear h₁).2.2
  have m_ne_b : e.M ≠ e.B := (ne_of_not_colinear h₁).2.1.symm
  --$E \ne C$ and $M \ne C$ for ∠ E C M
  have e_ne_c : e.E ≠ e.C := (ne_of_not_colinear h₂).2.2
  have m_ne_c : e.M ≠ e.C := (ne_of_not_colinear h₂).2.1.symm
  --$A \ne B$ and $C \ne B$ and $A \ne C$ and $B \ne C$ in nondegenerate triangle $A B C$.
  have a_ne_b : e.A ≠ e.B := (ne_of_not_colinear e.not_colinear_ABC).2.2.symm
  have c_ne_b : e.C ≠ e.B := (ne_of_not_colinear e.not_colinear_ABC).1
  have a_ne_c : e.A ≠ e.C := (ne_of_not_colinear e.not_colinear_ABC).2.1
  have b_ne_c : e.B ≠ e.C := (ne_of_not_colinear e.not_colinear_ABC).1.symm
  --We have $BD = AB - AD = AC - AE = CE$.
  have h₃ : (SEG e.B e.D).length = (SEG e.C e.E).length := by
    calc
      (SEG e.B e.D).length = (SEG e.D e.B).length := length_of_rev_eq_length' --$BD = DB$ by symmetry
      _=(SEG e.A e.B).length - (SEG e.A e.D).length := by -- $DB = AB - AD$ since $D$ lies on $AB$,
        rw [← eq_sub_of_add_eq']
        symm
        exact (length_eq_length_add_length (e.D_Int_seg))
      _= (SEG e.A e.C).length - (SEG e.A e.D).length := by rw [h₀] --$AB = AC$
      _= (SEG e.A e.C).length - (SEG e.A e.E).length := by rw [e.AE_eq_AD] --We have $AB - AD = AC - AE$,because $AE = AD$
      _= (SEG e.E e.C).length := by -- $AC - AE = EC$ since $E$ lies on $AC$.
        rw [← eq_sub_of_add_eq']
        symm
        exact (length_eq_length_add_length (e.E_Int_seg))
      _= (SEG e.C e.E).length := length_of_rev_eq_length' --$EC = CE$ by symmetry
  --Because M is the midpoint of BC, we have MB = MC.
  have h₄ : (SEG e.M e.B).length = (SEG e.M e.C).length := by
    have h₄₁ : (SEG e.M e.B).length = (SEG e.B e.M).length := length_of_rev_eq_length'
    rw[h₄₁]
    rw [e.midpoint_M]
    apply dist_target_eq_dist_source_of_midpt
  --Because $\angle A B C = -\angle A C B$ we have $\angle D B M = -\angle E C M$
  have h₅₀ : ∠ e.C e.B e.A (c_ne_b) (a_ne_b) = ∠ e.A e.C e.B (a_ne_c) (b_ne_c) := by
      apply (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := ⟨▵ e.A e.B e.C, e.not_colinear_ABC⟩)).mp
      exact e.isoc_ABC
  have M_int_BC : e.M LiesInt (SEG_nd e.B e.C c_ne_b) := by
    sorry
    --exact (SegND_eq_midpoint_iff_in_seg_and_dist_target_eq_dist_source.mp midpoint_M').1
  have D_int_ray_BA : e.D LiesInt (RAY e.B e.A a_ne_b) := by
    rw [← pt_pt_seg_toRay_eq_pt_pt_ray]
    apply SegND.lies_int_toRay_of_lies_int
    apply SegND.lies_int_rev_iff_lies_int.mp
    exact e.D_Int_seg
  have M_int_ray_BC : e.M LiesInt (RAY e.B e.C c_ne_b) := by
    rw [← pt_pt_seg_toRay_eq_pt_pt_ray]
    apply SegND.lies_int_toRay_of_lies_int
    exact M_int_BC
  have E_int_ray_CA : e.E LiesInt (RAY e.C e.A a_ne_c) := by
    rw [← pt_pt_seg_toRay_eq_pt_pt_ray]
    apply SegND.lies_int_toRay_of_lies_int
    apply SegND.lies_int_rev_iff_lies_int.mp
    exact e.E_Int_seg
  have M_int_ray_CB : e.M LiesInt (RAY e.C e.B b_ne_c) := by
    rw [← pt_pt_seg_toRay_eq_pt_pt_ray]
    apply SegND.lies_int_toRay_of_lies_int
    have M_int_CB : e.M LiesInt (SEG_nd e.C e.B b_ne_c) := by
      apply SegND.lies_int_rev_iff_lies_int.mp
      exact M_int_BC
  have h₅ : ∠ e.D e.B e.M (d_ne_b) (m_ne_b) = -∠ e.E e.C e.M (e_ne_c) (m_ne_c) := by
    have h₅₁ : -∠ e.E e.C e.M (e_ne_c) (m_ne_c) = -∠ e.A e.C e.B (a_ne_c) (b_ne_c) := by
      have inner_h₅₁ : ∠  e.E e.C e.M (e_ne_c) (m_ne_c) = ∠  e.A e.C e.B (a_ne_c) (b_ne_c) := by
        symm
        apply eq_ang_val_of_lieson_lieson
        · exact E_int_ray_CA
        · exact M_int_ray_CB
      simp only [inner_h₅₁]
    have h₅₂ : ∠ e.D e.B e.M (d_ne_b) (m_ne_b) = -∠ e.C e.B e.A (c_ne_b) (a_ne_b) := by
      rw [← neg_value_of_rev_ang (a_ne_b) (c_ne_b)]
      have inner_h₅₂ : ∠  e.D e.B e.M (d_ne_b) (m_ne_b) = ∠  e.A e.B e.C (a_ne_b) (c_ne_b) := by
        symm
        apply eq_ang_val_of_lieson_lieson
        · exact D_int_ray_BA
        · exact M_int_ray_BC
      simp only [inner_h₅₂]
    rw [h₅₁]
    rw [h₅₂]
    rw [h₅₀]
  --Thus $\triangle DBM \congr_a \triangle ECM$ (by SAS).
  have h₆ :  TRI_nd e.B e.D e.M h₁ ≅ₐ TRI_nd e.C e.E e.M h₂ := by
    apply TriangleND.acongr_of_SAS
    · exact h₄
    · exact h₅
    · exact h₃
  --We have $DM = EM$
  exact h₆.edge₁
end Problem1_1
end Schaum
