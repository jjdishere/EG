import EuclideanGeometry.Foundation.Axiom.Basic.Plane

/- This file discuss the relative positions of points and rays on a plane. -/
noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P] 

section colinear

-- Define a special normalize' that maps (0 : Vec) to (1 : Proj)
def colinear_of_nd {A B C : P} (h : ¬((C = B) ∨ (A = C) ∨ (B = A))): Prop := by
  push_neg at h
  exact Vec_nd.toProj ⟨VEC A B, (ne_iff_vec_ne_zero _ _).mp h.2.2⟩ = Vec_nd.toProj ⟨VEC A C, (ne_iff_vec_ne_zero _ _).mp h.2.1.symm⟩

def colinear (A B C : P) : Prop := by
  by_cases (C = B) ∨ (A = C) ∨ (B = A)
  · exact True
  · exact colinear_of_nd h

-- The definition of colinear now includes two cases: the degenerate case and the nondegenerate case. We use normalize' to avoid problems involving using conditions of an "if" in its "then" and "else". And we only use VEC to define colinear. 

theorem colinear_of_vec_eq_smul_vec {A B C : P} {t : ℝ} (e : VEC A C = t • VEC A B) : colinear A B C := by 
  have : colinear A B C = True := by
    unfold colinear
    apply dite_eq_left_iff.mpr
    simp only [eq_iff_iff, iff_true]
    intro h'
    push_neg at h'
    unfold colinear_of_nd
    exact (eq_toProj_of_smul ⟨_, (ne_iff_vec_ne_zero A B).1 h'.2.2⟩ ⟨_, ((ne_iff_vec_ne_zero A C).1 h'.2.1.symm)⟩ e)
  tauto

theorem colinear_of_vec_eq_smul_vec' {A B C : P} : (∃ t : ℝ, VEC A C = t • VEC A B) → colinear A B C := by
  intro h
  rcases h with ⟨t, e⟩
  exact colinear_of_vec_eq_smul_vec e

theorem eq_mul_vec_iff_colinear_of_ne {A B C : P} (g : B ≠ A) : colinear A B C ↔ ∃ r : ℝ , VEC A C = r • VEC A B := by
  constructor
  · intro c
    rw [← iff_true (colinear A B C), ← eq_iff_iff] at c
    unfold colinear at c
    rw [dite_eq_left_iff] at c
    by_cases (C = B) ∨ (A = C) ∨ (B = A)
    · by_cases C = A
      · use 0
        rw [h]
        simp only [vec_same_eq_zero, zero_smul]
      · have h : B = C := by tauto
        use 1
        rw [h]
        simp only [one_smul]
    · specialize c h
      push_neg at h
      unfold colinear_of_nd at c
      simp only [ne_eq, eq_iff_iff, iff_true] at c
      exact smul_of_eq_toProj ⟨VEC A B, (ne_iff_vec_ne_zero A B).1 g⟩ ⟨VEC A C, (ne_iff_vec_ne_zero A C).1 h.2.1.symm⟩ c
  · intro he
    rcases he with ⟨t, e⟩
    exact colinear_of_vec_eq_smul_vec e

-- Please rewrite this part, use minimal theorems, but create a tactic called `colinearity`
theorem triv_colinear (A C : P) : (colinear A A C) := by
  rw [← iff_true (colinear A A C), ← eq_iff_iff]
  unfold colinear
  rw [dite_eq_left_iff]
  intro h
  push_neg at h
  exfalso
  exact h.2.2 rfl

theorem flip_colinear_snd_trd {A B C : P} (c : colinear A B C) : (colinear A C B) := by 
  by_cases (B ≠ A) ∧ (C ≠ A)
  · rcases (eq_mul_vec_iff_colinear_of_ne h.1).1 c with ⟨t, e⟩
    have ht : t ≠ 0 := by
      by_contra ht'
      rw [ht', zero_smul] at e
      have _ : C = A := ((eq_iff_vec_eq_zero A C).2 e)
      tauto
    exact colinear_of_vec_eq_smul_vec (Eq.symm ((inv_smul_eq_iff₀ ht).2 e))
  · rw [← iff_true (colinear _ _ _), ← eq_iff_iff]
    unfold colinear
    rw [dite_eq_left_iff]
    intro g
    exfalso
    push_neg at *
    exact g.2.2 $ h g.2.1.symm

theorem flip_colinear_fst_snd {A B C : P} (c : colinear A B C) : (colinear B A C) := by
  by_cases B = A
  · rw [h]
    exact triv_colinear _ _
  · rw [eq_mul_vec_iff_colinear_of_ne h] at c
    rcases c with ⟨r, e⟩
    have e' : VEC B C = (1 - r) • VEC B A := by
      rw [← vec_sub_vec A B C, e, ← neg_vec A B, smul_neg, sub_smul, neg_sub, one_smul]
    exact colinear_of_vec_eq_smul_vec e'

-- the proof of this theorem using def of line seems to be easier
theorem colinear_of_colinear_colinear_ne {A B C D: P} (h₁ : colinear A B C) (h₂ : colinear A B D) (h : B ≠ A) : (colinear A C D) := sorry

theorem ne_of_not_colinear {A B C : P} (h : ¬ colinear A B C) : (C ≠ B) ∧ (A ≠ C) ∧ (B ≠ A) := by
  rw [← iff_true (colinear A B C), ← eq_iff_iff] at h
  unfold colinear at h
  rw [dite_eq_left_iff] at h
  push_neg at h
  rcases h with ⟨g, _⟩
  tauto

end colinear

end EuclidGeom