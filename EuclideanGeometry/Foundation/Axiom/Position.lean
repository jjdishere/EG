import EuclideanGeometry.Foundation.Axiom.Angle

/- This file discuss the relative positions of points and rays on a plane. -/
noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P] 

section colinear

-- Define a special normalize' that maps (0 : Vec) to (1 : Proj)
def colinear_of_nd {A B C : P} (h : ¬((C = B) ∨ (A = C) ∨ (B = A))): Prop := by
  push_neg at h
  exact (Vec_nd.normalize (⟨VEC A B, (ne_iff_vec_ne_zero _ _).mp h.2.2⟩ : Vec_nd)).toProj = (Vec_nd.normalize (⟨VEC A C, (ne_iff_vec_ne_zero _ _).mp h.2.1.symm⟩ : Vec_nd)).toProj

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
    unfold colinear at c
    by_cases (C ≠ A) ∧ (B ≠ C) 
    · have h₁ : C ≠ A := by tauto
      have h₂ : B ≠ C := by tauto
      simp [g, h₁, h₂] at c
      rw [← normalize'_eq_normalize_of_ne_zero ((ne_iff_vec_ne_zero A B).1 g), ← normalize'_eq_normalize_of_ne_zero ((ne_iff_vec_ne_zero A C).1 h₁)] at c
      exact smul_of_eq_toProj c
    · by_cases C = A
      · use 0
        rw [h]
        simp only [vec_same_eq_zero, zero_smul]
      · have h : B = C := by tauto
        use 1
        rw [h]
        simp only [one_smul]
  · intro he
    rcases he with ⟨t, e⟩
    exact colinear_of_vec_eq_smul_vec e

-- Please rewrite this part, use minimal theorems, but create a tactic called `colinearity`
theorem triv_colinear {A C : P} : (colinear A A C) := by
  unfold colinear
  tauto

theorem flip_colinear_snd_trd {A B C : P} (c : colinear A B C) : (colinear A C B) := by 
  by_cases (B ≠ A) ∧ (C ≠ A)
  · have w₁ : B ≠ A := by tauto
    have _ : C ≠ A := by tauto
    rcases (eq_mul_vec_iff_colinear_of_ne w₁).1 c with ⟨t, e⟩
    have ht : t ≠ 0 := by
      by_contra ht'
      rw [ht', zero_smul] at e
      have _ : C = A := ((eq_iff_vec_eq_zero A C).2 e)
      tauto
    exact colinear_of_vec_eq_smul_vec (Eq.symm ((inv_smul_eq_iff₀ ht).2 e))
  · unfold colinear
    tauto

theorem flip_colinear_fst_snd {A B C : P} (c : colinear A B C) : (colinear B A C) := by
  by_cases B = A
  · rw [h]
    tauto
  · rw [eq_mul_vec_iff_colinear_of_ne h] at c
    rcases c with ⟨r, e⟩
    have e' : VEC B C = (1 - r) • VEC B A := by
      rw [← vec_sub_vec A B C, e, ← neg_vec A B, smul_neg, sub_smul, neg_sub, one_smul]
    exact colinear_of_vec_eq_smul_vec e'

-- the proof of this theorem using def of line seems to be easier
theorem colinear_of_colinear_colinear_ne {A B C D: P} (h₁ : colinear A B C) (h₂ : colinear A B D) (h : B ≠ A) : (colinear A C D) := sorry

theorem ne_of_not_colinear {A B C : P} (h : ¬ colinear A B C) : (C ≠ B) ∧ (A ≠ C) ∧ (B ≠ A) := by
  unfold colinear at h
  tauto

end colinear
/- Positions of points on a line, ray, oriented segments. -/

section point_to_ray

def IsOnLeftSide (A : P) (ray : Ray P) : Prop := by
  by_cases A = ray.source
  · exact False
  · exact (0 < (OAngle.mk ray (Ray.mk_pt_pt ray.source A h ) rfl).value) ∧ ((OAngle.mk ray (Ray.mk_pt_pt ray.source A h ) rfl).value ≠ π) 

def IsOnRightSide (A : P) (ray : Ray P) : Prop := by
  by_cases A = ray.source
  · exact False
  · exact ((OAngle.mk ray (Ray.mk_pt_pt ray.source A h ) rfl).value < 0)


end point_to_ray

scoped infix : 50 "LiesOnLeft" => IsOnLeftSide 
scoped infix : 50 "LiesOnRight" => IsOnRightSide 

/- Position of two rays -/
section ray_to_ray

/- Statement of his theorem should change, since ray₀.source ≠ ray₂.source. -/
theorem intersect_of_ray_on_left_iff (ray₁ ray₂ : Ray P) (h : ray₂.source ≠ ray₁.source) : let ray₀ := Ray.mk_pt_pt ray₁.source ray₂.source h; (0 < OAngle.angle_of_two_ray_of_eq_source ray₀ ray₁ rfl) ∧ (OAngle.angle_of_two_ray_of_eq_source ray₀ ray₁ rfl < OAngle.angle_of_two_ray_of_eq_source ray₀ ray₂ sorry) ∧ (OAngle.angle_of_two_ray_of_eq_source ray₀ ray₂ sorry < π) ↔ (∃ A : P, (A LiesOn ray₁) ∧ (A LiesOn ray₂) ∧ (A LiesOnLeft ray₀))  := sorry

end ray_to_ray



/- Position of two lines; need a function to take the intersection of two lines (when they intersect). -/


/- A lot more theorems regarding positions -/
/- e.g. 180 degree implies colinear -/

end EuclidGeom
