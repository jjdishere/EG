import EuclideanGeometry.Foundation.Axiom.Angle

/- This file discuss the relative positions of points and rays on a plane. -/
noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P] 

section colinear

-- Define a special normalize' that maps (0 : Vec) to (1 : Proj)

def normalize' (v : Vec) : Dir := by
  let v' := if v = 0 then (1, 0) else v
  have nz : v' ≠ 0 := by
    by_cases v = 0
    · have pos : v' = (1, 0) := by
        apply if_pos
        exact h
      by_contra hv
      rw [pos] at hv
      simp only [Prod.mk_eq_zero, one_ne_zero, and_true] at hv 
    · have neg : v' = v := by
        apply if_neg
        exact h
      rw [neg]
      exact h
  exact Vec.normalize v' nz

theorem normalize'_eq_normalize_of_ne_zero {v : Vec} (nz : v ≠ 0) : (Vec.normalize v nz = normalize' v) := by
  unfold normalize'
  simp only [nz, ite_false]

def colinear (A B C : P) : Prop := by
  exact (B = A) ∨ (C = A) ∨ (B = C) ∨ (normalize' (VEC A B)).toProj = (normalize' (VEC A C)).toProj

-- The definition of colinear now includes two cases: the degenerate case and the nondegenerate case. We use normalize' to avoid problems involving using conditions of an "if" in its "then" and "else". And we only use VEC to define colinear. 

theorem colinear_of_vec_eq_smul_vec {A B C : P} {t : ℝ} (e : VEC A C = t • VEC A B) : colinear A B C := by
  unfold colinear
  by_cases (B ≠ A) ∧ (C ≠ A) ∧ (B ≠ C)
  · have hBA : B ≠ A := by tauto
    have hCA : C ≠ A := by tauto
    have hVEC : (Vec.normalize (VEC A B) ((ne_iff_vec_ne_zero A B).1 hBA)).toProj = (Vec.normalize (VEC A C) ((ne_iff_vec_ne_zero A C).1 hCA)).toProj := (eq_toProj_of_smul ((ne_iff_vec_ne_zero A B).1 hBA) ((ne_iff_vec_ne_zero A C).1 hCA) e)
    rw [normalize'_eq_normalize_of_ne_zero, normalize'_eq_normalize_of_ne_zero] at hVEC
    simp only [h, false_or]
    exact hVEC
  · have h' : (B = A) ∨ (C = A) ∨ (B = C) := by tauto
    tauto

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

-- Please rewrite this part, use minimal theorems, but create a tactic called `colinarity`
theorem perm_colinear {A B C : P} (h : colinear A B C) : (colinear B C A) := by sorry

theorem flip_colinear {A B C : P} (h : colinear A B C) : (colinear A C B) := sorry

theorem colinear_of_colinear_colinear_ne {A B C D: P} (h₁ : colinear A B C) (h₂ : colinear A B D) (h : A ≠ B) : (colinear A C D) := sorry

theorem ne_of_not_colinear {A B C : P} (h : ¬ colinear A B C) : (C ≠ B) ∧ (A ≠ C) ∧ (B ≠ A) := by
  sorry

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
