import EuclideanGeometry.Foundation.Axiom.Angle

/- This file discuss the relative positions of points and rays on a plane. -/
noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P] 

section colinear
def colinear (A B C : P) : Prop := by
  by_cases B ≠ A ∧ C ≠ A   
  · exact ANG B A C h.1 h.2 = 0 ∨ ANG B A C h.1 h.2 = π  
  · exact True  

-- rerwrite this part, use minimal theorems, but create a tactic called `colinarity`
theorem perm_colinear {A B C : P} (h : colinear A B C) : (colinear B C A) := by sorry

theorem flip_colinear {A B C : P} (h : colinear A B C) : (colinear A C B) := sorry

theorem colinear_of_colinear_colinear {A B C D: P} (h₁ : colinear A B C) (h₂ : colinear A B D) : (colinear A C D) := sorry

theorem eq_mul_vec_iff_colinear_of_ne (A B C : P) (g : A ≠ B) : colinear A B C ↔ ∃ r : ℝ , Vec A C = r • Vec A B:= sorry

theorem ne_of_not_colinear {A B C : P} (h : ¬ colinear A B C) : (C ≠ B) ∧ (A ≠ C) ∧ (B ≠ A) := sorry   

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

/- Positions of a point relative to a ray/line/segment: 1. at the end point, 2. on the ray (not including the end point) 3. on the opposite direction of the ray.  4. on the "left" of the ray. 5. on the "right" of the ray. -/
-- `all these are better stated with the notaiton of line, so I moved them to line_ex.lean`



/- Position of two rays -/
section ray_to_ray

/- Statement of his theorem should change, since ray₀.source ≠ ray₂.source. -/
theorem intersect_of_ray_on_left_iff (ray₁ ray₂ : Ray P) (h : ray₂.source ≠ ray₁.source) : let ray₀ := Ray.mk_pt_pt ray₁.source ray₂.source h; (0 < OAngle.angle_of_two_ray_of_eq_source ray₀ ray₁ rfl) ∧ (OAngle.angle_of_two_ray_of_eq_source ray₀ ray₁ rfl < OAngle.angle_of_two_ray_of_eq_source ray₀ ray₂ sorry) ∧ (OAngle.angle_of_two_ray_of_eq_source ray₀ ray₂ sorry < π) ↔ (∃ A : P, (A LiesOnRay ray₁) ∧ (A LiesOnRay ray₂) ∧ (A LiesOnLeft ray₀))  := sorry

end ray_to_ray



/- Position of two lines; need a function to take the intersection of two lines (when they intersect). -/


/- A lot more theorems regarding positions -/
/- e.g. 180 degree implies colinear -/

end EuclidGeom