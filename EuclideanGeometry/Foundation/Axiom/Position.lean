import EuclideanGeometry.Foundation.Axiom.Angle

/- This file discuss the relative positions of points and rays on a plane. -/
noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P] 

section colinear
def colinear (A B C : P) : Prop := ∠ A B C = 0 ∨ ∠ A B C = π  

-- rerwrite this part, use minimal theroems, but create a tactic called `colinarity`   
theorem perm_colinear {A B C : P} (h : colinear A B C) : (colinear B C A) := by sorry

theorem flip_colinear {A B C : P} (h : colinear A B C): (colinear A C B) := sorry

/- 
theorem colinear_ACB_of_colinear_ABC {A B C : P} (h : colinear A B C): colinear A C B := sorry

theorem colinear_BAC_of_colinear_ABC {A B C : P} (h : colinear A B C): colinear B A C := sorry

theorem colinear_BCA_of_colinear_ABC {A B C : P} (h : colinear A B C): colinear B C A := sorry

theorem colinear_CAB_of_colinear_ABC {A B C : P} (h : colinear A B C): colinear C A B := sorry
-/

theorem colinear_CBA_of_colinear_ABC {A B C : P} (h : colinear A B C): colinear C B A := sorry

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

theorem left_or_right_or_lies_on : sorry := sorry

theorem left_iff_not_right_of_not_lies_on : sorry := sorry

theorem not_lies_on_left_or_right : sorry := sorry

-- theroems stating colinear iff (Pos ∨ Neg ∨ Source) and alternativity of 3 conditions

end point_to_ray

scoped infix : 50 "LiesOnLeft" => IsOnLeftSide 
scoped infix : 50 "LiesOnRight" => IsOnRightSide 

/- Positions of a point relative to a ray/line/segment: 1. at the end point, 2. on the ray (not including the end point) 3. on the opposite direction of the ray.  4. on the "left" of the ray. 5. on the "right" of the ray. -/

/- Position of three (distinct) points.  Giving to colinear (futher classification) -/


/- Position of two rays -/
section ray_to_ray

/- -/
theorem intersect_of_ray_on_left_iff (ray₁ ray₂ : Ray P) (h : ray₂.source ≠ ray₁.source) : let ray₀ := Ray.mk_pt_pt ray₁.source ray₂.source h; (0 < OAngle.angle_of_two_ray ray₀ ray₁) ∧ (OAngle.angle_of_two_ray ray₀ ray₁ < OAngle.angle_of_two_ray ray₀ ray₂) ∧ (OAngle.angle_of_two_ray ray₀ ray₂ < π) ↔ (∃ A : P, (A LiesOnRay ray₁) ∧ (A LiesOnRay ray₂) ∧ (A LiesOnLeft ray₀))  := sorry

end ray_to_ray



/- Position of two lines; need a function to take the intersection of two lines (when they intersect). -/


/- A lot more theorems regarding positions -/
/- e.g. 180 degree implies colinear -/

end EuclidGeom
