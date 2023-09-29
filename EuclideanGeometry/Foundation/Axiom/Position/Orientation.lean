import EuclideanGeometry.Foundation.Axiom.Position.Angle

/- This file discuss the relative positions of points and rays on a plane. -/
noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P] 

/- Positions of points on a line, ray, oriented segments. -/

section point_to_ray

def IsOnLeftSide (A : P) (ray : Ray P) : Prop := by
  by_cases A = ray.source
  · exact False
  · exact (0 < (Angle.mk ray (Ray.mk_pt_pt ray.source A h ) rfl).value) ∧ ((Angle.mk ray (Ray.mk_pt_pt ray.source A h ) rfl).value ≠ π) 

def IsOnRightSide (A : P) (ray : Ray P) : Prop := by
  by_cases A = ray.source
  · exact False
  · exact ((Angle.mk ray (Ray.mk_pt_pt ray.source A h ) rfl).value < 0)


end point_to_ray

scoped infix : 50 "LiesOnLeft" => IsOnLeftSide 
scoped infix : 50 "LiesOnRight" => IsOnRightSide 

/- Position of two rays -/
section ray_to_ray

/- Statement of his theorem should change, since ray₀.source ≠ ray₂.source. -/
theorem intersect_of_ray_on_left_iff (ray₁ ray₂ : Ray P) (h : ray₂.source ≠ ray₁.source) : let ray₀ := Ray.mk_pt_pt ray₁.source ray₂.source h; (0 < Angle.angle_of_two_ray_of_eq_source ray₀ ray₁ rfl) ∧ (Angle.angle_of_two_ray_of_eq_source ray₀ ray₁ rfl < Angle.angle_of_two_ray_of_eq_source ray₀ ray₂ sorry) ∧ (Angle.angle_of_two_ray_of_eq_source ray₀ ray₂ sorry < π) ↔ (∃ A : P, (A LiesOn ray₁) ∧ (A LiesOn ray₂) ∧ (A LiesOnLeft ray₀))  := sorry

end ray_to_ray



/- Position of two lines; need a function to take the intersection of two lines (when they intersect). -/


/- A lot more theorems regarding positions -/
/- e.g. 180 degree implies colinear -/

end EuclidGeom
