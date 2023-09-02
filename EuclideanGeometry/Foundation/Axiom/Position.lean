import EuclideanGeometry.Foundation.Axiom.Angle

/- This file discuss the relative positions of points and lines on a plane. -/
noncomputable section
namespace EuclidGeom

section colinear
def colinear {P : Type _} [EuclideanPlane P] (A B C : P) : Prop := ∠ A B C = 0 ∨ ∠ A B C = Real.pi  

theorem colinear_ACB_of_colinear_ABC {P : Type _} [EuclideanPlane P] (A B C : P) (h : colinear A B C): colinear A C B := sorry

theorem colinear_BAC_of_colinear_ABC {P : Type _} [EuclideanPlane P] (A B C : P) (h : colinear A B C): colinear B A C := sorry

theorem colinear_BCA_of_colinear_ABC {P : Type _} [EuclideanPlane P] (A B C : P) (h : colinear A B C): colinear B C A := sorry

theorem colinear_CAB_of_colinear_ABC {P : Type _} [EuclideanPlane P] (A B C : P) (h : colinear A B C): colinear C A B := sorry

theorem colinear_CBA_of_colinear_ABC {P : Type _} [EuclideanPlane P] (A B C : P) (h : colinear A B C): colinear C B A := sorry

theorem eq_mul_vec_iff_colinear {P : Type _} [EuclideanPlane P] (A B C : P) (g : A ≠ B) : colinear A B C ↔ ∃ r : ℝ , Vec A C = r • Vec A B:= sorry

end colinear
/- Positions of points on a line, ray, oriented segments. -/

section left

def IsOnLeftSide {P : Type _} [EuclideanPlane P] (A : P) (ray : Ray P) : Prop := sorry

end left

scoped infix : 50 "IsOnLeftOf" => IsOnLeftSide 

/- Positions of a point relative to a ray/line/segment: 1. at the end point, 2. on the ray (not including the end point) 3. on the opposite direction of the ray.  4. on the "left" of the ray. 5. on the "right" of the ray. -/

/- Also inlclude functions such as Is_on_the_ray, and a type Left_of_the_ray.   -/



/- Position of three (distinct) points.  Giving to colinear (futher classification) -/


/- Position of two rays -/




/- Position of two lines; need a function to take the intersection of two lines (when they intersect). -/


/- A lot more theorems regarding positions -/
/- e.g. 180 degree implies colinear -/

end EuclidGeom
