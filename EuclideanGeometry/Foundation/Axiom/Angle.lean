import EuclideanGeometry.Foundation.Axiom.Ray

noncomputable section
namespace EuclidGeom
/- Define values of oriented angles, in (-π, π], modulo 2 π. -/
/- Define oriented angles, ONLY taking in two rays starting at one point!  And define ways to construct oriented angles, by given three points on the plane, and etc.  -/
class OAngle (P : Type _) [h : EuclideanPlane P] where 
  start_ray : Ray P
  end_ray : Ray P
  source_eq_source : start_ray.source = end_ray.source

namespace OAngle

def mk_pt_pt_pt {P : Type _} [h : EuclideanPlane P] (A O B : P) (h₁ : A ≠ O) (h₂ : O ≠ B): OAngle P where
  start_ray := Ray.mk_pt_pt O A (Ne.symm h₁)
  end_ray := Ray.mk_pt_pt O B h₂
  source_eq_source := rfl

def value {P : Type _} [h : EuclideanPlane P] (A : OAngle P): ℝ := StdR2.angle (A.start_ray.direction.vec) (A.end_ray.direction.vec)

/- If `A = O ∨ O = B`, then the angle is defined to be zero-/
def angle_of_three_points {P : Type _} [h : EuclideanPlane P] (A O B : P) : ℝ := StdR2.angle (A -ᵥ O) (B -ᵥ O)
-- still logic problem, do i really need the def of an angle? and show angle of 3 pts = value of OAngle they form?

end OAngle

scoped notation "∠" => OAngle.angle_of_three_points

/- Operations on oriented angles, such a additivity of the evaluation of oriented angles.  -/
/- theorem l1 l2 l3 add angle; sub angle -/
/- theorem O A B C add angle; sub angle-/


/- 90 degree -/

end EuclidGeom