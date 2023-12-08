import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem perp_foot_lies_int_ray_of_acute_ang {A B C : P} (b_ne_a : B ≠ A) (c_ne_a : C ≠ A) (acu : Angle.IsAcuteAngle (ANG B A C b_ne_a c_ne_a)) : (perp_foot C (LIN A B b_ne_a)) LiesInt (RAY A B b_ne_a) := by sorry

theorem ang_acute_of_is_isoceles {A B C : P} (hnd : ¬ colinear A B C) (hisoc : (▵ A B C).IsIsoceles) : Angle.IsAcuteAngle (ANG C B A (ne_of_not_colinear hnd).1 (ne_of_not_colinear hnd).2.2.symm) := by sorry

end EuclidGeom
