import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem perp_foot_lies_int_ray_of_acute_ang {A B C : P} (b_ne_a : B ≠ A) (c_ne_a : C ≠ A) (acu : Angle.IsAcuteAngle (ANG B A C b_ne_a c_ne_a)) : (perp_foot C (LIN A B b_ne_a)) LiesInt (RAY A B b_ne_a) := by sorry

theorem ang_acute_of_is_isoceles {A B C : P} (not_colinear_ABC : ¬ colinear A B C) (isoceles_ABC : (▵ A B C).IsIsoceles) : Angle.IsAcuteAngle (ANG C B A (ne_of_not_colinear not_colinear_ABC).1 (ne_of_not_colinear not_colinear_ABC).2.2.symm) := by sorry

theorem ang_acute_of_is_isoceles' {A B C : P} (not_colinear_ABC : ¬ colinear A B C) (isoceles_ABC : (▵ A B C).IsIsoceles) : Angle.IsAcuteAngle (ANG A B C (ne_of_not_colinear not_colinear_ABC).2.2.symm (ne_of_not_colinear not_colinear_ABC).1) := by sorry

theorem ang_acute_of_is_isoceles_variant {A B C : P} (not_colinear_ABC : ¬ colinear A B C) (isoceles_ABC : (▵ A B C).IsIsoceles) : Angle.IsAcuteAngle (ANG A C B (ne_of_not_colinear not_colinear_ABC).2.1 (ne_of_not_colinear not_colinear_ABC).1.symm) := by sorry

theorem ang_acute_of_is_isoceles_variant' {A B C : P} (not_colinear_ABC : ¬ colinear A B C) (isoceles_ABC : (▵ A B C).IsIsoceles) : Angle.IsAcuteAngle (ANG B C A (ne_of_not_colinear not_colinear_ABC).1.symm (ne_of_not_colinear not_colinear_ABC).2.1 ) := by sorry

end EuclidGeom
