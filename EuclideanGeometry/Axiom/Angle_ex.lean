import EuclideanGeometry.Axiom.Angle
import EuclideanGeometry.Axiom.Ray_ex1

namespace EuclidGeom

namespace OAngle

variable {P : Type _} [EuclideanPlane P] (oang : OAngle P)

/- whether an angle is acute/right/obtuse. -/

def IsRightAngle {P : Type _} [EuclideanPlane P] (oang : OAngle P) : Prop := sorry


def IsAcuteAngle {P : Type _} [EuclideanPlane P] (oang : OAngle P) : Prop := sorry


def IsObtuseAngle {P : Type _} [EuclideanPlane P] (oang : OAngle P) : Prop := sorry

-- scoped infix : 50 "IsRightAngle" => is_right_angle
-- scoped infix : 50 "IsAcuteAngle" => is_acute_angle
-- scoped infix : 50 "IsObtuseAngle" => is_obtuse_angle


/- Supplementary angles -/

def supplementary : (OAngle P) where
  start_ray := oang.end_ray
  end_ray := oang.start_ray.reverse
  source_eq_source := sorry

theorem right_of_supp_of_right (rt : IsRightAngle oang) :  IsRightAngle oang.supplementary := by sorry

theorem acute_of_supp_of_obtuse (rt : IsObtuseAngle oang) :  IsRightAngle oang.supplementary := by sorry

theorem obtuse_of_supp_of_acute (rt : IsAcuteAngle oang) :  IsRightAngle oang.supplementary := by sorry

def opposite :(OAngle P) where
  start_ray := oang.start_ray.reverse
  end_ray := oang.end_ray.reverse
  source_eq_source := sorry

theorem opposite_eq_supp_of_supp : oang.supplementary.supplementary = oang := by sorry




end OAngle

end EuclidGeom
