import EuclideanGeometry.Foundation.Axiom.Angle
import EuclideanGeometry.Foundation.Axiom.Ray_ex

namespace EuclidGeom

namespace OAngle

variable {P : Type _} [EuclideanPlane P] (oang : OAngle P)

/- whether an angle is acute/right/obtuse. -/

def IsRightAngle {P : Type _} [EuclideanPlane P] (oang : OAngle P) : Prop := sorry


def IsAcuteAngle {P : Type _} [EuclideanPlane P] (oang : OAngle P) : Prop := sorry


def IsObtuseAngle {P : Type _} [EuclideanPlane P] (oang : OAngle P) : Prop := sorry



/- Supplementary angles -/

-- Define the supplementary angle to be the oangle 

def supplementary : (OAngle P) where
  start_ray := oang.end_ray
  end_ray := oang.start_ray.reverse
  source_eq_source := sorry

theorem right_of_supp_of_right (rt : IsRightAngle oang) :  IsRightAngle oang.supplementary := by sorry

theorem acute_of_supp_of_obtuse (rt : IsObtuseAngle oang) :  IsRightAngle oang.supplementary := by sorry

theorem obtuse_of_supp_of_acute (rt : IsAcuteAngle oang) :  IsRightAngle oang.supplementary := by sorry

theorem is_nontriv_of_supp_of_is_nontriv (nontriv : oang.is_nontriv) : oang.supp.is_nontriv := by sorry

def opposite :(OAngle P) where
  start_ray := oang.start_ray.reverse
  end_ray := oang.end_ray.reverse
  source_eq_source := sorry

theorem opposite_eq_supp_of_supp : oang.supplementary.supplementary = oang := by sorry

theorem  is_nontriv_of_oppo_of_is_nontriv (nontriv : oang.is_nontriv) : oang.opposite.is_nontriv := by sorry

/- complementary angles -/


end OAngle

namespace OAngle

variable {P : Type _} [EuclideanPlane P] (oang : OAngle P)


end OAngle


end EuclidGeom
