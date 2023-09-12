import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex
import EuclideanGeometry.Foundation.Axiom.Position.Angle


noncomputable section

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

-- If two oriented angles share a same side, then they are supplementary oriented angles if and only if the sum of two angles is π or -π   `Do I use {oang1} or (oang1)?

theorem reverse_ray_iff_sum_of_oangle_eq_pi {oang1 : OAngle P} {oang2 : OAngle P} (h: oang1.end_ray = oang2.start_ray) : oang1.end_ray = oang2.start_ray.reverse ↔ oang1.value + oang2.value = π ∨ oang1.value + oang2.value = -π := by sorry

theorem right_of_supp_of_right (rt : IsRightAngle oang) :  IsRightAngle oang.supplementary := by sorry

theorem acute_of_supp_of_obtuse (rt : IsObtuseAngle oang) :  IsRightAngle oang.supplementary := by sorry

theorem obtuse_of_supp_of_acute (rt : IsAcuteAngle oang) :  IsRightAngle oang.supplementary := by sorry

theorem is_nd_of_supp_of_is_nd (nontriv : oang.is_nd) : oang.supplementary.is_nd := by sorry

def opposite :(OAngle P) where
  start_ray := oang.start_ray.reverse
  end_ray := oang.end_ray.reverse
  source_eq_source := sorry

theorem opposite_eq_supp_of_supp : oang.supplementary.supplementary = oang := by sorry

theorem  is_nd_of_oppo_of_is_nd (nontriv : oang.is_nd) : oang.opposite.is_nd := by sorry




end OAngle

namespace OAngle

variable {P : Type _} [EuclideanPlane P] (oang : OAngle P)


end OAngle


end EuclidGeom
