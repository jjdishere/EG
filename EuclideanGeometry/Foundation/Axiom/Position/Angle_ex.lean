import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex
import EuclideanGeometry.Foundation.Axiom.Position.Angle


noncomputable section

namespace EuclidGeom

namespace Angle

variable {P : Type _} [EuclideanPlane P] (ang : Angle P)

/- whether an angle is acute/right/obtuse. -/

def IsRightAngle {P : Type _} [EuclideanPlane P] (ang : Angle P) : Prop := sorry


def IsAcuteAngle {P : Type _} [EuclideanPlane P] (ang : Angle P) : Prop := sorry


def IsObtuseAngle {P : Type _} [EuclideanPlane P] (ang : Angle P) : Prop := sorry



/- Supplementary angles -/

-- Define the supplementary angle to be the angle 

def supplementary : (Angle P) where
  start_ray := ang.end_ray
  end_ray := ang.start_ray.reverse
  source_eq_source := sorry

-- If two oriented angles share a same side, then they are supplementary oriented angles if and only if the sum of two angles is π or -π   `Do I use {ang1} or (ang1)?

theorem reverse_ray_iff_sum_of_angle_eq_pi {ang1 : Angle P} {ang2 : Angle P} (h: ang1.end_ray = ang2.start_ray) : ang1.end_ray = ang2.start_ray.reverse ↔ ang1.value + ang2.value = π ∨ ang1.value + ang2.value = -π := by sorry

theorem right_of_supp_of_right (rt : IsRightAngle ang) :  IsRightAngle ang.supplementary := by sorry

theorem acute_of_supp_of_obtuse (rt : IsObtuseAngle ang) :  IsRightAngle ang.supplementary := by sorry

theorem obtuse_of_supp_of_acute (rt : IsAcuteAngle ang) :  IsRightAngle ang.supplementary := by sorry

theorem is_nd_of_supp_of_is_nd (nontriv : ang.is_nd) : ang.supplementary.is_nd := by sorry

def opposite :(Angle P) where
  start_ray := ang.start_ray.reverse
  end_ray := ang.end_ray.reverse
  source_eq_source := sorry

theorem opposite_eq_supp_of_supp : ang.supplementary.supplementary = ang := by sorry

theorem  is_nd_of_oppo_of_is_nd (nontriv : ang.is_nd) : ang.opposite.is_nd := by sorry




end Angle

namespace Angle

variable {P : Type _} [EuclideanPlane P] (ang : Angle P)


end Angle


end EuclidGeom
