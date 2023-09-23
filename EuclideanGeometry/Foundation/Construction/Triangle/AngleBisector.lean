import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Isometry.Rotation

/-!

-/
noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] 

namespace Angle

/- when the Angle is flat, bisector is on the left side-/
def bisector (ang : Angle P) : Ray P := sorry


end Angle

-- theorem bisect_perp_bisect_of_supp (ang : Angle P) : ang.bisector ⟂ ang.supplementary.bisector := sorry

end EuclidGeom