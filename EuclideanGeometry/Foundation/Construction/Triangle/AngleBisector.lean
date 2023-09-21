import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Isometry.Rotation

/-!

-/
noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] 

namespace OAngle

/- when the OAngle is flat, bisector is on the left side-/
def bisector (oang : OAngle P) : Ray P := sorry


end OAngle

-- theorem bisect_perp_bisect_of_supp (oang : OAngle P) : oang.bisector ⟂ oang.supplementary.bisector := sorry

end EuclidGeom