import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Isometry.Rotation

/-!

-/
noncomputable section
namespace EuclidGeom

namespace OAngle
variable {P : Type _} [EuclideanPlane P] 

/- when the OAngle is flat, bisector is on the left side-/
def bisector (ang : OAngle P) : Ray P := sorry

end OAngle

end EuclidGeom