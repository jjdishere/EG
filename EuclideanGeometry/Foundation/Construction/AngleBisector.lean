import EuclideanGeometry.Foundation.Axiom.Angle
import EuclideanGeometry.Foundation.Axiom.Rotation

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