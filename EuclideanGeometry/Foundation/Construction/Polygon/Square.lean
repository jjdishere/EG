import EuclideanGeometry.Foundation.Construction.Polygon.Rhombus
import EuclideanGeometry.Foundation.Construction.Polygon.Rectangle

/-!

-/
noncomputable section
namespace EuclidGeom

class Square (P : Type _) [EuclideanPlane P] extends Rhombus P, Rectangle P

end EuclidGeom
