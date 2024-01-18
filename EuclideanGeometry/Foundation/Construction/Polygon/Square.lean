import EuclideanGeometry.Foundation.Construction.Polygon.Rhombus
import EuclideanGeometry.Foundation.Construction.Polygon.Rectangle

/-!

-/
noncomputable section
namespace EuclidGeom

@[ext]
structure Square (P : Type*) [EuclideanPlane P] extends Rhombus P, Rectangle P

end EuclidGeom
