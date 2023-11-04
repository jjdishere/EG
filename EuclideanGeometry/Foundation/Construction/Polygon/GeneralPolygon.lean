import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral

/-!

-/
noncomputable section
namespace EuclidGeom

class Polygon (P : Type _) [EuclideanPlane P] where

class ConvexPolygon (P : Type _) [EuclideanPlane P] extends Polygon P where

class RegularPolygon (P : Type _) [EuclideanPlane P] extends ConvexPolygon P where

end EuclidGeom
