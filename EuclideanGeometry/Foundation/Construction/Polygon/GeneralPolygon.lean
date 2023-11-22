import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral

/-!

-/
noncomputable section
namespace EuclidGeom

structure Polygon (P : Type _) [EuclideanPlane P] where

structure ConvexPolygon (P : Type _) [EuclideanPlane P] extends Polygon P where

structure RegularPolygon (P : Type _) [EuclideanPlane P] extends ConvexPolygon P where

end EuclidGeom
