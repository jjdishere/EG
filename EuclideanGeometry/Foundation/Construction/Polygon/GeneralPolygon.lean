import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral

/-!

-/
noncomputable section
namespace EuclidGeom

structure Polygon (P : Type*) [EuclideanPlane P] where

structure ConvexPolygon (P : Type*) [EuclideanPlane P] extends Polygon P where

structure RegularPolygon (P : Type*) [EuclideanPlane P] extends ConvexPolygon P where

end EuclidGeom
