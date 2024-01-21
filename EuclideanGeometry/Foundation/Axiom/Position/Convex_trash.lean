import EuclideanGeometry.Foundation.Axiom.Position.Orientation
import EuclideanGeometry.Foundation.Axiom.Position.Convex
import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral

noncomputable section
namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

theorem cvx_of_inscribed_to_cvx {X Y Z W A B C D : P} (h : (QDR A B C D).IsConvex) (h1 : X LiesInt (SEG A B)) (h2 : Y LiesInt (SEG B C)) (h3 : Z LiesInt (SEG C D)) (h4 : W LiesInt (SEG D A)) : (QDR X Y Z W).IsConvex := by sorry

end EuclidGeom
