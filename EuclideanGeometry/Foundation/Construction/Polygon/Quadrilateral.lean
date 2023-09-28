import EuclideanGeometry.Foundation.Axiom.Position.Convex
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic

/-!
# Quadrilateral

In this file we define general quadrilaterals as four points on the plane and convex quadrilaterals.

## Important Definitions
*
*

## Notation

## Implementation Notes

Currently, we just defines general quadrilaterals and convex quadrilaterals. There are more classes in between. For example, quadrilateral without self-intersection, quadrilateral of non-degenerate (which means it does not self-intersect and not degenerate to a triangle). 
Of course many definitions work on these classes already, but without necessarity in application, we will not formalize these class for present.
-/

noncomputable section
namespace EuclidGeom

/-- Class of Quadrilateral: A quadrilateral consists of four points; it is the generalized quadrilateral formed by these four points -/
class Quadrilateral (P : Type _) [EuclideanPlane P] where
  point₁ : P
  point₂ : P
  point₃ : P
  point₄ : P

/-- For four points $A$ $B$ $C$ $D$ on a plane, instead of writing Quadrilateral.mk $A$ $B$ $C$ $D$ for the quadrilateral formed by $A$ $B$ $C$ $D$, we use QDR $A$ $B$ $C$ $D$ to denote such a quadrilateral. -/
scoped notation "QDR" => Quadrilateral.mk

namespace Quadrilateral
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)

/-- The edge of first point and second point of a quadrilateral -/
def edge₁₂ : Seg P := SEG qdr.1 qdr.2

/-- The edge of second point and third point of a quadrilateral -/
def edge₂₃ : Seg P := SEG qdr.2 qdr.3

/-- The edge of third point and fourth point of a quadrilateral -/
def edge₃₄ : Seg P := SEG qdr.3 qdr.4

/-- The edge of fourth point and first point of a quadrilateral -/
def edge₄₁ : Seg P := SEG qdr.4 qdr.1

/-- The diagonal of first point and third point of a quadrilateral --/
def diagonal₁₃ : Seg P := SEG qdr.1 qdr.3

/-- The diagonal of second point and fourth point of a quadrilateral --/
def diagonal₂₄ : Seg P := SEG qdr.2 qdr.4

end Quadrilateral



end EuclidGeom