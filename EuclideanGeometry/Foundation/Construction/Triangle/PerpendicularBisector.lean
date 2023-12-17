import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Circle.Basic

/-!

-/
noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

structure IsPerpBis (seg_nd : SegND P) (line : Line P) : Prop where

def SegND.PerpBis (seg_nd : SegND P) : Line P := sorry

theorem SegND.perp_bis_is_perp_bis (seg_nd : SegND P) : IsPerpBis seg_nd seg_nd.PerpBis := sorry

structure IsCircumcenter (tr_nd : TriangleND P) (O : P) : Prop where

def TriangleND.Circumcenter (tr_nd : TriangleND P) : P := sorry

theorem TriangleND.circumcenter_is_circumcenter (tr_nd : TriangleND P) : IsCircumcenter tr_nd tr_nd.Circumcenter := sorry

structure IsCircumcircle (tr_nd : TriangleND P) (cir : Circle P) : Prop where

def TriangleND.Circumcircle (tr_nd : TriangleND P) : Circle P := sorry

theorem TriangleND.circumcircle_is_circumcircle (tr_nd : TriangleND P) : IsCircumcircle tr_nd tr_nd.Circumcircle := sorry

end EuclidGeom
