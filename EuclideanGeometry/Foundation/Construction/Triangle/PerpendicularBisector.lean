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

structure IsCircumcenter (tr_nd : Triangle_nd P) (O : P) : Prop where

def Triangle_nd.Circumcenter (tr_nd : Triangle_nd P) : P := sorry

theorem Triangle_nd.circumcenter_is_circumcenter (tr_nd : Triangle_nd P) : IsCircumcenter tr_nd tr_nd.Circumcenter := sorry

structure IsCircumcircle (tr_nd : Triangle_nd P) (cir : Circle P) : Prop where

def Triangle_nd.Circumcircle (tr_nd : Triangle_nd P) : Circle P := sorry

theorem Triangle_nd.circumcircle_is_circumcircle (tr_nd : Triangle_nd P) : IsCircumcircle tr_nd tr_nd.Circumcircle := sorry

end EuclidGeom
