import EuclideanGeometry.Foundation.Axiom.Triangle.Basic

/-!

-/
noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

def Triangle_nd.Median1 (tr_nd : Triangle_nd P) : SegND P := sorry

structure IsCentroid (tr_nd : Triangle_nd P) (G : P) : Prop where

def Triangle_nd.Centroid (tr_nd : Triangle_nd P) : P := sorry

theorem Triangle_nd.centroid_is_centroid (tr_nd : Triangle_nd P) : IsCentroid tr_nd tr_nd.Centroid := sorry

end EuclidGeom
