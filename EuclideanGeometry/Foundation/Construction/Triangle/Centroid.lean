import EuclideanGeometry.Foundation.Axiom.Triangle.Basic

/-!

-/
noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

def TriangleND.Median1 (tr_nd : TriangleND P) : SegND P := sorry

structure IsCentroid (tr_nd : TriangleND P) (G : P) : Prop where

def TriangleND.Centroid (tr_nd : TriangleND P) : P := sorry

theorem TriangleND.centroid_is_centroid (tr_nd : TriangleND P) : IsCentroid tr_nd tr_nd.Centroid := sorry

end EuclidGeom
