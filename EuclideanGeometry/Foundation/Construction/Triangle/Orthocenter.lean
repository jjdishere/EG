import EuclideanGeometry.Foundation.Axiom.Triangle.Basic

/-!

-/
noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

def TriangleND.Height1 (tr_nd : TriangleND P) : SegND P := sorry

structure IsOrthocenter (tr_nd : TriangleND P) (H : P) : Prop where

def TriangleND.Orthocenter (tr_nd : TriangleND P) : P := sorry

theorem TriangleND.orthocenter_is_orthocenter (tr_nd : TriangleND P) : IsOrthocenter tr_nd tr_nd.Orthocenter := sorry

end EuclidGeom
