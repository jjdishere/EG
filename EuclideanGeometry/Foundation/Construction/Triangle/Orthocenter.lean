import EuclideanGeometry.Foundation.Axiom.Triangle.Basic

/-!

-/
noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

def Triangle_nd.Height1 (tr_nd : Triangle_nd P) : SegND P := sorry

structure IsOrthocenter (tr_nd : Triangle_nd P) (H : P) : Prop where

def Triangle_nd.Orthocenter (tr_nd : Triangle_nd P) : P := sorry

theorem Triangle_nd.orthocenter_is_orthocenter (tr_nd : Triangle_nd P) : IsOrthocenter tr_nd tr_nd.Orthocenter := sorry

end EuclidGeom
