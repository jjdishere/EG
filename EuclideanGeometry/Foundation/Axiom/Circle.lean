import EuclideanGeometry.Foundation.Axiom.Position

noncomputable section
namespace EuclidGeom

/- Class of Circles-/
class Circle (P : Type _) [EuclideanPlane P] where 
  center : P
  radius : ℝ
  rad_pos : 0 < radius

namespace Circle
variable {P : Type _} [EuclideanPlane P]

def mk_pt_pt (O A : P) (h : A ≠ O) : Circle P where
  center := O
  radius := (SEG O A).length
  rad_pos := (Seg.nontriv_iff_length_pos _).mp h

def mk_pt_pt_pt (A B C: P) (h : ¬ colinear A B C) : Circle P := sorry

end Circle

scoped notation "CIR" => Circle.mk_pt_pt

scoped notation "⨀" => Circle.mk_pt_pt
-- power of a point
-- point lieson, inside, outside a circle by power
-- ray with circle
-- line with circle
end EuclidGeom
