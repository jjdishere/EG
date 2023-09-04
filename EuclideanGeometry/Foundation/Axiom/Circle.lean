import EuclideanGeometry.Foundation.Axiom.Position

noncomputable section
namespace EuclidGeom

class Circle (P : Type _) [EuclideanPlane P] where 
  center : P
  radius : ℝ
  rad_pos : 0 < radius

namespace Circle
variable {P : Type _} [EuclideanPlane P]

def mk_pt_pt (O A : P) (h : O ≠ A) : Circle P := sorry

def mk_pt_pt_pt (A B C: P) (h : ¬ colinear A B C) : Circle P := sorry

end Circle

scoped notation "CIR" => Circle.mk_pt_pt

scoped notation "⨀" => Circle.mk_pt_pt
-- point lieson, inside, outside a circle
-- ray with circle
-- line with circle
end EuclidGeom
