import EuclideanGeometry.Foundation.Axiom.Position

noncomputable section
namespace EuclidGeom

class Circle {P : Type _} [EuclideanPlane P] where 
  center : P
  radius : ℝ
  rad_pos : 0 < radius

-- point lieson, inside, outside a circle
-- ray with circle
-- line with circle
end EuclidGeom
