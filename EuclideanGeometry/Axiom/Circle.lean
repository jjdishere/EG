import EuclideanGeometry.Axiom.Position

noncomputable section
namespace EuclidGeom

class Circle {P : Type _} [EuclideanPlane P] where 
  center : P
  radius : ℝ
  rad_pos : 0 < radius

end EuclidGeom
