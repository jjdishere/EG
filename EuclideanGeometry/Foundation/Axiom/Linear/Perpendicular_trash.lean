import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Position.Angle

noncomputable section
namespace EuclidGeom

open Line

variable {P : Type*} [EuclideanPlane P]

theorem perp_foot_unique' {A B : P} {l : Line P} (h : B LiesOn l) [_hne : PtNe A B] (hp : LIN A B ⟂ l) : perp_foot A l = B := sorry

end EuclidGeom
