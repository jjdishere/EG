import EuclideanGeometry.Foundation.Axiom.Triangle

namespace EuclidGeom

/- definition of congruence of triangles-/

/- should use translation and rotation as definition, eq of length and angle as result? -/
variable {P : Type _} [EuclideanPlane P]

/- def IsCongTo (tr₁ : Triangle P) (tr₂ : Triangle P) := by 
  by_cases colinear tr₁.1 tr₁.2 tr₁.3
  · exact colinear tr₂.1 tr₂.2 tr₂.3 ∧ tr₁.edge₁.length = tr₂.edge₁.length ∧  tr₁.edge₂.length = tr₂.edge₂.length ∧  tr₁.edge₃.length = tr₂.edge₃.length
  · exact
-/
 

/- SAS -/

end EuclidGeom