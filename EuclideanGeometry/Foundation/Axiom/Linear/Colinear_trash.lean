import EuclideanGeometry.Foundation.Axiom.Linear.Ray
import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem not_colinear_of_colinear_not_colinear {A B C D : P} : (h₁ : colinear A B C) →  (h₂ : ¬ colinear D A B) → ¬ colinear D B C := sorry

end EuclidGeom
