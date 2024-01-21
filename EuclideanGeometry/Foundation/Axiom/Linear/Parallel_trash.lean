import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

namespace Parallel

theorem segnd_para_line_of_line_para_line (A B : P) (B_ne_A : B ≠ A) (l : Line P) (h : (SEG_nd A B B_ne_A) ∥ l) : (LIN A B B_ne_A) ∥ l := by sorry

end Parallel

end EuclidGeom
