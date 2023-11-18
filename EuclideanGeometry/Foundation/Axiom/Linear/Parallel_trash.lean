import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem Seg_nd.not_para_rev_of_not_para (seg_nd seg_nd' : Seg_nd P) : (¬ seg_nd ∥ seg_nd') → (¬ seg_nd ∥ seg_nd'.reverse) := sorry

end EuclidGeom
