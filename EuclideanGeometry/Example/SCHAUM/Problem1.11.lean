import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace SCHAUM_Problem_1_11
/-
If $ABCD$ is a parallelogram and $CDEF$ is a parallelogram, then $ABFE$ is a parallelogram.
-/

-- $ABCD$ is a parallelogram.
variable {A B C D : Plane} {hprg1 : Quadrilateral.IsParallelogram (QDR A B C D)}
-- $CDEF$ is a parallelogram.
variable {E F : Plane} {hprg2 : Quadrilateral.IsParallelogram (QDR C D E F)}
-- State the main goal.
theorem SCHAUM_Problem_1_11 : Quadrilateral.IsParallelogram (QDR A B F E) := by
  sorry

end SCHAUM_Problem_1_11
