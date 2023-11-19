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
  apply is_prg_of_para_eq_length
  · sorry
  · calc
      _ = (SEG C D).length := by sorry
      _ = (SEG E F).length := by sorry
      _ = (SEG F E).length := by sorry
  · sorry

end SCHAUM_Problem_1_11
