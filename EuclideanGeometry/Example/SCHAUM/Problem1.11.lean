import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type*} [EuclideanPlane Plane]

namespace SCHAUM_Problem_1_11
/-
If $ABCD$ is a parallelogram and $EFCD$ is a parallelogram, then $ABFE$ is a parallelogram.
-/

structure Setting (Plane : Type*) [EuclideanPlane Plane] where
  -- $ABCD$ is a parallelogram.
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  ABCD_IsPRG : (QDR A B C D) IsPRG
  -- $CDEF$ is a parallelogram.
  E : Plane
  F : Plane
  EFCD_IsPRG : (QDR E F C D) IsPRG
-- Prove that $ABFE$ is a parallelogram.
theorem result (Plane : Type*) [EuclideanPlane Plane] (e : Setting Plane) : (QDR e.A e.B e.F e.E) IsPRG := by
  /-
  Because $ABCD$ is a parallelogram, $\overarrow{AB} = \overarrow{DC}$.
  Because $EFCD$ is a parallelogram, $\overarrow{EF} = \overarrow{DC}$.
  Therefore, $\overarrow{AB} = \overarrow{DC} = \overarrow{EF}$, so $ABFE$ is a parallelogram.
  -/
  -- $\overarrow{AB} = \overarrow{DC} = \overarrow{EF}$, so $ABFE$ is a parallelogram.
  calc
    -- Because $ABCD$ is a parallelogram, $\overarrow{AB} = \overarrow{DC}$.
    _ = VEC e.D e.C := e.ABCD_IsPRG
    -- Because $EFCD$ is a parallelogram, $\overarrow{EF} = \overarrow{DC}$.
    _ = _ := e.EFCD_IsPRG.symm

end SCHAUM_Problem_1_11
end EuclidGeom
