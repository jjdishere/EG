import EuclideanGeometry.Foundation.Axiom.Ray
import EuclideanGeometry.Foundation.Axiom.Ray_ex1

/- The purpose of of this file is to establish results about parallel transport along a vector. Presumably, all results are "invariant" under parallel transport. -/

namespace EuclidGeom

variable {P: Type _} [EuclideanPlane P] (v : ℝ × ℝ) (gseg : GDirSeg P) (seg : DirSeg P) (ray : Ray P)
