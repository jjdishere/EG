import EuclideanGeometry.Foundation.Axiom.Ray
import EuclideanGeometry.Foundation.Axiom.Ray_ex1

/- The purpose of of this file is to establish results about parallel translate along a vector. Presumably, all results are "invariant" under parallel translation. -/

namespace EuclidGeom

namespace Seg

variable {P: Type _} [EuclideanPlane P] (v : ℝ × ℝ) (seg : Seg P)

-- parallel translate a generalized directed segments

def translate (seg : Seg P) (v : ℝ × ℝ) : Seg P where
  source := v +ᵥ seg.source
  target := v +ᵥ seg.target

-- parallel translate a nontrivial generalized directed segment is nontrivial

theorem Seg.non_triv_of_trans_non_triv (seg : Seg P) (v : ℝ × ℝ) (nontriv : seg.source ≠ seg.target) : (Seg.translate seg v).source ≠ (Seg.translate seg v).target := by sorry

end Seg

namespace Ray

variable {P: Type _} [EuclideanPlane P] (v : ℝ × ℝ) (ray : Ray P)

-- parallel translate a ray

def translate (ray : Ray P) (v : ℝ × ℝ) : Ray P where
  source := sorry
  direction := sorry

end Ray

end EuclidGeom