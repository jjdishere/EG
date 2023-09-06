import EuclideanGeometry.Foundation.Axiom.Ray
import EuclideanGeometry.Foundation.Axiom.Ray_ex1

/- The purpose of of this file is to establish results about parallel translate along a vector. Presumably, all results are "invariant" under parallel translation. -/

namespace EuclidGeom

namespace Seg

variable {P: Type _} [EuclideanPlane P] (v : ℝ × ℝ) (l : Seg P)

-- parallel translate a generalized directed segments

def translate (v : ℝ × ℝ) (l : Seg P) : Seg P where
  source := v +ᵥ l.source
  target := v +ᵥ l.target

-- parallel translate a nontrivial generalized directed segment is nontrivial

theorem non_triv_of_trans_non_triv (v : ℝ × ℝ) (l : Seg P) (nontriv : l.source ≠ l.target) : (l.translate v).source ≠ (l.translate v).target := by sorry

theorem reverse_of_trans_eq_trans_of_reverse (v : ℝ × ℝ) (l : Seg P) : (l.translate v).reverse = l.reverse.translate v := by sorry

-- parallel translation does not change the length of a generalized directed segement.

theorem length_eq_length_of_translate (v: ℝ × ℝ) (l : Seg P) : l.length = (l.translate v).length := by sorry

end Seg

namespace Ray

variable {P: Type _} [EuclideanPlane P] (v : ℝ × ℝ) (l : Ray P)

-- parallel translate a ray

def translate (l : Ray P) (v : ℝ × ℝ) : Ray P where
  source := sorry
  direction := sorry

end Ray

end EuclidGeom