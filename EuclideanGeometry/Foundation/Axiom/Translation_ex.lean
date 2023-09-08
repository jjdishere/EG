import EuclideanGeometry.Foundation.Axiom.Ray
import EuclideanGeometry.Foundation.Axiom.Ray_ex

/- The purpose of of this file is to establish results about parallel translate along a vector. Presumably, all results are "invariant" under parallel translation. -/

noncomputable section


namespace EuclidGeom

namespace DSeg

variable {P: Type _} [EuclideanPlane P] (v : Vec) (l : DSeg P)

-- parallel translate a generalized directed segments

def translate (l : DSeg P) (v : Vec)  : DSeg P where
  source := v +ᵥ l.source
  target := v +ᵥ l.target

-- parallel translate a nontrivial generalized directed segment is nontrivial

theorem non_triv_of_trans_non_triv (v : Vec) (l : DSeg P) (nontriv : l.is_nontriv) : (l.translate v).is_nontriv := by sorry

theorem reverse_of_trans_eq_trans_of_reverse (v : Vec) (l : DSeg P) : (l.translate v).reverse = l.reverse.translate v := by sorry

-- parallel translation does not change the length of a generalized directed dsegement.

theorem length_eq_length_of_translate (v: Vec) (l : DSeg P) : l.length = (l.translate v).length := by sorry

end DSeg

namespace Ray

variable {P: Type _} [EuclideanPlane P] (v : Vec) (l : Ray P)

-- parallel translate a ray

def translate (l : Ray P) (v : Vec) : Ray P where
  source := sorry
  toDir := sorry

end Ray

end EuclidGeom