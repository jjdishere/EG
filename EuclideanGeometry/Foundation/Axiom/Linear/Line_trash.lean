import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem pt_flip_colinear {A B O : P} (h : B = pt_flip A O) : colinear A O B := by
  apply flip_colinear_snd_trd
  by_cases hne : A = B
  · rw [hne]
    unfold colinear
    simp
  haveI : PtNe A B := ⟨hne⟩
  apply Line.pt_pt_linear
  sorry

end EuclidGeom
