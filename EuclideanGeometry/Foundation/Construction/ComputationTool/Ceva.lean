import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Construction.ComputationTool.Oarea_method

/-!

-/
noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P]

section Ceva's_theorem

theorem ceva_theorem (A B C D : P) (nd1 : ¬ colinear A B C) (nd2 : ¬ colinear B C D) (nd3 : ¬ colinear C D A) (nd4 : ¬ colinear D A B) (nd5 : ¬ LIN A D (ne_of_not_colinear nd3).1.symm ∥ LIN B C (ne_of_not_colinear nd1).1) (nd6 : ¬ LIN B D (ne_of_not_colinear nd2).2.1.symm ∥ LIN B A (ne_of_not_colinear nd1).2.2.symm) (nd7 : ¬ LIN C D (ne_of_not_colinear nd2).1 ∥ LIN A B (ne_of_not_colinear nd1).2.2) : (divratio (Line.inx (LIN A D (ne_of_not_colinear nd3).1.symm) (LIN B C (ne_of_not_colinear nd1).1) nd5) B C) * (divratio (Line.inx (LIN B D (ne_of_not_colinear nd2).2.1.symm) (LIN B A (ne_of_not_colinear nd1).2.2.symm) nd6) C A) * (divratio (Line.inx (LIN C D (ne_of_not_colinear nd2).1) (LIN A B (ne_of_not_colinear nd1).2.2) nd7) A B) = -1 := by
  let E : P := (Line.inx (LIN A D (ne_of_not_colinear nd3).1.symm) (LIN B C (ne_of_not_colinear nd1).1) nd5)
  let F : P := (Line.inx (LIN B D (ne_of_not_colinear nd2).2.1.symm) (LIN B A (ne_of_not_colinear nd1).2.2.symm) nd6)
  let G : P := (Line.inx (LIN C D (ne_of_not_colinear nd2).1) (LIN A B (ne_of_not_colinear nd1).2.2) nd7)
  have colinbce : colinear B C E := (Line.lies_on_line_of_pt_pt_iff_colinear (ne_of_not_colinear nd1).1 E).mp (Line.inx_lies_on_snd nd5)
  sorry

end Ceva's_theorem

end EuclidGeom
