import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

#check SegND.toDirLine_eq_toRay_toDirLine
#check eq_toDir_of_source_to_pt_lies_int
#check eq_toDirLine_of_source_to_pt_lies_int
#check eq_toDir_of_pt_lies_int_to_target
#check eq_toDirLine_of_pt_lies_int_to_target
#check eq_toDir_of_parallel_and_same_side
#check neg_toDir_of_parallel_and_opposite_side
#check TriangleND.same_orient_of_perm_vertices
#check TriangleND.iscclock_iff_liesonleft₁


/-
some tips of iff
h : a ↔ b
h.not : ¬ a ↔ ¬ b
h.symm : b ↔ a
h.mp : a → b
h.mpr : b → a
h' : a → b
h'.mt : ¬ b → ¬ a
-/

end EuclidGeom
