import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

#check SegND.toDirLine_eq_toRay_toDirLine
#check SegND.toDir_eq_of_lies_int
#check SegND.dirLine_source_pt_eq_toDirLine_of_lies_int
#check SegND.mk_pt_target_toDirLine_eq_of_lies_int
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
