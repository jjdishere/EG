import EuclideanGeometry.Foundation.Construction.Polygon.Parallelogram

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem vec_eq_of_eq_dir_and_eq_length {A B C D : P} (h1 : B ≠ A) (h2 : D ≠ C) (h3 : (SEG_nd A B h1).toDir = (SEG_nd C D h2).toDir) (h4 : (SEG A B).length = (SEG C D).length) : VEC A B = VEC C D := by sorry

/-- In the main file already. -/
theorem is_prg_nd_of_diag_inx_eq_mid_eq_mid_variant_1 {A B C D : P} (h : (QDR A B C D).IsConvex) (h' : (SEG A C).midpoint = (SEG B D).midpoint) : ((QDR_cvx A B C D h).toQuadrilateral).IsParallelogramND := by sorry
