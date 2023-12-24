import EuclideanGeometry.Foundation.Construction.Polygon.Parallelogram

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem vec_eq_of_eq_dir_and_eq_length {A B C D : P} (h1 : B ≠ A) (h2 : D ≠ C) (h3 : (SEG_nd A B h1).toDir = (SEG_nd C D h2).toDir) (h4 : (SEG A B).length = (SEG C D).length) : VEC A B = VEC C D := by sorry

theorem is_prg_nd_of_diag_inx_eq_mid_eq_mid_variant_1 {A B C D : P} (h : (QDR A B C D).IsConvex) (h' : (SEG A C).midpoint = (SEG B D).midpoint) : ((QDR_cvx A B C D sorry sorry).toQuadrilateral).IsParallelogram_nd := by sorry

theorem is_prg_of_is_prg_nd (A B C D : P) (h : (QDR A B C D).IsParallelogram_nd) : (QDR A B C D).IsParallelogram := by sorry

theorem todir_eq_of_is_prg_nd (A B C D : P) (h : (QDR A B C D).IsParallelogram_nd) (h1 : B ≠ A) (h2 : C ≠ D): (SEG_nd A B h1).toDir = (SEG_nd D C h2).toDir := by sorry

theorem todir_eq_of_is_prg_nd_variant (A B C D : P) (h : (QDR A B C D).IsParallelogram_nd) (h1 : D ≠ A) (h2 : C ≠ B): (SEG_nd A D h1).toDir = (SEG_nd B C h2).toDir := by sorry
