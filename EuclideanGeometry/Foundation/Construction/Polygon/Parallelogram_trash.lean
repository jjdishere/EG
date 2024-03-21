import EuclideanGeometry.Foundation.Construction.Polygon.Parallelogram

namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

theorem vec_eq_of_eq_dir_and_eq_length {A B C D : P} [h1 : PtNe B A] [h2 : PtNe D C] (h3 : (SEG_nd A B).toDir = (SEG_nd C D).toDir) (h4 : (SEG A B).length = (SEG C D).length) : VEC A B = VEC C D := by sorry

/-- In the main file already. -/
theorem is_prg_nd_of_diag_inx_eq_mid_eq_mid_variant_1 {A B C D : P} (h : (QDR A B C D).IsConvex) (h' : (SEG A C).midpoint = (SEG B D).midpoint) : ((QDR_cvx A B C D h).toQuadrilateral).IsPrgND := by sorry
