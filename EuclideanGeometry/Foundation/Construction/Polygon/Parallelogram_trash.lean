import EuclideanGeometry.Foundation.Construction.Polygon.Parallelogram

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace prg_trash

theorem vec_eq_of_eq_dir_and_eq_length {A B C D : P} (h1 : B ≠ A) (h2 : D ≠ C) (h3 : (SEG_nd A B h1).toDir = (SEG_nd C D h2).toDir) (h4 : (SEG A B).length = (SEG C D).length) : VEC A B = VEC C D := by sorry

theorem is_prg_of_diag_inx_eq_mid_eq_mid_variant_1 (A B C D : P) (h' : (SEG A C).midpoint = (SEG B D).midpoint) : QDR A B C D IsPRG := by sorry

end prg_trash
