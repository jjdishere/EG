import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem ne_source_of_lies_int_seg_nd (A B C : P) (h1 : B ≠ A) (h2 : C LiesInt (SEG_nd A B h1)) : C ≠ A := by sorry

theorem ne_source_of_lies_int_seg (A B C : P) (h2 : C LiesInt (SEG A B)) : C ≠ A := by sorry

theorem eq_todir_of_lies_int_seg_nd (A B C : P) (h1 : B ≠ A) (h2 : C LiesInt (SEG A B)) : (SEG_nd A B h1).toDir = (SEG_nd A C (ne_source_of_lies_int_seg_nd A B C h1 h2)).toDir := by sorry

end EuclidGeom
