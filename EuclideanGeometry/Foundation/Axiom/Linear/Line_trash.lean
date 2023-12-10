import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem ne_source_of_lies_int_seg_nd (A B C : P) (h1 : B ≠ A) (h2 : C LiesInt (SEG_nd A B h1)) : C ≠ A := by sorry

theorem ne_source_of_lies_int_seg (A B C : P) (h2 : C LiesInt (SEG A B)) : C ≠ A := by sorry

theorem eq_todir_of_lies_int_seg_nd (A B C : P) (h1 : B ≠ A) (h2 : C LiesInt (SEG A B)) : (SEG_nd A B h1).toDir = (SEG_nd A C (ne_source_of_lies_int_seg_nd A B C h1 h2)).toDir := by sorry

theorem lies_int_seg_nd_of_lies_int_seg (A B C : P) (h1 : B ≠ A) (h2 : C LiesInt (SEG A B)) : C LiesInt (SEG_nd A B h1) := by sorry

theorem lies_on_seg_nd_of_lies_on_seg (A B C : P) (h1 : B ≠ A) (h2 : C LiesOn (SEG A B)) : C LiesOn (SEG_nd A B h1) := by sorry

namespace Ray

theorem snd_pt_lies_int_mk_pt_pt {A B : P} (h : B ≠ A) : B LiesInt (RAY A B h) := by sorry

end Ray

end EuclidGeom
