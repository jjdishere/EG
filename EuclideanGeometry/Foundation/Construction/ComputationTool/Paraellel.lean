import EuclideanGeometry.Foundation.Axiom.Linear.Ratio
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

/-!
# Parallel lines divide segments proportionally
-/

noncomputable section
namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P] {A B C D E F X : P} [PtNe A B] [PtNe C D] [PtNe E F]

theorem divratio_eq_of_para (h : (LIN A B) ∥ (LIN C D)) (hxac : Collinear X A C) (hxbd : Collinear X B D) (hn : (LIN A B) ≠ (LIN C D)) : divratio X A C = divratio X B D := sorry

theorem divratio_eq_of_para_of_para (habcd : (LIN A B) ∥ (LIN C D)) (habef : (LIN A B) ∥ (LIN E F)) (hace : Collinear A C E) (hbdf : Collinear B D F) (hn : (LIN C D) ≠ (LIN E F)) : divratio A C E = divratio B D F := sorry

theorem line_inx_lies_on_seg_iff_of_para (h : (LIN A B) ∥ (LIN C D)) (hxac : Collinear X A C) (hxbd : Collinear X B D) (hn : (LIN A B) ≠ (LIN C D)) : X LiesOn (SEG A C) ↔ X LiesOn (SEG B D) := sorry

theorem line_inx_lies_int_seg_iff_of_para (h : (LIN A B) ∥ (LIN C D)) (hxac : Collinear X A C) (hxbd : Collinear X B D) (hn : (LIN A B) ≠ (LIN C D)) : X LiesInt (SEG A C) ↔ X LiesInt (SEG B D) := sorry

theorem lies_on_seg_line_inx_iff_of_para (h : (LIN A B) ∥ (LIN C D)) (hxac : Collinear X A C) (hxbd : Collinear X B D) (hn : (LIN A B) ≠ (LIN C D)) : A LiesOn (SEG C X) ↔ B LiesOn (SEG D X) := sorry

theorem lies_int_seg_line_inx_iff_of_para (h : (LIN A B) ∥ (LIN C D)) (hxac : Collinear X A C) (hxbd : Collinear X B D) (hn : (LIN A B) ≠ (LIN C D)) : A LiesInt (SEG C X) ↔ B LiesInt (SEG D X) := sorry

end EuclidGeom
