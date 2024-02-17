import EuclideanGeometry.Foundation.Axiom.Linear.Ratio
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

/-!
# Parallel lines divide segments proportionally
-/

noncomputable section
namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P] {l₁ l₂ l₃ : Line P} {A B C D E F X : P}

theorem divratio_eq_of_para₁₂₃ (ha : A LiesOn l₁) (hb : B LiesOn l₁) (hc : C LiesOn l₂) (hd : D LiesOn l₂) (h : l₁ ∥ l₂) (ne : l₁ ≠ l₂) (hxac : Collinear A C X) (hxbd : Collinear B D X) : divratio X A C = divratio X B D := sorry

theorem divratio_eq_of_para₁₃₂ (ha : A LiesOn l₁) (hb : B LiesOn l₁) (hc : C LiesOn l₂) (hd : D LiesOn l₂) (h : l₁ ∥ l₂) (ne : l₁ ≠ l₂) (hxac : Collinear A C X) (hxbd : Collinear B D X) : divratio X C A = divratio X D B := sorry

theorem divratio_eq_of_para₂₁₃ (ha : A LiesOn l₁) (hb : B LiesOn l₁) (hc : C LiesOn l₂) (hd : D LiesOn l₂) (h : l₁ ∥ l₂) (ne : l₁ ≠ l₂) (hxac : Collinear A C X) (hxbd : Collinear B D X) : divratio A X C = divratio B X D := sorry

theorem divratio_eq_of_para₂₃₁ (ha : A LiesOn l₁) (hb : B LiesOn l₁) (hc : C LiesOn l₂) (hd : D LiesOn l₂) (h : l₁ ∥ l₂) (ne : l₁ ≠ l₂) (hxac : Collinear A C X) (hxbd : Collinear B D X) : divratio A C X = divratio B D X := sorry

theorem divratio_eq_of_para₃₁₂ (ha : A LiesOn l₁) (hb : B LiesOn l₁) (hc : C LiesOn l₂) (hd : D LiesOn l₂) (h : l₁ ∥ l₂) (ne : l₁ ≠ l₂) (hxac : Collinear A C X) (hxbd : Collinear B D X) : divratio C X A = divratio D X B := sorry

theorem divratio_eq_of_para₃₂₁ (ha : A LiesOn l₁) (hb : B LiesOn l₁) (hc : C LiesOn l₂) (hd : D LiesOn l₂) (h : l₁ ∥ l₂) (ne : l₁ ≠ l₂) (hxac : Collinear A C X) (hxbd : Collinear B D X) : divratio C A X = divratio D B X := sorry

theorem divratio_eq_of_para_of_para (ha : A LiesOn l₁) (hb : B LiesOn l₁) (hc : C LiesOn l₂) (hd : D LiesOn l₂) (he : E LiesOn l₃) (hf : F LiesOn l₃) (h₁₂ : l₁ ∥ l₂) (h₁₃ : l₁ ∥ l₃) (ne : l₁ ≠ l₂)  (hace : Collinear A C E) (hbdf : Collinear B D F) : divratio A C E = divratio B D F := sorry

theorem line_inx_lies_on_seg_iff_of_para (ha : A LiesOn l₁) (hb : B LiesOn l₁) (hc : C LiesOn l₂) (hd : D LiesOn l₂) (h : l₁ ∥ l₂) (ne : l₁ ≠ l₂) (hxac : Collinear A C X) (hxbd : Collinear B D X) : X LiesOn (SEG A C) ↔ X LiesOn (SEG B D) := sorry

theorem line_inx_lies_int_seg_iff_of_para (ha : A LiesOn l₁) (hb : B LiesOn l₁) (hc : C LiesOn l₂) (hd : D LiesOn l₂) (h : l₁ ∥ l₂) (ne : l₁ ≠ l₂) (hxac : Collinear A C X) (hxbd : Collinear B D X) : X LiesInt (SEG A C) ↔ X LiesInt (SEG B D) := sorry

theorem lies_on_seg_line_inx_iff_of_para (ha : A LiesOn l₁) (hb : B LiesOn l₁) (hc : C LiesOn l₂) (hd : D LiesOn l₂) (h : l₁ ∥ l₂) (ne : l₁ ≠ l₂) (hxac : Collinear A C X) (hxbd : Collinear B D X) : A LiesOn (SEG C X) ↔ B LiesOn (SEG D X) := sorry

theorem lies_int_seg_line_inx_iff_of_para (ha : A LiesOn l₁) (hb : B LiesOn l₁) (hc : C LiesOn l₂) (hd : D LiesOn l₂) (h : l₁ ∥ l₂) (ne : l₁ ≠ l₂) (hxac : Collinear A C X) (hxbd : Collinear B D X) : A LiesInt (SEG C X) ↔ B LiesInt (SEG D X) := sorry

variable [PtNe A B] [PtNe C D] [PtNe E F]

theorem divratio_eq_of_para' (h : (LIN A B) ∥ (LIN C D)) (hxac : Collinear A C X) (hxbd : Collinear B D X) (hn : (LIN A B) ≠ (LIN C D)) : divratio X A C = divratio X B D := sorry

theorem divratio_eq_of_para_of_para' (habcd : (LIN A B) ∥ (LIN C D)) (habef : (LIN A B) ∥ (LIN E F)) (hace : Collinear A C E) (hbdf : Collinear B D F) (hn : (LIN A B) ≠ (LIN C D)) : divratio A C E = divratio B D F := sorry

theorem line_inx_lies_on_seg_iff_of_para' (h : (LIN A B) ∥ (LIN C D)) (hxac : Collinear A C X) (hxbd : Collinear B D X) (hn : (LIN A B) ≠ (LIN C D)) : X LiesOn (SEG A C) ↔ X LiesOn (SEG B D) := sorry

theorem line_inx_lies_int_seg_iff_of_para' (h : (LIN A B) ∥ (LIN C D)) (hxac : Collinear A C X) (hxbd : Collinear B D X) (hn : (LIN A B) ≠ (LIN C D)) : X LiesInt (SEG A C) ↔ X LiesInt (SEG B D) := sorry

theorem lies_on_seg_line_inx_iff_of_para' (h : (LIN A B) ∥ (LIN C D)) (hxac : Collinear A C X) (hxbd : Collinear B D X) (hn : (LIN A B) ≠ (LIN C D)) : A LiesOn (SEG C X) ↔ B LiesOn (SEG D X) := sorry

theorem lies_int_seg_line_inx_iff_of_para' (h : (LIN A B) ∥ (LIN C D)) (hxac : Collinear A C X) (hxbd : Collinear B D X) (hn : (LIN A B) ≠ (LIN C D)) : A LiesInt (SEG C X) ↔ B LiesInt (SEG D X) := sorry

end EuclidGeom
