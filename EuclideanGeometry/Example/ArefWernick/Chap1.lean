import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Aref-Wernick book: Problems and Solutions in Euclidean Geometry Chapter 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Aref_Wernick_Exercise_1_1
/- Two triangles are congruent if two sides and the enclosed median in one triangle are respectively equal to two sides and the enclosed median of the other.
In other words, let $\triangle A_1B_1C_1$ and $\triangle A_2B_2C_2$ be two triangles and let $A_1M_1$ and $A_2M_2$ be the corresponding medians. Suppose that $A_1B_1 = A_2B_2$, $A_1C_1 = A_2C_2$, and $A_1M_1 = A_2M_2$.
Prove that $\triangle A_1B_1C_1$ is congruent to $\triangle A_2B_2C_2$. -/

-- We have two triangles $\triangle A_1B_1C_1,A_2B_2C_2$ .
variable {A₁ B₁ C₁ A₂ B₂ C₂ : P} {hnd₁ : ¬ colinear A₁ B₁ C₁} {hnd₂ : ¬ colinear A₂ B₂ C₂}
-- $M_1,M_2$ are midpoints of $B_1C_1,B_2,C_2$
variable {M₁ M₂ : P} {hm₁ : M₁ = (SEG B₁ C₁).midpoint} {hm₂ : M₂ = (SEG B₂ C₂).midpoint}
-- We have $A_1B_1 = A_2B_2$, $A_1C_1 = A_2C_2$, and $A_1M_1 = A_2M_2$.
variable {h₁ : (SEG A₁ B₁).length = (SEG A₂ B₂).length} {h₂ : (SEG A₁ C₁).length = (SEG A₂ C₂).length} {h₃ : (SEG A₁ M₁).length = (SEG A₂ M₂).length}

-- Theorem : $\triangle A_1B_1C_1$ is congruent to $\triangle A_2B_2C_2$
theorem Aref_Wernick_Exercise_1_1 : (TRI_nd A₁ B₁ C₁ hnd₁) ≅ (TRI_nd A₂ B₂ C₂ hnd₂) := sorry

end Aref_Wernick_Exercise_1_1

namespace Aref_Wernick_Exercise_1_2
/- Let $D$ and $E$ be points on two sides $AB$ and $AC$ of a triangle $ABC$, respectively,
 such that $BD = BC = CE$. The segments $BE$ and $CD$ intersect at $F$.

Prove that $\angle BFD = \pi / 2 - \angle CAB$. -/

-- We have triangle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $B \ne A$ and $C \ne A$ and $B \ne C$.
--This is because vertices of nondegenerate triangles are distinct.
lemma b_ne_a : B ≠ A := (ne_of_not_colinear hnd).2.2
lemma c_ne_a : C ≠ A := (ne_of_not_colinear hnd).2.1.symm
lemma b_ne_c : B ≠ C := (ne_of_not_colinear hnd).1.symm
-- Let $D$ and $E$ be points lies on the nondegenerate segments of $AB$ and $AC$
variable{D E : P} {hd : D LiesInt SEG A B} {he : E LiesInt SEG A C}
-- We have $BD=BC$ and $BC=CE$
variable (hedge : (SEG B D).length = (SEG B C).length ∧ (SEG B C).length = (SEG C E).length)
-- Claim: $D \ne C, D \ne B, E \ne A, E \ne B$
lemma d_ne_c : D ≠ C := sorry
lemma d_ne_b : D ≠ B := sorry
lemma e_ne_a : E ≠ A := sorry
lemma e_ne_b : E ≠ B := sorry
-- The segments $BE$ and $CD$ intersect at $F$.
variable {F : P} {hf : is_inx F (SEG B E) (SEG C D)}
-- Claim: $B \ne f$ and $D \ne F$.
lemma b_ne_f : B ≠ F := by
  have d_not_lies_on_bc : ¬ D LiesOn (LIN B C (ne_of_not_colinear hnd).1) := by
    by_contra not
    have line_neq : (LIN A B (b_ne_a (hnd := hnd))).toProj ≠ (LIN B C (b_ne_c (hnd := hnd)).symm).toProj := (edge_toLine_not_para_of_not_colinear hnd).1
    have aa : D LiesOn (SEG_nd A B (b_ne_a (hnd := hnd))).1 := Seg.lies_on_of_lies_int hd
    have inxd : is_inx D (LIN B C (ne_of_not_colinear hnd).1) (LIN A B (ne_of_not_colinear hnd).2.2) := by
      exact ⟨not, SegND.lies_on_toLine_of_lie_on aa⟩
    have inxb : is_inx B (LIN B C (ne_of_not_colinear hnd).1) (LIN A B (ne_of_not_colinear hnd).2.2) := by
      exact ⟨(SEG_nd B C (ne_of_not_colinear hnd).1).source_lies_on_toLine , (SEG_nd A B (ne_of_not_colinear hnd).2.2).target_lies_on_toLine ⟩
    exact d_ne_b (unique_of_inx_of_line_of_not_para line_neq inxb.symm inxd.symm)
  have bcd_notcoli : ¬ colinear B C D := (Line.lies_on_line_of_pt_pt_iff_colinear (b_ne_c (hnd := hnd)).symm D).mpr.mt d_not_lies_on_bc
  have b_not_lies_on_cd : ¬ B LiesOn (LIN C D d_ne_c) := (Line.lies_on_line_of_pt_pt_iff_colinear d_ne_c B).mp.mt (flip_colinear_snd_trd.mt (flip_colinear_fst_snd.mt bcd_notcoli))
  have f_lies_on_seg_cd : F LiesOn (SEG_nd C D d_ne_c).1 := hf.2
  exact (ne_of_lieson_and_not_lieson (SegND.lies_on_toLine_of_lie_on f_lies_on_seg_cd) b_not_lies_on_cd).symm
lemma d_ne_f : D ≠ F := sorry

-- Theorem : $\angle BFD = \pi / 2 - \angle CAB$
theorem Aref_Wernick_Exercise_1_2 : ∠ B F D (b_ne_f (hnd := hnd) (hd := hd) (hf := hf)) d_ne_f = ↑(π / 2) - ∠ C A B (c_ne_a (hnd := hnd)) (b_ne_a (hnd := hnd)) := sorry

end Aref_Wernick_Exercise_1_2

end EuclidGeom
