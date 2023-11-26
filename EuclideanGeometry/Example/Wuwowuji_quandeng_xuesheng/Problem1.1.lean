import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Wuwowuji_Problem_1_1
/-
$C, D$ lies in segment $BF$, $AB ∥ DE$, $AB = DF$, $BC = DE$.

Prove that $∠ BAC = ∠ EFD$.
-/

-- $C, D$ lies in segment $BF$, they lies on the same line $l$.
variable {B C D F : P} {l : Line P} {hb : B LiesOn l} {hc : C LiesOn l} {hd : C LiesOn l} {hf : F LiesOn l} {C_int : C LiesInt (SEG B F)} {D_int : D LiesInt (SEG B F)}
-- $A, E$ do not lie on $l$.
variable {A E : P} {ha : ¬ A LiesOn l} {he : ¬ E LiesOn l}

-- need A and E be at the same side of l!!

lemma hnd1 : ¬ colinear A B C := sorry
lemma hnd2 : ¬ colinear D E F := sorry
lemma a_ne_b : A ≠ B := by sorry
lemma d_ne_e : D ≠ E := by sorry
lemma a_ne_c : A ≠ C := by sorry
lemma b_ne_c : B ≠ C := by sorry
lemma e_ne_f : E ≠ F := by sorry
lemma d_ne_f : D ≠ F := by sorry
-- $AB ∥ DE$
variable {hpr : (SEG_nd A B a_ne_b.symm) ∥ (SEG_nd D E d_ne_e.symm)}
-- $AB = DF$
variable {h₁ : (SEG A B).length = (SEG D F).length}
-- $BC = DE$
variable {h₂ : (SEG B C).length = (SEG D E).length}
-- State the main goal.
theorem Wuwowuji_Problem_1_1 : ∠ B A C a_ne_b.symm a_ne_c.symm = ∠ E F D e_ne_f d_ne_f := by
  -- Use SAS to prove $▵ BAC ≅ ▵ DFE$.
  have h : Triangle_nd.IsACongr (TRI_nd B A C hnd1) (TRI_nd D F E hnd2) := by
    apply Triangle_nd.acongr_of_SAS
    · -- $CB = BC = DE = ED$.
      have : (SEG C B).length = (SEG E D).length := by rw [length_of_rev_eq_length', h₂, length_of_rev_eq_length']
      exact this
    · -- $∠ ABC$ and $∠ EDF$ are corresponding angles.
      have : IsCorrespondingAng (ANG A B C a_ne_b b_ne_c.symm) (ANG E D F d_ne_e.symm d_ne_f.symm) := by
        constructor
        · sorry
        · sorry
      -- Then $∠ ABC = ∠ EDF = -∠ FDE$.
      calc
        _ = ∠ E D F d_ne_e.symm d_ne_f.symm := eq_value_of_iscorrespondingang this
        _ = _ := by apply neg_value_of_rev_ang
    · -- $BA = AB = DF$.
      have : (SEG B A).length = (SEG D F).length := by rw [length_of_rev_eq_length', h₁]
      exact this
  -- $∠ BAC = -∠ CAB = - -∠ EFD = ∠ EFD$.
  calc
    _ = - ∠ C A B a_ne_c.symm a_ne_b.symm := by apply neg_value_of_rev_ang
    _ = ∠ E F D e_ne_f d_ne_f := by
      have : ∠ C A B a_ne_c.symm a_ne_b.symm = - ∠ E F D e_ne_f d_ne_f := h.angle₂
      rw [this, neg_neg]
end Wuwowuji_Problem_1_1
