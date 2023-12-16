import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Shan_Problem_1_9
/- In $\triangle ABC$, assume that $\angle CBA = 2\cdot \angle ACB$. Let $AD$ be the height and $AE$ the median.

Prove that $AB = 2\cdot DE$. -/

-- We have triangle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- We have $\angle CBA = 2\cdot \angle ACB$
variable {hang : ∠ C B A b_ne_c.symm a_ne_b = 2 * ∠ A C B c_ne_a.symm b_ne_c}
-- $AD$ is the height
variable {D : P} {hd : D = perp_foot A (LIN B C b_ne_c.symm)}
-- $AE$ is the median
variable {E : P} {he : E = (SEG B C).midpoint}

-- Theorem : $AB = 2\cdot DE$
theorem Shan_Problem_1_9 : (SEG A B).length = 2 * (SEG D E).length := by
  -- 下述证明需要在 ¬ AB ⟂ BC 的时候使用，垂直的时候需要另行讨论（此时D = B）
  -- Let $F$ be the midpoint of $AB$
  let F := (SEG A B).midpoint
  -- In right triangle $\triangle ADB$, $DF = FB$ and $DF = \frac{1}{2} AB$
  have df_eq_fb : (SEG D F).length = (SEG F B).length := sorry
  have two_df_eq_ab : 2 * (SEG D F).length = (SEG A B).length := sorry
  -- Claim: $F \ne D$ and $B \ne D$
  have f_ne_d : F ≠ D := sorry
  have b_ne_d : B ≠ D := sorry
  -- $\angle F D B = \angle C B A$
  have ang₁ : ∠ F D B f_ne_d b_ne_d = ∠ C B A b_ne_c.symm a_ne_b := sorry
  -- Claim : $F \ne E$ and $D \ne E$
  have f_ne_e : F ≠ E := sorry
  have d_ne_e : D ≠ E := sorry
  -- $EF$ is median line of $\triangle ABC$, $EF \parallel AC$, so $\angle FED = \angle ACB$
  have ang₂ : ∠ F E D f_ne_e d_ne_e = ∠ A C B c_ne_a.symm b_ne_c := sorry
  -- $\angle FDB = \angle DFE + \angle FED$
  have ang₃ : ∠ F D B f_ne_d b_ne_d = ∠ D F E f_ne_d.symm f_ne_e.symm + ∠ F E D f_ne_e d_ne_e := sorry
  -- $\angle DFE = \angle FED$
  have ang₄ : ∠ E F D f_ne_e.symm f_ne_d.symm = ∠ D E F d_ne_e f_ne_e := sorry
  -- $D F E$ is not colinear
  have dfe_not_colinear : ¬ colinear D F E := sorry
  -- $ED = DF$ because $\triangle DFE$ is isoceles
  have dfe_isoceles : (TRI_nd D F E dfe_not_colinear).1.IsIsoceles := by
    apply is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mpr
    exact ang₄
  have ed_eq_df : (SEG E D).length = (SEG D F).length := by
    exact dfe_isoceles
  -- $ED = DF = \frac{1}{2} AB$
  rw [← two_df_eq_ab, ← ed_eq_df]
  simp
  exact Seg.length_of_rev_eq_length (seg := (SEG D E))
end Shan_Problem_1_9

namespace Shan_Problem_1_10
/- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$ and $\angle BAC = 3\pi /5$. Extend $AC$ to $E$ such that $AE = BC$. Let $D$ be the midpoint of $BE$.

Prove that $AD = DC$. -/

-- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : P} {hnd : ¬ colinear A B C} {hisoc : (▵ A B C).IsIsoceles}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- We have $\angle BAC = 3\pi /5$
variable {hang : ∠ B A C a_ne_b.symm c_ne_a = ↑ (3 * π / 5)}
-- $E$ lies in the extension of $AC$ and $AE = BC$
variable {E : P} {he₁ : E LiesInt (SEG_nd A C c_ne_a).extension} {he₂ : (SEG A E).length = (SEG B C).length}
-- $D$ is the midpoint of $BE$
variable {D : P} {hd : D = (SEG B E).midpoint}

-- Theorem : $AD = DC$
theorem Shan_Problem_1_10 : (SEG A D).length = (SEG D C).length := by
  -- Claim: $A \ne E$
  have a_ne_e : A ≠ E := sorry
  -- Extend $EA$ to $M$ such that $AM = EC$
  let M := Ray.extpoint (SEG_nd E A a_ne_e).extension (SEG E C).length
  have am_eq_ec : (SEG A M).length = (SEG E C).length := by
    apply seg_length_eq_dist_of_extpoint (SEG_nd E A a_ne_e).extension
    simp
    exact length_nonneg
  -- Claim: $M \ne C$, $B \ne M$
  have m_ne_c : M ≠ C := sorry
  have b_ne_m : B ≠ M := sorry
  -- $CM = CA + AM = CA + EC = AE = BC$
  have cm_eq_bc : (SEG C M).length = (SEG B C).length := by
    calc
      -- $CM = CA + AM$
      _ = (SEG C A).length + (SEG A M).length := by
        -- $M$ lies in extension of $CA$
        have m_lies_int_ca_extn : M LiesInt (SEG_nd C A c_ne_a.symm).extension := sorry
        -- $A$ lies on $CM$
        have a_lies_on_cm : A LiesOn (SEG_nd C M m_ne_c).1 := SegND.lies_on_of_lies_int (SegND.target_lies_int_seg_source_pt_of_pt_lies_int_extn m_lies_int_ca_extn)
        exact length_eq_length_add_length a_lies_on_cm
      -- $CA + AM = CA + EC$
      _ = (SEG C A).length + (SEG E C).length := by
        rw[am_eq_ec]
      -- $CA + EC = AC + CE$ by symmetry
      _ = (SEG A C).length + (SEG C E).length := by simp only [length_of_rev_eq_length']
      -- $AC + CE = AE$
      _ = (SEG A E).length := by
        -- $C$ lies on $AE$
        have c_lies_on_ae : C LiesOn (SEG_nd A E a_ne_e.symm).1 := SegND.lies_on_of_lies_int (SegND.target_lies_int_seg_source_pt_of_pt_lies_int_extn he₁)
        exact (length_eq_length_add_length c_lies_on_ae).symm
      -- $AE = BC$
      _ = (SEG B C).length := he₂
  -- $\angle BMC = 2\pi / 5$
  have ang₁ : ∠ B M C b_ne_m m_ne_c.symm = ↑ (2 * π / 5) := sorry
  -- $BAM$ is not colinear
  have bam_not_colinear : ¬ colinear B A M := sorry
  -- $\triangle BAM$ is isoceles
  have isocele₁ : (TRI_nd B A M bam_not_colinear).1.IsIsoceles := sorry
  -- Let $N$ be the midpoint of $AC$
  let N := (SEG A C).midpoint
  -- $DN = \frac{1}{2}MB = \frac{1}{2}AC$
  have dn_eq_half_ac : (SEG D N).length = (1 / 2) * (SEG A C).length := sorry
  sorry
  --需要直角三角形等价于斜边中线等于斜边一半的定理
end Shan_Problem_1_10
