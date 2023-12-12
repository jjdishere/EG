import EuclideanGeometry.Foundation.Index

noncomputable section


namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Shan_Problem_2_11
/- Let $\triangle ABC$ be a regular triangle,
Let $E$ be a point on the extension of $BA$ and $D$ a point on the extension of $BC$
such that $AE = BD$, connect $CE,DE$
Prove that $CE = DE$ -/

-- Let $\triangle ABC$ be a regular triangle
variable {A B C : P} {hnd : ¬ colinear A B C} {hreg : (▵ A B C).IsRegular}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- Let $E$ be a point on the extension of $BA$ and $D$ a point on the extension of $BC$
variable {D E : P} {he : D LiesInt (SEG_nd B C b_ne_c.symm).extension} {he : E LiesInt (SEG_nd B A a_ne_b).extension}
-- We have $AE = BD$
variable {h : (SEG A E).length = (SEG B D).length}

-- Theorem : $CE = DE$
theorem Shan_Problem_2_11 : (SEG C E).length = (SEG D E).length := by
/-
  Extend $BD$ to $F$ such that $DF = BC$.
  Then $BF = BD + DF = AE + AB = BE$, and $\angle FBE = 60^{\circ}$  or $-60^{\circ}$.
  So $\triangle EBF$ is regular, $EF = EB$, $\angle EBC = - \angle EFD$.
  Thus $\triangle BEC$ is anti-congruence to $\triangle FED$ by SAS.
  Therefore $CE = DE$
-/
  -- Claim: $D \ne B$, $E \ne B$
  have d_ne_b : D ≠ B := sorry
  have e_ne_b : E ≠ B := sorry
  -- Extend $BD$ to $F$ such that $DF = CB$
  let F := Ray.extpoint (SEG_nd B D d_ne_b).extension (SEG B C).length
  have df_eq_cb : (SEG D F).length = (SEG C B).length := by
    calc
      -- $DF = BC$ from above
      _ = (SEG B C).length := by
        apply seg_length_eq_dist_of_extpoint (SEG_nd B D d_ne_b).extension
        simp
        exact length_nonneg
      -- $BC = CB$ by symmetry
      _ = (SEG C B).length := by
        simp only [length_of_rev_eq_length']
  -- Claim: $F \ne B$, $D \ne F$, $E \ne F$
  have f_ne_b : F ≠ B := sorry
  have d_ne_f : D ≠ F := sorry
  have e_ne_f : E ≠ F := sorry
  -- $F$ lies in extension of $BD$
  have f_lies_int_bd_extn : F LiesInt (SEG_nd B D d_ne_b).extension := by
    apply lies_int_of_pos_extpoint (r := (SEG B C).length)
    simp
    rw [length_pos_iff_nd]
    exact b_ne_c
  -- $D$ lies on $BF$
  have d_lies_on_bf : D LiesOn (SEG_nd B F f_ne_b) :=  SegND.lies_on_of_lies_int (SegND.target_lies_int_seg_source_pt_of_pt_lies_int_extn f_lies_int_bd_extn)
  -- $C$ lies on $BF$
  have c_lies_on_bf : C LiesOn (SEG_nd B F f_ne_b) := sorry
  -- $A$ lies on $BE$
  have a_lies_on_be : A LiesOn (SEG_nd B E e_ne_b) := SegND.lies_on_of_lies_int (SegND.target_lies_int_seg_source_pt_of_pt_lies_int_extn he)
  -- $BF = BD + DF = AE + AB = BE$
  have bf_eq_be : (SEG B F).length = (SEG B E).length := by
    calc
      -- $BF = BD + DF$
      _ = (SEG B D).length + (SEG D F).length := by
        exact length_eq_length_add_length d_lies_on_bf
      -- $BD + DF = BD + BC$
      _ = (SEG B D).length + (SEG B C).length := by
        simp only [length_of_rev_eq_length', df_eq_cb]
      -- $BD + BC = AE + BC$
      _ = (SEG A E).length + (SEG B C).length := by rw [h]
      -- $AE + BC = AE + AB$
      _ = (SEG A E).length + (SEG A B).length := by
        -- $AB = BC$ by $\triangle ABC$ is regular
        have ab_eq_bc : (SEG B C).length = (SEG A B).length := hreg.2
        rw[ab_eq_bc]
      -- $AE + AB = BA + AE$ by symmetry
      _ = (SEG B A).length + (SEG A E).length := by
        simp only [length_of_rev_eq_length', add_comm]
      -- $BA + AE = BE$
      _ = (SEG B E).length := by
        exact (length_eq_length_add_length a_lies_on_be).symm
  -- $\angle EBF = \angle ABC$
  have ang₁ : ∠ F B E f_ne_b e_ne_b = ∠ C B A c_ne_a a_ne_b := by
    apply eq_ang_value_of_lies_int_lies_int
    constructor
    exact SegND.lies_on_toray_of_lies_on c_lies_on_bf
    exact b_ne_c.symm
    constructor
    exact SegND.lies_on_toray_of_lies_on a_lies_on_be
    exact a_ne_b
  -- $\angle FBE = \frac{\pi}{3}$ or $ - \frac{\pi}{3}$
  have ang_ebf_eq_sixty : ∠ F B E f_ne_b e_ne_b = ↑ (π / 3) ∨  ∠ F B E f_ne_b e_ne_b = ↑ (- π / 3) := by
    by_cases h₁ : (TRI_nd A B C hnd).is_cclock
    have sixty₁ : ∠ C B A a_ne_b b_ne_c.symm = ↑ (π / 3) := (ang_eq_sixty_deg_of_cclock_regular_tri (TRI_nd A B C hnd) h₁ hreg).2.1
    rw[← ang₁] at sixty₁
    left
    exact sixty₁
    have sixty₂ : ∠ C B A a_ne_b b_ne_c.symm = ↑ (- π / 3) := (ang_eq_sixty_deg_of_acclock_regular_tri (TRI_nd A B C hnd) h₁ hreg).2.1
    rw[← ang₁] at sixty₂
    right
    exact sixty₂
  -- $BFE$ is not colinear
  have bfe_not_colinear : ¬ colinear B F E := sorry
  -- $\triangle BFE$ is regular
  have bfe_is_regular : (TRI_nd B F E bfe_not_colinear).1.IsRegular := by
    apply regular_tri_of_isoceles_tri_of_fst_ang_eq_sixty_deg
    exact ang_ebf_eq_sixty
    rw[← Seg.length_of_rev_eq_length (seg := (SEG B E))] at bf_eq_be
    exact bf_eq_be.symm
  -- $\angle EBC = - \angle EFD$ because $\triangle BFE$ is regular
  have ang₂ : ∠ E B C e_ne_b b_ne_c.symm = - ∠ E F D e_ne_f d_ne_f := by
    -- 下面两个sorry留下的是很烦的相同射线推相同角度
    -- $\angle EBC = - \angle FBE$
    have ang₂' : ∠ E B C e_ne_b b_ne_c.symm = -∠ F B E f_ne_b e_ne_b := sorry
    -- $\angle EFD = \angle EFB$
    have ang₂'' : ∠ E F D e_ne_f d_ne_f = ∠ E F B e_ne_f f_ne_b.symm := sorry
    -- $\angle EFB = \angle FBE$
    have ang₂''' : ∠ E F B e_ne_f f_ne_b.symm = ∠ F B E f_ne_b e_ne_b := ((regular_tri_iff_eq_angle_of_nd_tri (TRI_nd B F E bfe_not_colinear)).mp bfe_is_regular).1.symm
    rw[ang₂', ang₂'', ang₂''']
  -- $FE = BE$ because $\triangle BFE$ is regular
  have fe_eq_be : (SEG F E).length = (SEG B E).length := by
    calc
    -- $FE = EB$ because $\triangle BFE$ is regular
    _ = (SEG E B).length := by
      exact bfe_is_regular.1
    -- $EB = BE$ by symmetry
    _ = (SEG B E).length := by
      simp only [length_of_rev_eq_length']
  -- $BEC$ is not colinear and $FED$ is not colinear
  have bec_not_colinear : ¬ colinear B E C := sorry
  have fed_not_colinear : ¬ colinear F E D := sorry
  -- $\triangle BCE$ is anti-congruence to $\triangle FDE$
  have cong : (TRI_nd B E C bec_not_colinear) ≅ₐ (TRI_nd F E D fed_not_colinear) := TriangleND.acongr_of_SAS df_eq_cb.symm ang₂ fe_eq_be.symm
  -- $EC = ED$ because $\triangle BCE \cong \triangle FDE$
  have ec_eq_ed : (SEG E C).length = (SEG E D).length := cong.edge₁
  rw[length_of_rev_eq_length', ec_eq_ed]
  simp only [length_of_rev_eq_length']
end Shan_Problem_2_11

namespace Shan_Problem_2_22
/- In $\triangle ABC$, $D$ is midpoint of $BA$, $E$ us midpoint of $BC$,
$F,G$ are points of trisection of $AC$,
line $DF$ and $EG$ intersect at $H$
Prove that quadrilateral $ABCH$ is parallelogram -/

-- We have triangle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- $D$ is midpoint of $BA$, $E$ is midpoint of $BC$
variable {D E : P} {hd : D = (SEG B A).midpoint} {he : E = (SEG B C).midpoint}
-- $F,G$ are points of trisection of $AC$
variable {F G : P} {hf : F LiesInt (SEG_nd A C c_ne_a).1} {he : E LiesInt (SEG_nd A C c_ne_a).1} {htri : (SEG A F).length = (SEG F G).length ∧ (SEG F G).length = (SEG G C).length}
-- Claim: $F \ne D$ and $G \ne E$
lemma f_ne_d : F ≠ D := sorry
lemma g_ne_e : G ≠ E := sorry
-- $H$ is the intersection of line $DF$ and $EG$
variable {H : P} {hh : is_inx H (LIN D F f_ne_d) (LIN E G g_ne_e)}

-- Theorem : quadrilateral $ABCH$ is parallelogram
theorem Shan_Problem_2_22 : QDR A B C H IsPRG := sorry

end Shan_Problem_2_22

namespace Shan_Problem_2_36
/- In $\triangle ABC$, $D,E$ are points in $AB,AC$ respectively,
such that $DE \parallel BC$,
$F,G$ are points lies on line $BC$,
such that $FB = CG$ and $AF \parallel BE$ ,
Prove that $AG \parallel DC$-/

-- We have triangle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- $D,E$ are points in $AB,AC$ respectively
variable {D E : P} {hd : D LiesInt (SEG_nd A B a_ne_b.symm).1} {he : E LiesInt (SEG_nd A C c_ne_a).1}
-- $F,G$ are points lies on line $BC$
variable {F G : P} {hf : F LiesOn (LIN B C b_ne_c.symm)} {hg : G LiesOn (LIN B C b_ne_c.symm)}
-- We have $FB = CG$
variable {hedge : (SEG F B).length = (SEG C G).length}
-- Claim : $F \ne A$ and $E \ne B$
lemma f_ne_a : F ≠ A := sorry
lemma e_ne_b : E ≠ B := sorry
-- We have $AF \parallel BE$
variable {hpara : (SEG_nd A F f_ne_a) ∥ (SEG_nd B E e_ne_b)}
-- Claim: $G \ne A$ and $D \ne C$
lemma g_ne_a : G ≠ A := sorry
lemma d_ne_c : D ≠ C := sorry

-- Theorem : $AG \parallel DC$
theorem Shan_Problem_2_36 : (SEG_nd A G g_ne_a) ∥ (SEG_nd C D d_ne_c) := sorry

end Shan_Problem_2_36

namespace Shan_Problem_2_37
/- In $\triangle ABC$
$\angle BAC = \pi / 4$,
$BE, CF$ are heights,
such that $AE = 2 EC$
Prove that $AF = 3 FB$ -/

-- We have acute triangle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C} {hacute : TriangleND.IsAcute (TRI_nd A B C hnd)}
-- 这个题应该需要加锐角三角形的限制，否则需要条件中的$AE = 2 EC$是有向线段的相等
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- $BE, CF$ are heights
variable {E F : P} {he : E = perp_foot B (LIN A C c_ne_a)} {hf : F = perp_foot C (LIN A B a_ne_b.symm)}
-- 之后应该会需要一个锐角三角形中，垂足落在边的内部的定理
-- We have $AE = 2 EC$
variable {h : (SEG A E).length = 2 * (SEG E C).length}

-- Theorem : $AF = 3 FB$
theorem Shan_Problem_2_37 : (SEG A F).length = 3 * (SEG F B).length := sorry

end Shan_Problem_2_37

namespace Shan_Problem_2_38
/- In $\triangle ABC$, $D$ is the midpoint of $BC$,
let the angle bisectors of $\angle ADB$ and $\angle ADC$ intersect $AB$ and $AC$ at $E,F$,
Prove that $EF \parallel BC$-/

-- We have triangle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- $D$ is the midpoint of $BC$
variable {D : P} {hd : D = (SEG B C).midpoint}
-- Claim: $A \ne D$ and $B \ne D$ and $C \ne D$
lemma a_ne_d : A ≠ D := sorry
lemma b_ne_d : B ≠ D := sorry
lemma c_ne_d : C ≠ D := sorry
-- let the angle bisectors of $\angle ADB$ and $\angle ADC$ intersect $AB$ and $AC$ at $E,F$
variable {E F : P} {he : is_inx E (ANG A D B a_ne_d b_ne_d).AngBis (SEG A B)} {hf : is_inx F (ANG A D C a_ne_d c_ne_d).AngBis (SEG A C)}
-- Claim: $F \ne E$
lemma f_ne_e : F ≠ E := sorry

-- Theorem : $EF \parallel BC$
theorem Shan_Problem_2_38 : (SEG_nd E F f_ne_e) ∥ (SEG_nd B C b_ne_c.symm) := sorry

end Shan_Problem_2_38

namespace Shan_Problem_2_42
/- In $\triangle ABC$, $D$ is the midpoint of $AB$,
$E$ lies on $AC$ such that $AE = 2 CE$,
$CD,BE$ intersects at $O$
Prove that $OE = \frac{1}{4} BE$-/

-- We have triangle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- $D$ is midpoint of $AB$
variable {D : P} {hd : D = (SEG A B).midpoint}
-- $E$ lies on $AC$ such that $AE = 2 CE$,
variable {E : P} {he : E LiesInt (SEG A C) ∧ (SEG A E).length = 2 * (SEG C E).length}
-- $CD,BE$ intersects at $O$
variable {O : P} {ho : is_inx O (SEG C D) (SEG B E)}

-- Theorem : $OE = \frac{1}{4} BE$
theorem Shan_Problem_2_42 : (SEG O E).length = (1 / 4) * (SEG B E).length := sorry

end Shan_Problem_2_42

namespace Shan_Problem_2_43
/- In $\triangle ABC$, $E,F$ lies on $AB$ such that $AE = FB$,
The parallel line to $AC$ of $E,F$ intersect $BC$ at $G,H$ respectively,
Prove that $EG + FH = AC$-/

-- We have triangle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- $E,F$ lies on $AB$ such that $AE = FB$
variable {E F : P} {he : E LiesInt (SEG A B)} {hf : F LiesInt (SEG A B)} {hef : (SEG A E).length = (SEG F B).length}
-- 此处以后可能会专门加上过一个点做平行线的定义,从而更改条件的叙述
-- $l_1,l_2$ are parallel lines to $AC$ of $E,F$ respectively
variable {l₁ l₂ : Line P} {hl₁ : l₁ ∥ (SEG_nd A C c_ne_a) ∧ E LiesOn l₁} {hl₂ : l₂ ∥ (SEG_nd A C c_ne_a) ∧ F LiesOn l₂}
-- $l_1,l_2$ intersect $BC$ at $G,H$ respectively
variable {G H : P} {hg : is_inx G l₁ (SEG B C)} {hh : is_inx H l₂ (SEG B C)}

-- Theorem : $EG + FH = AC$
theorem Shan_Problem_2_43 :(SEG E G).length + (SEG F H).length = (SEG A C).length := sorry

end Shan_Problem_2_43

namespace Shan_Problem_2_44
/- $A,B,C$ are points on line $l$ such that $\frac{AB}{BC} = \frac{m}{n}$,
$A₁,B₁,C₁$ are points on line $l₁$ such that $AA₁ \parallel BB₁ \parallel CC₁$.
Prove that $BB₁ = \frac{n}{m+n} AA₁ + \frac{m}{m+n} CC₁$-/

-- We have line $l$ and points $A,B,C$ lies on $l$
variable {l : Line P} {A B C : P} {ha : A LiesOn l} {hb : B LiesOn l} {hc : C LiesOn l}
-- We have $\frac{AB}{BC} = \frac{m}{n}$
variable {m n : ℝ} {hpos : m > 0 ∧ n > 0} {hratio : (SEG A B).length / (SEG B C).length = m / n}
-- We have line $l₁$ and points $A₁,B₁,C₁$ lies on $l₁$
variable {l₁ : Line P} {A₁ B₁ C₁ : P} {ha₁ : A₁ LiesOn l₁} {hb₁ : B₁ LiesOn l₁} {hc₁ : C₁ LiesOn l₁}
-- We have $A \ne A₁$, $B \ne B₁$, $C \ne C₁$ and $AA₁ \parallel BB₁ \parallel CC₁$
variable {nea : A₁ ≠ A} {neb : B₁ ≠ B} {nec : C₁ ≠ C} {hpara₁ : (SEG_nd A A₁ nea) ∥ (SEG_nd B B₁ neb)} {hpara₂ : (SEG_nd B B₁ neb) ∥ (SEG_nd C C₁ nec)}

-- Theorem : $BB₁ = \frac{n}{m+n} AA₁ + \frac{m}{m+n} CC₁$
theorem Shan_Problem_2_44 : (SEG B B₁).length = (n / (m+n)) * (SEG A A₁).length + (m/(m+n)) * (SEG C C₁).length := sorry

end Shan_Problem_2_44

namespace Shan_Problem_2_48
/- $ABCD$ are convex quadrilateral, $AC$ and $BD$ intersect at $E$,
Prove that area of $\triangle ABD$ : area of $\triangle CBD = AE : CE$  -/

-- We have convex quadrilateral $ABCD$
variable {A B C D : P} {hcvx : (QDR A B C D) IsConvex}
-- $AD$ and $BC$ intersect at $E$
variable {E : P} {he : is_inx E (SEG A D) (SEG B C)}

-- Theorem : area of $\triangle ABC :$ area of $\triangle DBC = AE : DE$
theorem Shan_Problem_2_48 : Triangle.area (▵ A B D) / Triangle.area (▵ C B D) = (SEG A E).length / (SEG D E).length := sorry

end Shan_Problem_2_48

namespace Shan_Problem_2_52
/- $AD$ is the height of hypotenuse $BC$ of right triangle $\triangle ABC$,
the angle bisector of $\angle ABC$ intersect $AD$ and $AC$ at $M,N$ respectively,
Prove that $AB^2 - AN^2 = BM \times BN$-/

-- Let triangle $\triangle ABC$ be a right triangle with $\angle BAC = 90^{circ}$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
variable {hright : ∠ B A C a_ne_b.symm c_ne_a = ↑ (π / 2)}
-- 以后有了直角三角形的具体定义之后可能需要改hright
-- $AD$ is the height of $\triangle ABC$
variable {D : P} {hd : D = perp_foot A (LIN B C b_ne_c.symm)}
-- the angle bisector of $\angle ABC$ intersect $AD$ and $AC$ at $M,N$ respectively
variable {l : Ray P} {M N : P} {hl : l = (ANG A B C a_ne_b b_ne_c.symm).AngBis} {hm : is_inx M (SEG A D) l} {hn : is_inx N (SEG A C) l}

-- Theorem : $AB^2 - AN^2 = BM \times BN$
theorem Shan_Problem_2_52 : (SEG A B).length * (SEG A B).length - (SEG A N).length * (SEG A N).length = (SEG B M).length * (SEG B N).length := sorry

end Shan_Problem_2_52
