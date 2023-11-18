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
variable {D E : P} {hd : D LiesOn (SEG_nd B A a_ne_b).extension} {he : E LiesOn (SEG_nd B C b_ne_c.symm).extension}
-- We have $AE = BD$
variable {h : (SEG A E).length = (SEG A E).length}

theorem Shan_Problem_2_11 : (SEG C E).length = (SEG D E).length := sorry

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

theorem Shan_Problem_2_36 : (SEG_nd A G g_ne_a) ∥ (SEG_nd C D d_ne_c) := sorry

end Shan_Problem_2_36

namespace Shan_Problem_2_37
/- In $\triangle ABC$
$\angle BAC = \pi / 4$,
$BE, CF$ are heights,
such that $AE = 2 EC$
Prove that $AF = 3 FB$ -/

-- We have acute triangle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C} {hacute : Triangle_nd.IsAcute (TRI_nd A B C hnd)}
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
-- $G,H$ lies on $BC$
variable {G H : P} {hg : G LiesInt (SEG B C)} {hh : H LiesInt (SEG B C)}
-- Claim : $G \ne E$ and $H \ne F$
lemma g_ne_e : G ≠ E := sorry
lemma h_ne_f : H ≠ F := sorry
-- $EG \parallel AC$ and $FH \parallel AC$
variable {para₁ : (SEG_nd E G g_ne_e) ∥ (SEG_nd A C c_ne_a)} {para₂ : (SEG_nd F H h_ne_f) ∥ (SEG_nd A C c_ne_a)}

theorem Shan_Problem_2_43 :(SEG E G).length + (SEG F H).length = (SEG A C).length := sorry

end Shan_Problem_2_43
