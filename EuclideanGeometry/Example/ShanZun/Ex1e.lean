import EuclideanGeometry.Foundation.Index

noncomputable section


namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]
namespace Shan_Problem_2_13
/- In $\triangle ABC$. Let D be the midpoint of segment BC, the perpendicular line passing through D of the bisector of $\angle BAC$ intersects AB (respectively, AC) at E ( F, respectively).

Prove that $BE=CF=\frac{1}{2}|AB-AC|$.  -/
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
--Introduce the midpoint D
variable {D : P} {hd : D = (SEG B C).midpoint}
--Introduce two points colinear and the orthogonality. The colinear condition is not helpful.
variable {E F : P} {he : is_inx E (LIN A B a_ne_b.symm) (Line.mk_pt_proj A (ANG B A C a_ne_b.symm c_ne_a).AngBis.toProj.perp)} {hf : is_inx F (LIN A C c_ne_a) (Line.mk_pt_proj A (ANG B A C a_ne_b.symm c_ne_a).AngBis.toProj.perp)}

theorem Shan_Problem_2_13 : (SEG B E).length=|((SEG A B).length-(SEG A C).length)|/2 ∧ (SEG C F).length = |((SEG A B).length-(SEG A C).length)|/2 := sorry

end Shan_Problem_2_13
namespace Shan_Problem_2_18
/- In $\triangle ABC$ $AB < BC$. Let CD be the height, $CE$ be the bisector of $\angle ACB$ and $CF$ be the median.

Prove that If CE liesInt CD and CF, and $\angle ACB=90°$, then CE is the bisector of $\angle FCD$.  -/
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- Introduce the height CD , bisector CE and median CF.
variable {D E F : P}
lemma d_ne_c : D ≠ C := sorry
lemma e_ne_c : E ≠ C := sorry
lemma f_ne_c : F ≠ C := sorry
variable {hd : D LiesOn LINE A B ∧ LINE C D ⟂ LINE A B} {he : E LiesOn SEG A B ∧ (∠ A C E c_ne_a.symm e_ne_c)= (∠ E C B e_ne_c b_ne_c)} {hf : F = (SEG A B).midpoint}

variable {elies_int : Angle.IsInt E (ANG D C F d_ne_c f_ne_c)} {acb_right : (∠ A C B (c_ne_a.symm) (b_ne_c)) = π/2}
theorem Shan_Problem_2_18 :  ∠ D C E d_ne_c e_ne_c = ∠ E C F e_ne_c f_ne_c:=sorry
end Shan_Problem_2_18
