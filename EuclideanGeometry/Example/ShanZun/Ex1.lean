import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Shan_Problem_1_1
/- In $\triangle ABC$, let $AD$ be the height and $AE$ be the angle bisector of $\triangle ABC$.
Prove that $\angle DAE = (\angle CBA - \angle ACB) / 2$. -/


-- Let $\triangle ABC$ be an nondegenerate triangle.
variable {A B C : P} {hnd : ¬ colinear A B C}


end Shan_Problem_1_1



namespace Shan_Problem_1_2
/- Let $\triangle ABC$ be a nondegenerate isosceles triangle in which $AB = AC$.
Let $D$ be a point on the extension of $AB$ and $E$ a point on the extension of $AC$,
such that $\angle EBC = \angle BCD$.
Prove that $\angle CDA = \angle BEA$. -/

variable {A B C : P} {hnd : ¬ colinear A B C} {hisoc : (▵ A B C).IsIsoceles}
-- Claim: $A \ne B$ and $A \ne C$ and $B \ne C$.
--This is because vertices of nondegenerate triangles are distinct.
lemma b_ne_a : B ≠ A := (ne_of_not_colinear hnd).2.2
lemma c_ne_a : C ≠ A := (ne_of_not_colinear hnd).2.1.symm
lemma b_ne_c : B ≠ C := (ne_of_not_colinear hnd).1.symm
-- Let $D$ and $e$ be points on the extension of the nondegenerate segments of $AB$ and $AC$, respectively.
variable {D E : P} {hd : D LiesOn (SEG_nd A B (b_ne_a (hnd := hnd))).extension}
{he : E LiesOn (SEG_nd A C (c_ne_a (hnd := hnd))).extension}
-- Claim: $E \ne B$ and $D \ne C$. This is because $E$ lies on line AC, but $B$ doesn't lies on AC; $D$ lies on line AB, but $C$ doesn't lies on AB.

lemma e_ne_b : E ≠ B := ne_of_lieson_and_not_lieson (Seg_nd.lies_on_toline_of_lies_on_extn he) ((Line.lies_on_iff_colinear_of_ne_lies_on_lies_on (c_ne_a (hnd := hnd)) (Seg_nd.lies_on_toLine_of_lie_on (Seg.source_lies_on (seg := (SEG_nd A C (c_ne_a (hnd := hnd))).1))) (Seg_nd.lies_on_toLine_of_lie_on (Seg.target_lies_on (seg := (SEG_nd A C (c_ne_a (hnd := hnd))).1))) B).mp.mt (flip_colinear_snd_trd.mt hnd))
lemma d_ne_c : D ≠ C := ne_of_lieson_and_not_lieson (Seg_nd.lies_on_toline_of_lies_on_extn hd) ((Line.lies_on_iff_colinear_of_ne_lies_on_lies_on (b_ne_a (hnd := hnd)) (Seg_nd.lies_on_toLine_of_lie_on (Seg.source_lies_on (seg := (SEG_nd A B (b_ne_a (hnd := hnd))).1))) (Seg_nd.lies_on_toLine_of_lie_on (Seg.target_lies_on (seg := (SEG_nd A B (b_ne_a (hnd := hnd))).1))) C).mp.mt hnd)
-- Claim: $A \ne D$ and $A \ne E$. This is because $E$ lies on extension of $AC$, but $A$ doesn't lies on extension of $AC$; $D$ lies on extension of $AB$, but $A$ doesn't lies on extension of $AB$
lemma a_ne_d : A ≠ D := by
  have a_notlieson_ab_extn : ¬ A LiesOn (SEG_nd A B (b_ne_a (hnd := hnd))).extension := by
    apply Ray.not_lies_on_of_lies_int_rev
    simp only [extn_eq_rev_toray_rev, Ray.rev_rev_eq_self]
    constructor
    exact Seg_nd.lies_on_toRay_of_lies_on Seg.target_lies_on
    exact (b_ne_a (hnd := hnd)).symm
  exact (ne_of_lieson_and_not_lieson hd a_notlieson_ab_extn).symm
lemma a_ne_e : A ≠ E := by
  have a_notlieson_ac_extn : ¬ A LiesOn (SEG_nd A C (c_ne_a (hnd := hnd))).extension := by
    apply Ray.not_lies_on_of_lies_int_rev
    simp only [extn_eq_rev_toray_rev, Ray.rev_rev_eq_self]
    constructor
    exact Seg_nd.lies_on_toRay_of_lies_on Seg.target_lies_on
    exact (c_ne_a (hnd := hnd)).symm
  exact (ne_of_lieson_and_not_lieson he a_notlieson_ac_extn).symm
-- -- We have $\angle EBC = \angle BCD$.
variable (hang : ∠ E B C e_ne_b b_ne_c.symm =  ∠ B C D b_ne_c d_ne_c)

theorem Shan_Problem_1_2 : ∠ C D A (d_ne_c (hnd := hnd) (hd := hd)).symm (a_ne_d (hnd := hnd) (hd := hd)) = ∠ B E A (e_ne_b (hnd := hnd) (he := he)).symm (a_ne_e (hnd := hnd) (he := he)) := sorry

end Shan_Problem_1_2
