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

end Shan_Problem_1_1

theorem Seg_nd.not_lies_int_extn_and_rev_extn_of_lies_on {A : P} {seg_nd : Seg_nd P} (lieson : A LiesOn seg_nd.1) : ¬ A LiesInt seg_nd.extension ∧ ¬ A LiesInt seg_nd.reverse.extension := by
  constructor
  apply Ray.not_lies_int_of_lies_on_rev
  simp only [extn_eq_rev_toray_rev, Ray.rev_rev_eq_self]
  apply lies_on_toRay_of_lies_on
  apply Seg.lies_on_iff_lies_on_rev.mpr
  exact lieson
  apply Ray.not_lies_int_of_lies_on_rev
  simp only [extn_eq_rev_toray_rev, Ray.rev_rev_eq_self, Seg_nd.rev_rev_eq_self]
  exact lies_on_toRay_of_lies_on lieson

namespace Shan_Problem_1_2
/- Let $\triangle ABC$ be a nondegenerate isosceles triangle in which $AB = AC$.
Let $D$ be a point on the extension of $AB$ and $E$ a point on the extension of $AC$,
such that $\angle EBC = \angle BCD$.
Prove that $\angle CDA = \angle BEA$. -/

-- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : P} {hnd : ¬ colinear A B C} {hisoc : (▵ A B C).IsIsoceles}
-- Claim: $B \ne A$ and $C \ne A$ and $B \ne C$. This is because vertices of nondegenerate triangles are distinct.
lemma b_ne_a : B ≠ A := (ne_of_not_colinear hnd).2.2
lemma c_ne_a : C ≠ A := (ne_of_not_colinear hnd).2.1.symm
lemma b_ne_c : B ≠ C := (ne_of_not_colinear hnd).1.symm
-- Let $D$ and $e$ be points on the extension of the nondegenerate segments of $AB$ and $AC$, respectively.
variable {D E : P} {hd : D LiesInt (SEG_nd A B (b_ne_a (hnd := hnd))).extension} {he : E LiesInt (SEG_nd A C (c_ne_a (hnd := hnd))).extension}
-- Claim: $E \ne B$ and $D \ne C$. This is because $E$ lies on line $AC$, but $B$ doesn't lies on $AC$; $D$ lies on line $AB$, but $C$ doesn't lies on $AB$.
lemma e_ne_b : E ≠ B := by -- for $E \ne B$
  have b_not_lieson_ac := (lies_on_line_of_pt_pt_iff_colinear (c_ne_a (hnd := hnd)) B).mp.mt (flip_colinear_snd_trd.mt hnd) -- $B$ doesn't lies on line $AC$ because $A, B, C$ not colinear
  have e_lieson_ac := Seg_nd.lies_on_toline_of_lies_on_extn (Ray.lies_on_of_lies_int he) -- $E$ lieson line $AC$ because $E$ lies in the extension of $AC$
  exact ne_of_lieson_and_not_lieson e_lieson_ac b_not_lieson_ac -- $E \ne B$ because $E$ lies on line $AC$, but $B$ doesn't lies on line $AC$
lemma d_ne_c : D ≠ C := by -- for $D \ne C$
  have c_not_lieson_ab := (lies_on_line_of_pt_pt_iff_colinear (b_ne_a (hnd := hnd)) C).mp.mt hnd -- $C$ doesn't lies on line $AB$ because $A, B, C$ not colinear
  have d_lieson_ab := Seg_nd.lies_on_toline_of_lies_on_extn (Ray.lies_on_of_lies_int hd) -- $D$ lieson line $AB$ because $D$ lies in the extension of $AB$
  exact ne_of_lieson_and_not_lieson d_lieson_ab c_not_lieson_ab -- $D \ne C$ because $D$ lies on line $AB$, but $C$ doesn't lies on line $AB$
-- Claim: $A \ne D$ and $A \ne E$. This is because $E$ lies on extension of $AC$, but $A$ doesn't lies on extension of $AC$; $D$ lies on extension of $AB$, but $A$ doesn't lies on extension of $AB$
lemma d_ne_a : D ≠ A := by -- for $D \ne A$
  have a_lies_on_ab : A LiesOn (SEG_nd A B (b_ne_a (hnd := hnd))).1 := Seg.source_lies_on
  --have a_lies_on_ab := Seg.source_lies_on (SEG_nd A B (b_ne_a (hnd := hnd))).1 -- $A$ lieson segment $AB$ because $A$ is the source of segment $AB$
  have a_not_lies_int_ab_extn := (Seg_nd.not_lies_int_extn_and_rev_extn_of_lies_on a_lies_on_ab).1 -- $A$ doesn't lies in the extension of $AB$ because $A$ lies on segment $AB$
  exact ne_of_liesint_and_not_liesint hd a_not_lies_int_ab_extn -- $D \ne A$ because $D$ lies in the extension of $AB$, but $A$ doesn't liesint the extension of $AB$
lemma e_ne_a : E ≠ A := by -- for $E \ne A$
  have a_lies_on_ac : A LiesOn (SEG_nd A C (c_ne_a (hnd := hnd))).1 := Seg.source_lies_on  -- $A$ lieson segment $AC$ because $A$ is the source of segment $AC$
  have a_not_lies_int_ac_extn := (Seg_nd.not_lies_int_extn_and_rev_extn_of_lies_on a_lies_on_ac).1 -- $A$ doesn't lies in the extension of $AC$ because $A$ lies on segment $AC$
  exact ne_of_liesint_and_not_liesint he a_not_lies_int_ac_extn -- $E \ne A$ because $E$ lies in the extension of $AC$, but $A$ doesn't liesint the extension of $AC$
-- We have $\angle EBC = \angle BCD$.
variable (hang : ∠ E B C e_ne_b b_ne_c.symm =  ∠ B C D b_ne_c d_ne_c)

-- Prove that $\angle CDA = \angle BEA$
theorem Shan_Problem_1_2 : ∠ C D A (d_ne_c (hnd := hnd) (hd := hd)).symm (d_ne_a (hnd := hnd) (hd := hd)).symm = ∠ B E A (e_ne_b (hnd := hnd) (he := he)).symm (e_ne_a (hnd := hnd) (he := he)).symm := sorry

end Shan_Problem_1_2
