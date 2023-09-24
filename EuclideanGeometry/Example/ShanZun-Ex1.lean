import EuclideanGeometry.Foundation.Index

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
/- Let $\triangle ABC$ be a nondegenerate isosceles triangle in which $AB = AC$. Let $D$ be a point on the extension of $AB$ and $E$ a point on the extension of $AC$, such that $\angle EBC = \angle BCD$.

Prove that $\angle CDA = \angle BEA$. -/
variable {A B C : P} {hnd : ¬ colinear A B C} {hisoc : (▵ A B C).IsIsoceles}
-- Claim: $A \ne B$ and $A \ne C$ and $B \ne C$. This is because vertices of nondegenerate triangles are distinct.
lemma a_ne_b : A ≠ B := (ne_of_not_colinear hnd).2.2.symm
lemma a_ne_c : A ≠ C := (ne_of_not_colinear hnd).2.1
lemma b_ne_c : B ≠ C := (ne_of_not_colinear hnd).1.symm
-- Let $D$ and $e$ be points on the extension of the nondegenerate segments of $AB$ and $AC$, respectively.
variable {D E : P} {hd : Ray.IsInt D (SEG_nd A B a_ne_b).extension} {he : Ray.IsInt E (SEG_nd A C a_ne_c).extension}
-- Claim: $E \ne B$ and $D \ne C$. This is because 
--lemma extn.source_eq_target : {seg_nd : Seg_nd P} seg_nd.1.target := sorry
--lemma e_ne_b : E ≠ B := by


-- We have $\angle EBC = \angle BCD$.
--variable {hang : }
end Shan_Problem_1_2