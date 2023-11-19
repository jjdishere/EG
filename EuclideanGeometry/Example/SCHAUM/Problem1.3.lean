import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Problem1_3_
/-Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
Let $D$ and $E$ be two points on $BC$,such that $BD=CE$

Prove that $∠DAB = ∠CAE$.
-/
--Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : P} {hnd: ¬ colinear A B C} {hisoc: (▵ A B C).IsIsoceles}
--Let $D$ and $E$ be two points on $BC$
variable {D : P} {D_on_seg: D LiesInt (SEG A B)}
variable {E : P} {E_on_seg: E LiesInt (SEG A B)}
--such that $BD = CE$.
variable {D_E_seg_position : (SEG B D).length = (SEG C E).length}
--lemma for existance of angle
--B ≠ A and C ≠ A by hnd
lemma b_ne_a : B ≠ A := (ne_of_not_colinear hnd).2.2
lemma c_ne_a : C ≠ A := (ne_of_not_colinear hnd).2.1.symm
--D ≠ A and E ≠ A
lemma d_ne_a : D ≠ A := sorry
lemma e_ne_a : E ≠ A := sorry
--Prove that $DM = EM$.
theorem Problem1_3_ : ∠ D A B (d_ne_a) (b_ne_a (hnd := hnd))= ∠ C A E (c_ne_a (hnd := hnd)) (e_ne_a) := sorry

end Problem1_3_
