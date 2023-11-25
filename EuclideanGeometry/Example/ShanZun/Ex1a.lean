import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Shan_Problem_1_3
/- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
 Let $D$ be a point in the extension of $AB$ such that $BD = AB$. Let $E$ be the midpoint of $AB$.
Prove that $CD = 2 \cdot CE$. -/

-- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : P} {hnd : ¬ colinear A B C} {hisoc : (▵ A B C).IsIsoceles}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- $D$ is a point in the extension of $AB$
variable {D : P} {hd_1 : D LiesInt (SEG_nd A B a_ne_b).extension}
-- We have $BD=AB$
{hd_2 : (SEG B D).length = (SEG A B).length}
-- $E$ is the midpoint of $AB$
variable {E : P} {he : E = (SEG A B).midpoint}

-- Theorem : $CD = 2 \cdot CE$
theorem Shan_Problem_1_3 : (SEG C D).length = 2 * (SEG C E).length := by
  -- Extend $AC$ to $F$ such that $CF = AC$
  let F := Ray.extpoint (SEG_nd A C c_ne_a).extension (SEG A C).length
  have cf_eq_ac : (SEG C F).length = (SEG A C).length := by
    apply seg_length_eq_dist_of_extpoint (SEG_nd A C c_ne_a).extension
    simp
  -- $\triangle A B F$ is congruent to $\triangle A C D$, so $BF = CD$
  have iso : (▵ A B F) ≅ₐ (▵ A C D) := sorry
  have bf_eq_cd : (SEG B F).length = (SEG C D).length := iso.edge₁
  -- $2 CE = BF$
  -- 以后这里可能需要增加中位线的定理
  have two_ce_eq_bf : 2 * (SEG C E).length = (SEG B F).length := sorry
  rw[two_ce_eq_bf, bf_eq_cd]
end Shan_Problem_1_3

namespace Shan_Problem_1_4
/- Let $\triangle ABC$ be a triangle in which $\angle BCA = 2 \cdot \angle CBA$. Let $AD$ be the height of $\triangle ABC$ over $BC$.

Prove that $BD = AC + CD$.-/

-- We have triangle $\triangle ABC$
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma a_ne_b : A ≠ B := sorry
lemma b_ne_c : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- We have $\angle BCA = 2 \cdot \angle CBA$
variable {hang : ∠ B C A b_ne_c c_ne_a.symm = 2 * ∠ C B A b_ne_c.symm a_ne_b}
-- $AD$ is the height of $\triangle ABC$
variable {D : P} {hd : D = perp_foot A (LIN B C b_ne_c.symm)}

-- Theorem : $BD = AC + CD$
theorem Shan_Problem_1_4 : (SEG B D).length = (SEG A C).length + (SEG C D).length := sorry

end Shan_Problem_1_4
