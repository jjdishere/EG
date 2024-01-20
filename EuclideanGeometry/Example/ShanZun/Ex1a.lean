import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

namespace Shan_Problem_1_3
/- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
 Let $D$ be a point in the extension of $AB$ such that $BD = AB$. Let $E$ be the midpoint of $AB$.
Prove that $CD = 2 \cdot CE$. -/

-- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : P} {hnd : ¬ Collinear A B C} {isoceles_ABC : (▵ A B C).IsIsoceles}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma A_ne_B : A ≠ B := sorry
lemma B_ne_C : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- $D$ is a point in the extension of $AB$
variable {D : P} {hd_1 : D LiesInt (SEG_nd A B A_ne_B).extension}
-- We have $BD=AB$
{hd_2 : (SEG B D).length = (SEG A B).length}
-- $E$ is the midpoint of $AB$
variable {E : P} {he : E = (SEG A B).midpoint}

-- Theorem : $CD = 2 \cdot CE$
theorem Shan_Problem_1_3 : (SEG C D).length = 2 * (SEG C E).length := by
  -- Extend $AC$ to $F$ such that $CF = AC$
  let F := Ray.extpoint (SEG_nd A C c_ne_a).extension (SEG A C).length
  have cf_eq_ac : (SEG C F).length = (SEG A C).length :=
    (SEG_nd A C c_ne_a).extension.dist_of_extpoint (SEG A C).length_nonneg
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
variable {A B C : P} {hnd : ¬ Collinear A B C}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma A_ne_B : A ≠ B := sorry
lemma B_ne_C : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- We have $\angle BCA = 2 \cdot \angle CBA$
variable {hang : ∠ B C A B_ne_C c_ne_a.symm = 2 • ∠ C B A B_ne_C.symm A_ne_B}
-- $AD$ is the height of $\triangle ABC$
variable {D : P} {hd : D = perp_foot A (LIN B C B_ne_C.symm)}

-- Theorem : $BD = AC + CD$
theorem Shan_Problem_1_4 : (SEG B D).length = (SEG A C).length + (SEG C D).length := by
  -- Extend $BC$ to $E$ such that $CE = CA$
  let E := Ray.extpoint (SEG_nd B C B_ne_C.symm).extension (SEG C A).length
  have ce_eq_ca : (SEG C E).length = (SEG C A).length :=
    (SEG_nd B C B_ne_C.symm).extension.dist_of_extpoint (SEG C A).length_nonneg
  -- $DE = AC + CD$
  have de_eq_ac_plus_cd : (SEG D E).length = (SEG A C).length + (SEG C D).length := sorry
  -- $C A E$ is not collinear
  have cae_not_collinear : ¬ Collinear C A E := sorry
  -- $\triangle CAE$ is isoceles
  have isoceles₁ : (TRI_nd C A E cae_not_collinear).1.IsIsoceles := by
    rw[← Seg.length_of_rev_eq_length (seg := (SEG C E))] at ce_eq_ca
    exact ce_eq_ca
  -- Claim: $E \ne A$ and $C \ne E$
  have e_ne_a : E ≠ A := sorry
  have c_ne_e : C ≠ E := sorry
  -- $\angle EAC = \angle CEA$
  have ang₁ : ∠ E A C e_ne_a c_ne_a = ∠ C E A c_ne_a e_ne_a.symm := (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := TRI_nd C A E cae_not_collinear)).mp isoceles₁
  -- $\angle ACB = 2 \angle CEA$
  have ang₂ : ∠ A C E c_ne_a.symm c_ne_e.symm = 2 • ∠ C E A c_ne_e e_ne_a.symm := sorry
  -- Claim: $E \ne B$
  have e_ne_b : E ≠ B := sorry
  -- $\angle EBA = \angle AEB$
  have ang₃ : ∠ E B A e_ne_b A_ne_B = ∠ A E B e_ne_a.symm e_ne_b.symm := sorry
  -- $ABE$ is not collinear
  have abe_not_collinear : ¬ Collinear A B E := sorry
  -- $\triangle ABE$ is isoceles
  have isoceles₂ : (TRI_nd A B E abe_not_collinear).1.IsIsoceles := by
    apply is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mpr
    exact ang₃
  -- $BD = DE$
  have bd_eq_de : (SEG B D).length = (SEG D E).length := sorry
  -- 此处需要等腰三角形三线合一的定理
  rw[← de_eq_ac_plus_cd]
  exact bd_eq_de
end Shan_Problem_1_4
