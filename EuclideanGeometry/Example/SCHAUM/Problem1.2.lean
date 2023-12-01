import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace Problem1_2_
/-Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.Let $D$ be a point on $AB$.
Let $E$ be a point on $AC$ such that $AE = AD$.Let $P$ be the foot of perpendicular from $D$ to $BC$.
Let $Q$ be the foot of perpendicular from $E$ to $BC$.

Prove that $DP = EQ$.
-/

--Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : Plane} {hnd: ¬ colinear A B C} {hisoc: (▵ A B C).IsIsoceles}
--Let $D$ be a point on $AB$.
variable {D : Plane} {D_int_AB : D LiesInt (SEG A B)}
--Let $E$ be a point on $AC$
variable {E : Plane} {E_int_AC : E LiesInt (SEG A C)}
--such that $AE = AD$.
variable {AE_eq_AD : (SEG A E).length = (SEG A D).length}
-- Claim:$B \ne C$.
lemma B_ne_C : B ≠ C :=
  -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
  (ne_of_not_colinear hnd).1.symm
-- Let $P$ be the foot of perpendicular from $D$ to $BC$.
variable {P : Plane} {hd : P = perp_foot D (LIN B C B_ne_C.symm)}
-- Let $Q$ be the foot of perpendicular from $E$ to $BC$.
variable {Q : Plane} {hd : Q = perp_foot E (LIN B C B_ne_C.symm)}
-- Prove that $DP = EQ$.
theorem Problem1_2_ : (SEG D P).length = (SEG E Q).length := by
/-
In the isoceles triangle $ABC$, we have $AB = AC$.
Thus we have $BD = AB - AD = AC - AE = CE$.
The angle $DBP$ is the same as angle $ABC$, the angle $ECQ$ is the same as angle $ACB$.
In the isoceles triangle $ABC$, we have $\angle ABC = - \angle ACB$.
Therefore, $\angle DBP = \angle ABC = - \angle ACB = - \angle ECQ$.
Since $DP$ is perpendicular to $BC$ at $P$, we have $\angle BPD = \pi/2$ or $\angle BPD = - \pi/2$.
Since $EQ$ is perpendicular to $BC$ at $Q$, we have $\angle CQE = \pi/2$ or $\angle CQE = - \pi/2$.
Thus, $|\angle BPD| = |\angle CQE|$
In $\triangle PBD$ and $\triangle QEC$,
$\cdot \angle DBP = - \angle ECQ$
$\cdot |\angle BPD| = |\angle CQE|$
$\cdot BD = CE$
Thus, $\triangle PBD \congr_a \triangle QEC$ (by AAS)
Therefore, $DP = EQ$.
-/
  --In the isoceles triangle $ABC$, we have $AB = AC$.
  have hisoc' : (SEG A B).length = (SEG A C).length := by
    calc
      -- $AB = CA$ by isoceles,
      _ = (SEG C A).length := hisoc.symm
      -- $CA = AC$ by symmetry.
      _ = (SEG A C).length := length_eq_length_of_rev (SEG C A)
  --Thus we have $BD = AB - AD = AC - AE = CE$.
  have seg1 : (SEG B D).length = (SEG C E).length := by
    calc
      -- $BD = DB$ by symmetry,
      _ = (SEG D B).length := by sorry
      -- $DB = AB - AD$ since $D$ lies on $AB$,
      _ = (SEG A B).length - (SEG A D).length := by
        rw [← eq_sub_of_add_eq']
        exact (length_eq_length_add_length (SEG A B) D (D_on_seg)).symm
      -- $AB - AD = AC - AE$ since $AB = AC$ and $AD = AE$,
      _ = (SEG A C).length - (SEG A E).length := by rw [E_ray_position, ← hisoc']
      -- $AC - AE = EC$ since $E$ lies on $AC$,
      _ = (SEG E C).length := by
        rw [← eq_sub_of_add_eq']
        exact (length_eq_length_add_length (SEG A C) E (E_on_seg)).symm
      -- $EC = CE$ by symmetry.
      _ = (SEG C E).length := length_eq_length_of_rev (SEG E C)
  -- we have $A \ne B$.
  have A_ne_B : A ≠ B := (ne_of_not_colinear hnd).2.2.symm
  -- we have $A \ne C$.
  have A_ne_C : A ≠ C := (ne_of_not_colinear hnd).2.1
  -- we have $C \ne B$.
  have c_ne_B : C ≠ B := (ne_of_not_colinear hnd).1
  -- we have $\triangle P B D$ is nondegenerate
  have hnd1 : ¬ colinear P B D := by sorry
  -- we have $B \ne D$.
  have B_ne_d : B ≠ D := (ne_of_not_colinear hnd1).1.symm
  -- we have $P \ne D$.
  have p_ne_d : P ≠ D := (ne_of_not_colinear hnd1).2.1
  -- we have $P \ne B$.
  have p_ne_B : P ≠ B := (ne_of_not_colinear hnd1).2.2.symm
  -- we have $\triangle Q C E$ is nondegenerate
  have hnd2 : ¬ colinear Q C E := by sorry
  -- we have $C \ne E$.
  have c_ne_e : C ≠ E := (ne_of_not_colinear hnd2).1.symm
  -- we have $Q \ne E$.
  have q_ne_e : Q ≠ E := (ne_of_not_colinear hnd2).2.1
  -- we have $Q \ne C$.
  have q_ne_C : Q ≠ C := (ne_of_not_colinear hnd2).2.2.symm
  --$\angle DBP = - \angle ECQ$.
  have ang2 : (∠ D B P B_ne_d.symm p_ne_B) = - (∠ E C Q c_ne_e.symm q_ne_C) := by
    calc
      -- The angle $DBP$ is the same as angle $ABC$,
      _ = ∠ A B C A_ne_B c_ne_B := by sorry
      -- In the isoceles triangle $ABC$, we have $\angle ABC = \angle BCA$,
      _ = ∠ B C A c_ne_B.symm A_ne_C := by sorry
      -- $\angle BCA = - \angle A C B$ by symmetry,
      _ = - ∠ A C B A_ne_C c_ne_B.symm := by sorry
      -- the angle $ECQ$ is the same as angle $ACB$.
      _ = - ∠ E C Q c_ne_e.symm q_ne_C := by sorry
  have ang1 : (∠ B P D p_ne_B.symm p_ne_d.symm) = - (∠ C Q E q_ne_C.symm q_ne_e.symm) := by sorry
  -- $|\angle BPD| = |\angle CQE|$
  have h : Triangle_nd.IsACongr (TRI_nd P B D hnd1) (TRI_nd Q C E hnd2) := by
    apply Triangle_nd.acongr_of_AAS
    · exact ang1
    · exact ang2
    · exact seg1
  exact h.edge₂

end Problem1_2_
