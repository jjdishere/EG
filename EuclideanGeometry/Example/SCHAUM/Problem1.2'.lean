import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

namespace Schaum
namespace Problem1_2
/-
Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.Let $D$ be a point on $AB$.
Let $E$ be a point on $AC$ such that $AE = AD$.Let $P$ be the foot of perpendicular from $D$ to $BC$.
Let $Q$ be the foot of perpendicular from $E$ to $BC$.

Prove that $DP = EQ$.
-/

structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  -- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
  A : Plane
  B : Plane
  C : Plane
  not_colinear_ABC : ¬ colinear A B C
  hisoc : (▵ A B C).IsIsoceles
  --Let $D$ be a point on $AB$.
  D : Plane
  D_int_AB : D LiesInt (SEG A B)
  --Let $E$ be a point on $AC$,
  E : Plane
  E_int_AC: E LiesInt (SEG A C)
  -- such that $AE = AD$.
  AE_eq_AD : (SEG A E).length = (SEG A D).length
  -- Claim: $B \ne C$.
  B_ne_C : B ≠ C :=
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_colinear not_colinear_ABC).1.symm
  -- Let $P$ be the foot of perpendicular from $D$ to $BC$.
  P : Plane
  hP : P = perp_foot D (LIN B C B_ne_C.symm)
  -- Let $Q$ be the foot of perpendicular from $E$ to $BC$.
  Q : Plane
  hQ : Q = perp_foot E (LIN B C B_ne_C.symm)

/- # Another Style of Setting-/
structure Setting1 (Plane : Type _) [EuclideanPlane Plane] where
  -- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
  A : Plane
  B : Plane
  C : Plane
  not_colinear_ABC : ¬ colinear A B C
  hisoc : (▵ A B C).IsIsoceles
  --Let $D$ be a point on $AB$.
  D : Plane
  D_int_AB : D LiesInt (SEG A B)
  --Let $E$ be a point on $AC$,
  E : Plane
  E_int_AC: E LiesInt (SEG A C)
  -- such that $AE = AD$.
  AE_eq_AD : (SEG A E).length = (SEG A D).length

-- Claim: $B \ne C$.
lemma B_ne_C {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane}: e.B ≠ e.C := by
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
  exact (ne_of_not_colinear e.not_colinear_ABC).1.symm

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends Setting1 Plane where
  B_ne_C : B ≠ C := B_ne_C
  -- Let $P$ be the foot of perpendicular from $D$ to $BC$.
  P : Plane
  hP : P = perp_foot D (LIN B C B_ne_C.symm)
  -- Let $Q$ be the foot of perpendicular from $E$ to $BC$.
  Q : Plane
  hQ : Q = perp_foot E (LIN B C B_ne_C.symm)

-- Prove that $DP = EQ$.
theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : (SEG e.D e.P).length = (SEG e.E e.Q).length := by
/-
  In the isoceles triangle $ABC$, we have $AB = AC$.
  Thus we have $BD = AB - AD = AC - AE = CE$.
  In the isoceles triangle $ABC$, we have $\angle ABC = - \angle ACB$.
  Therefore, $\angle DBP = \angle ABC = -\angle ACB = - \angle ECQ$.
  Since $DP$ is perpendicular to $BC$ at $P$, we have $\angle DPB = \pi/2$ or $ - \pi/2$.
  Since $EQ$ is perpendicular to $BC$ at $Q$, we have $\angle EQC = \pi/2$ or $ - \pi/2$.
  Thus $\angle DPB = - \angle EQC \mod \pi$.
  In $\triangle DBP$ and $\triangle EQC$,
  $\bullet \qquad \angle DBP = - \angle ECQ$
  $\bullet \qquad \angle DPB = - \angle EQC \mod \pi$
  $\bullet \qquad BD = CE$
  Thus $\triangle DPB \congr_a \triangle EQC$ (by AAS).
  Therefore, $DP = EQ$.
-/
  -- In the isoceles triangle $ABC$, we have $AB = AC$.
  have hisoc' : (SEG e.A e.B).length = (SEG e.A e.C).length := by
    calc
      -- $AB = CA$ by isoceles,
      _ = (SEG e.C e.A).length := e.hisoc.symm
      -- $CA = AC$ by symmetry.
      _ = (SEG e.A e.C).length := (SEG e.A e.C).length_of_rev_eq_length
  -- Thus we have $BD = AB - AD = AC - AE = CE$.
  have seg1 : (SEG e.B e.D).length = (SEG e.C e.E).length := by
    calc
      -- $BD = DB$ by symmetry,
      _ = (SEG e.D e.B).length := by sorry
      -- $DB = AB - AD$ since $D$ lies on $AB$,
      _ = (SEG e.A e.B).length - (SEG e.A e.D).length := by
        rw [← eq_sub_of_add_eq']
        exact sorry -- (length_eq_length_add_length (SEG A B) D (D_on_seg)).symm
      -- $AB - AD = AC - AE$ since $AB = AC$ and $AD = AE$,
      _ = (SEG e.A e.C).length - (SEG e.A e.E).length := by sorry -- rw [E_ray_position, ← hisoc']
      -- $AC - AE = EC$ since $E$ lies on $AC$.
      _ = (SEG e.E e.C).length := by
        rw [← eq_sub_of_add_eq']
        exact sorry --(length_eq_length_add_length (SEG A C) E (E_on_seg)).symm
      _ = (SEG e.C e.E).length := sorry -- length_eq_length_of_rev (SEG E C)
  -- We have $A \ne B$.
  have A_ne_B : e.A ≠ e.B := (ne_of_not_colinear e.not_colinear_ABC).2.2.symm
  -- We have $A \ne C$.
  have A_ne_C : e.A ≠ e.C := (ne_of_not_colinear e.not_colinear_ABC).2.1
  -- We have $C \ne B$.
  have C_ne_B : e.C ≠ e.B := (ne_of_not_colinear e.not_colinear_ABC).1
  -- We have $\triangle PBD$ is nondegenerate
  have not_colinear_PBD : ¬ colinear e.P e.B e.D := by sorry
  -- We have $B \ne D$.
  have B_ne_D : e.B ≠ e.D := (ne_of_not_colinear not_colinear_PBD).1.symm
  -- We have $P \ne D$.
  have P_ne_D : e.P ≠ e.D := (ne_of_not_colinear not_colinear_PBD).2.1
  -- We have $P \ne B$.
  have P_ne_B : e.P ≠ e.B := (ne_of_not_colinear not_colinear_PBD).2.2.symm
  -- We have $\triangle QCE$ is nondegenerate
  have not_colinear_QCE : ¬ colinear e.Q e.C e.E := by sorry
  -- We have $C \ne E$.
  have C_ne_E : e.C ≠ e.E := (ne_of_not_colinear not_colinear_QCE).1.symm
  -- We have $Q \ne E$.
  have Q_ne_E : e.Q ≠ e.E := (ne_of_not_colinear not_colinear_QCE).2.1
  -- We have $Q \ne C$.
  have Q_ne_C : e.Q ≠ e.C := (ne_of_not_colinear not_colinear_QCE).2.2.symm
  -- Therefore, $\angle DBP = \angle ABC = -\angle ACB = - \angle ECQ$.
  have ang2 : (∠ e.D e.B e.P B_ne_D.symm P_ne_B) = - (∠ e.E e.C e.Q C_ne_E.symm Q_ne_C) := by
    calc
      -- the angle $DBP$ is the same as angle $ABC$,
      _ = ∠ e.A e.B e.C A_ne_B C_ne_B := by sorry
      -- in the isoceles triangle $ABC$, we have $\angle ABC = \angle BCA$,
      _ = ∠ e.B e.C e.A C_ne_B.symm A_ne_C := by sorry
      -- $\angle BCA = - \angle ACB$ by symmetry,
      _ = - ∠ e.A e.C e.B A_ne_C C_ne_B.symm := by sorry
      -- the angle $ECQ$ is the same as angle $ACB$.
      _ = - ∠ e.E e.C e.Q C_ne_E.symm Q_ne_C := by sorry
  -- $|\angle DPB| = |\angle EQC|$.
  have ang1 : (∠ e.B e.P e.D P_ne_B.symm P_ne_D.symm) = - (∠ e.C e.Q e.E Q_ne_C.symm Q_ne_E.symm) := by sorry
  -- $\triangle DPB \congr_a \triangle EQC$ (by AAS).
  have h : (TRI_nd e.P e.B e.D not_colinear_PBD) ≅ₐ (TRI_nd e.Q e.C e.E not_colinear_QCE) := by
    apply TriangleND.acongr_of_AAS
    -- $\cdot \angle DBP = - \angle ECQ$
    · exact ang1
    -- $\cdot |\angle DPB| = |\angle EQC|$
    · exact ang2
    -- $\cdot BD = CE$
    · sorry --exact seg1
  -- Therefore, $DP = EQ$.
  exact h.edge₂

end Problem1_2
end Schaum
end EuclidGeom
