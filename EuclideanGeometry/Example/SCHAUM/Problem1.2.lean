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
variable {D : Plane} {D_on_seg: D LiesInt (SEG A B)}
--Let $E$ be a point on $AC$
variable {E : Plane} {E_on_seg: E LiesInt (SEG A C)}
--such that $AE = AD$.
variable {E_ray_position : (SEG A E).length = (SEG A D).length}
-- Claim:$B \ne C$.
-- This is because vertices  B C of nondegenerate triangles are distinct.
lemma b_ne_c : B ≠ C := (ne_of_not_colinear hnd).1.symm
-- Let $P$ be the foot of perpendicular from $D$ to $BC$.
variable {P : Plane} {hd : P = perp_foot D (LIN B C b_ne_c.symm)}
-- Let $Q$ be the foot of perpendicular from $E$ to $BC$.
variable {Q : Plane} {hd : Q = perp_foot E (LIN B C b_ne_c.symm)}
-- Prove that $DP = EQ$.
theorem Problem1_2_ : (SEG D P).length = (SEG E Q).length := by
  have hisoc' : (SEG A B).length = (SEG A C).length := by
    calc
      _ = (SEG C A).length := hisoc.symm
      _ = (SEG A C).length := length_eq_length_of_rev (SEG C A)
  have seg1 : (SEG B D).length = (SEG C E).length := by
    calc
      _ = (SEG D B).length := by sorry
      _ = (SEG A B).length - (SEG A D).length := by
        rw [← eq_sub_of_add_eq']
        exact (length_eq_length_add_length (SEG A B) D (D_on_seg)).symm
      _ = (SEG A C).length - (SEG A E).length := by rw [E_ray_position, ← hisoc']
      _ = (SEG E C).length := by
        rw [← eq_sub_of_add_eq']
        exact (length_eq_length_add_length (SEG A C) E (E_on_seg)).symm
      _ = (SEG C E).length := length_eq_length_of_rev (SEG E C)
  have a_ne_b : A ≠ B := (ne_of_not_colinear hnd).2.2.symm
  have a_ne_c : A ≠ C := (ne_of_not_colinear hnd).2.1
  have c_ne_b : C ≠ B := (ne_of_not_colinear hnd).1
  have hnd1 : ¬ colinear P B D := by sorry
  have b_ne_d : B ≠ D := (ne_of_not_colinear hnd1).1.symm
  have p_ne_d : P ≠ D := (ne_of_not_colinear hnd1).2.1
  have p_ne_b : P ≠ B := (ne_of_not_colinear hnd1).2.2.symm
  have hnd2 : ¬ colinear Q C E := by sorry
  have c_ne_e : C ≠ E := (ne_of_not_colinear hnd2).1.symm
  have q_ne_e : Q ≠ E := (ne_of_not_colinear hnd2).2.1
  have q_ne_c : Q ≠ C := (ne_of_not_colinear hnd2).2.2.symm
  have ang2 : (∠ D B P b_ne_d.symm p_ne_b) = - (∠ E C Q c_ne_e.symm q_ne_c) := by
    calc
      _ = ∠ A B C a_ne_b c_ne_b := by sorry
      _ = ∠ B C A c_ne_b.symm a_ne_c := by sorry
      _ = - ∠ A C B a_ne_c c_ne_b.symm := by sorry
      _ = - ∠ E C Q c_ne_e.symm q_ne_c := by sorry
  have ang1 : (∠ B P D p_ne_b.symm p_ne_d.symm) = - (∠ C Q E q_ne_c.symm q_ne_e.symm) := by sorry
  have h : IsACongr (TRI_nd P B D hnd1).1 (TRI_nd Q C E hnd2).1 := by
    apply acongr_of_AAS
    · exact ang1
    · exact ang2
    · exact seg1
  exact h.edge₂
end Problem1_2_
