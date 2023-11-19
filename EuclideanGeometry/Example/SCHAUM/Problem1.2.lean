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
variable {E : Plane} {E_on_seg: E LiesInt (SEG A B)}
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
theorem Problem1_2_ : (SEG D P).length = (SEG E Q).length := by sorry

end Problem1_2_
