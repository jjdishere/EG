import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type*} [EuclideanPlane Plane]

namespace Wuwowuji_Problem_1_8
/-
$∠ AOC = ∠ COB$, $P$ lies in $OC$, $D, E$ is the perpendicular foot from $P$ to line $OA, OB$, respectively.

Prove that $▵ OPD ≅ₐ ▵ OPE$.
-/

-- Define $A, B, C, O$ on the plane.
variable {A B C O : Plane} {hnd1 : ¬ Collinear O A B} {hnd2 : ¬ Collinear O B C} {hnd3 : ¬ Collinear O C A}
-- nondegenerate
lemma o_ne_a : O ≠ A:= by sorry
lemma o_ne_b : O ≠ B := by sorry
lemma o_ne_c : O ≠ C := by sorry
-- $∠ AOC = ∠ COB$.
variable {hang : ∠ A O C o_ne_a o_ne_b = ∠ C O B o_ne_c o_ne_b}
-- $P$ lies in $OC$.
variable {P : Plane} {hp : P LiesInt (SEG O C)}
-- $D, E$ is the perpendicular foot from $P$ to line $OA, OB$.
variable {D E : Plane} {hd : D = perp_foot P (LIN O A o_ne_a.symm)} {he : E = perp_foot P (LIN O B o_ne_b.symm)}
-- State the main goal.
lemma hnd4 : ¬ Collinear O P D := by sorry
lemma hnd5 : ¬ Collinear O P E := by sorry
theorem Wuwowuji_Problem_1_8 : (TRI_nd O P D hnd4) ≅ₐ (TRI_nd O P E hnd5) := by
  sorry

end Wuwowuji_Problem_1_8
