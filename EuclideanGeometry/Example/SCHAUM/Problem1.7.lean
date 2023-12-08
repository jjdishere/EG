import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence_trash

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace Problem1_7_
/-Let $\triangle ABC$ be an isoceles triangle in which $AB = AC$.
Let $D$ and $E$ be points on the segment $BC$ such that $BD = CE$.

Prove that the height of $D$ to $AB$ is the same as the height of $E$ to $AC$.
-/
--Let $\triangle ABC$ be an isoceles triangle in which $AB = AC$
variable {A B C : Plane} {hnd : ¬ colinear A B C} {hisoc : (▵ A B C).IsIsoceles}
--Let $D$ be point on the segment $BC$
variable {D : Plane} {D_int_BC : D LiesInt (SEG B C)}
--Let $E$ be point on the segment $BC$
variable {E : Plane} {E_int_BC : E LiesInt (SEG B C)}
--such that $BD = CE$
variable {BD_eq_CE : (SEG B D).length = (SEG C E).length}
--Claim $B \ne A$
lemma B_ne_a : B ≠ A := (ne_of_not_colinear hnd).2.2
--Claim $C \ne A$
lemma c_ne_a : C ≠ A := (ne_of_not_colinear hnd).2.1.symm
--Prove that the height of $D$ to $AB$ is the same as the height of $E$ to $AC$
--take the foot of the height of $D$ to $AB$ and denote as $X$
variable {X : Plane} {hd : X = perp_foot D (LIN A B B_ne_a)}
--take the foot of the height of $E$ to $AB$ and denote as $Y$
variable {Y : Plane} {he : Y = perp_foot E (LIN A C c_ne_a)}
theorem Problem1_7_ : (SEG D X).length = (SEG E Y).length := by
/-
In isoceles triangle $ABC$, we have $\angle ABC$ and $\angle ACB$ are acute.
From $D$ lies on $BC$ and $\angle ABC$ is acute, we know that $X$ lies on ray $BA$, so $\angle XBD$ is the same as $\angle ABC$.
From $E$ lies on $BC$ and $\angle ACB$ is acute, we know that $Y$ lies on ray $CA$, so $\angle YCE$ is the same as $\angle ACB$.
In isoceles triangle $ABC$, we have $\angle ABC = - \angle ACB$.
So $\angle XBD = \angle ABC = - \angle ACB = - \angle YCE$.
Since $DX$ is perpendicular to $AB$ at $X$, we have $\angle BXD = \pi/2$ or $\angle BXD = - \pi/2$.
Since $EY$ is perpendicular to $AC$ at $Y$, we have $\angle CYE = \pi/2$ or $\angle CYE = - \pi/2$.
Thus, $|\angle BXD| = |\angle CYE|$.
In $\triangle XBD$ and $\triangle YCE$,
$\cdot |\angle BXD| = |\angle CYE|$
$\cdot \angle DBX = - \angle ECY$
$\cdot BD = CE$
Thus, $\triangle XBD \cong_a \triangle YEC$ (by AAS)
Therefore, $DX = EY$.
-/
  have not_colinear_XBD : ¬ colinear X B D := by sorry
  have not_colinear_YCE : ¬ colinear Y C E := by sorry
  -- We have that $X, B, D$ are pairwise distinct.
  have X_ne_B : X ≠ B := by sorry
  have D_ne_X : D ≠ X := by sorry
  have D_ne_B : D ≠ B := by sorry
  -- We have that $Y, C, E$ are pairwise distinct.
  have Y_ne_C : Y ≠ C := by sorry
  have E_ne_Y : E ≠ Y := by sorry
  have E_ne_C : E ≠ C := by sorry
  -- We have that $A, B, C$ are pairwise distinct.
  have A_ne_B : A ≠ B := by sorry
  have C_ne_B : C ≠ B := by sorry
  have A_ne_C : A ≠ C := by sorry
  have trngl_XBD_acongr_trngl_YCE : (TRI_nd X B D not_colinear_XBD) ≅ₐ (TRI_nd Y C E not_colinear_YCE) := by
    have angle_BXD_eq_neg_angle_CYE : ∠ B X D X_ne_B.symm D_ne_X = - ∠ C Y E Y_ne_C.symm E_ne_Y := by sorry
    have angle_DBX_eq_neg_angle_ECY : ∠ D B X D_ne_B X_ne_B = - ∠ E C Y E_ne_C Y_ne_C := by
      calc
      ∠ D B X D_ne_B X_ne_B
      _= ∠ C B A C_ne_B A_ne_B := by sorry
        --apply Angle_trash.eq_ang_of_lieson_lieson
      _= - ∠ B C A C_ne_B.symm A_ne_C := by sorry
      _= - ∠ E C Y E_ne_C Y_ne_C := by sorry
    apply cong_trash.acongr_of_AAS
    · exact angle_BXD_eq_neg_angle_CYE
    · exact angle_DBX_eq_neg_angle_ECY
    · exact BD_eq_CE
  exact trngl_XBD_acongr_trngl_YCE.edge₂
end Problem1_7_
