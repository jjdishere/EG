import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash

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
variable {D : Plane} {D_on_seg : D LiesInt (SEG B C)}
--Let $E$ be point on the segment $BC$
variable {E : Plane} {E_on_seg : E LiesInt (SEG B C)}
--such that $BD = CE$
variable {E_ray_position : (SEG B D).length = (SEG C E).length}
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
$\cdot \angle XBD = - \angle YCE$
$\cdot |\angle BXD| = |\angle CYE|$
$\cdot BD = CE$
Thus, $\triangle XBD \congr_a \triangle YEC$ (by AAS)
Therefore, $DX = EY$.
-/
  have hnd_bdx : ¬ colinear B D X := by sorry
  have hnd_cey : ¬ colinear C E Y := by sorry
  have x_ne_B : X ≠ B := by sorry
  have d_ne_B : D ≠ B := by sorry
  have y_ne_C : Y ≠ C := by sorry
  have e_ne_C : E ≠ C := by sorry
  have A_ne_B : A ≠ B := by sorry
  have c_ne_B : C ≠ B := by sorry
  have A_ne_C : A ≠ C := by sorry
  have trngl_bdx_acongr_trngl_cey : Triangle_nd.IsACongr (TRI_nd B D X hnd_bdx) (TRI_nd C E Y hnd_cey) := by
    have ang_dbx_eq_neg_ang_ecy : ∠ D B X d_ne_B x_ne_B = - ∠ E C Y e_ne_C y_ne_C := by
      calc
      ∠ D B X d_ne_B x_ne_B
      _= ∠ C B A c_ne_B A_ne_B := by sorry
        --apply Angle_trash.eq_ang_of_lieson_lieson
      _= - ∠ B C A c_ne_B.symm A_ne_C := by sorry
      _= - ∠ E C Y e_ne_C y_ne_C := by sorry
    apply Triangle_nd.acongr_of_AAS
    -- the current AAS thm seems like ASA
    · exact ang_dbx_eq_neg_ang_ecy
    · sorry
    · exact E_ray_position
  exact trngl_bdx_acongr_trngl_cey.edge₁
end Problem1_7_
