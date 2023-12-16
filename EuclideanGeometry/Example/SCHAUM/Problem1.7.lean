import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Line_trash
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex_trash
-- import EuclideanGeometry.Foundation.Axiom.Triangle.Basic

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace Problem1_7_
/-Let $\triangle ABC$ be an isoceles triangle in which $AB = AC$.
Let $D$ and $E$ be points on the segment $BC$ such that $BD = CE$.

Prove that the height of $D$ to $AB$ is the same as the height of $E$ to $AC$.
-/
--Let $\triangle ABC$ be an isoceles triangle in which $AB = AC$
variable {A B C : Plane} {not_colinear_ABC : ¬ colinear A B C} {isoceles_ABC : (▵ A B C).IsIsoceles}
--Let $D$ be point on the segment $BC$
variable {D : Plane} {D_int_BC : D LiesInt (SEG B C)}
--Let $E$ be point on the segment $BC$
variable {E : Plane} {E_int_BC : E LiesInt (SEG B C)}
--such that $BD = CE$
variable {BD_eq_CE : (SEG B D).length = (SEG C E).length}
--Claim $B \ne A$
lemma B_ne_A : B ≠ A := (ne_of_not_colinear not_colinear_ABC).2.2
--Claim $C \ne A$
lemma C_ne_A : C ≠ A := (ne_of_not_colinear not_colinear_ABC).2.1.symm
--Prove that the height of $D$ to $AB$ is the same as the height of $E$ to $AC$
--take the foot of the height of $D$ to $AB$ and denote as $X$
variable {X : Plane} {hd : X = perp_foot D (LIN A B (B_ne_A (not_colinear_ABC := not_colinear_ABC)))}
--take the foot of the height of $E$ to $AB$ and denote as $Y$
variable {Y : Plane} {he : Y = perp_foot E (LIN A C (C_ne_A (not_colinear_ABC := not_colinear_ABC)))}
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
  have angle_CBA_eq_neg_angle_BCA : ∠ C B A C_ne_B A_ne_B = - ∠ B C A C_ne_B.symm A_ne_C := by
    calc
    ∠ C B A C_ne_B A_ne_B
    _= ∠ A C B A_ne_C C_ne_B.symm := is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := (TRI_nd A B C not_colinear_ABC)).mp isoceles_ABC
    _= - ∠ B C A C_ne_B.symm A_ne_C := neg_value_of_rev_ang A_ne_C C_ne_B.symm
  have angle_DBX_eq_angle_CBA : (∠ D B X D_ne_B X_ne_B) = (∠ C B A C_ne_B A_ne_B) := by
    symm;
    have D_int_ray_BC : D LiesInt (RAY B C C_ne_B) := by
      apply SegND.lies_int_toRay_of_lies_int (seg_nd := (SEG_nd B C C_ne_B))
      exact lies_int_seg_nd_of_lies_int_seg B C D C_ne_B D_int_BC
    have X_int_ray_BA : X LiesInt (RAY B A A_ne_B) := by
      simp only [hd]
      simp only [Line.line_of_pt_pt_eq_rev A_ne_B.symm]
      have angle_ABD_acute :  Angle.IsAcuteAngle (ANG A B D A_ne_B D_ne_B) := by
        have angle_ABD_is_angle_ABC : (ANG A B D A_ne_B D_ne_B) = (ANG A B C A_ne_B C_ne_B) := by
          symm;
          apply eq_ang_of_lies_int_liesint A_ne_B C_ne_B A_ne_B D_ne_B
          · exact Ray.snd_pt_lies_int_mk_pt_pt B A A_ne_B
          · exact D_int_ray_BC
        rw [angle_ABD_is_angle_ABC]
        exact ang_acute_of_is_isoceles' not_colinear_ABC isoceles_ABC
      exact perp_foot_lies_int_ray_of_acute_ang A_ne_B D_ne_B angle_ABD_acute
    exact eq_ang_val_of_lieson_lieson C_ne_B A_ne_B D_ne_B X_ne_B D_int_ray_BC X_int_ray_BA
  have angle_BXD_eq_neg_angle_CYE : (∠ B X D X_ne_B.symm D_ne_X) = - ∠ C Y E Y_ne_C.symm E_ne_Y := by
    have BX_perp_XD : (LIN B X X_ne_B) ⟂ (LIN X D D_ne_X) := by sorry
    have CY_perp_YE : (LIN C Y Y_ne_C) ⟂ (LIN Y E E_ne_Y) := by sorry
    have angle_BXD_eq_pi_div_two_or_neg_pi_div_two : (∠ B X D X_ne_B.symm D_ne_X = ↑ (π / 2)) ∨ (∠ B X D X_ne_B.symm D_ne_X = ↑ (- π / 2)) := by sorry
    have angle_CYE_eq_pi_div_two_or_neg_pi_div_two : (∠ C Y E Y_ne_C.symm E_ne_Y = ↑ (π / 2)) ∨ (∠ C Y E Y_ne_C.symm E_ne_Y = ↑ (- π / 2)) := by sorry
    rcases angle_BXD_eq_pi_div_two_or_neg_pi_div_two with h1 | h2
    · have angle_BXD_is_pos : (∠ B X D X_ne_B.symm D_ne_X).IsPos := by
        simp only [h1]
        sorry
      have triangle_XBD_is_cclock : (TRI_nd X B D not_colinear_XBD).is_cclock := by
        apply TriangleND.cclock_of_pos_angle (TRI_nd X B D not_colinear_XBD) _
        left; exact angle_BXD_is_pos
      have angle_DBX_is_pos : (∠ D B X D_ne_B X_ne_B).IsPos := by
        exact (TriangleND.angle_pos_of_cclock (TRI_nd X B D not_colinear_XBD) triangle_XBD_is_cclock).2.1
      have angle_CBA_is_pos : (∠ C B A C_ne_B A_ne_B).IsPos := by
        simp only [angle_DBX_eq_angle_CBA.symm]
        exact angle_DBX_is_pos
      have triangle_ABC_is_cclock : (TRI_nd A B C not_colinear_ABC).is_cclock := by
        apply TriangleND.cclock_of_pos_angle (TRI_nd A B C not_colinear_ABC) _
        right; left; exact angle_CBA_is_pos
      have angle_
    · sorry
  have angle_DBX_eq_neg_angle_ECY : ∠ D B X D_ne_B X_ne_B = - ∠ E C Y E_ne_C Y_ne_C := by
    calc
    ∠ D B X D_ne_B X_ne_B
    _= ∠ C B A C_ne_B A_ne_B := by
      exact angle_DBX_eq_angle_CBA
    _= - ∠ B C A C_ne_B.symm A_ne_C := angle_CBA_eq_neg_angle_BCA
    _= - ∠ E C Y E_ne_C Y_ne_C := by
      have E_int_ray_CB : E LiesInt (RAY C B C_ne_B.symm) := by
        apply SegND.lies_int_toRay_of_lies_int (seg_nd := (SEG_nd C B C_ne_B.symm))
        apply lies_int_seg_nd_of_lies_int_seg C B E C_ne_B.symm _
        apply (Seg.lies_int_rev_iff_lies_int (seg := (SEG B C))).mpr
        exact E_int_BC
      have Y_int_ray_CA : Y LiesInt (RAY C A A_ne_C) := by
        simp only [he, Line.line_of_pt_pt_eq_rev A_ne_C.symm]
        have angle_ACE_acute :  Angle.IsAcuteAngle (ANG A C E A_ne_C E_ne_C) := by
          have angle_ACE_is_angle_ACB : (ANG A C E A_ne_C E_ne_C) = (ANG A C B A_ne_C C_ne_B.symm) := by
            symm;
            apply eq_ang_of_lies_int_liesint A_ne_C C_ne_B.symm A_ne_C E_ne_C
            · exact Ray.snd_pt_lies_int_mk_pt_pt C A A_ne_C
            · exact E_int_ray_CB
          rw [angle_ACE_is_angle_ACB]
          exact ang_acute_of_is_isoceles_variant not_colinear_ABC isoceles_ABC
        exact perp_foot_lies_int_ray_of_acute_ang (A := C) (B := A) (C := E) A_ne_C E_ne_C angle_ACE_acute
      rw [eq_ang_val_of_lieson_lieson C_ne_B.symm A_ne_C E_ne_C Y_ne_C E_int_ray_CB Y_int_ray_CA]
  have triangle_XBD_acongr_triangle_YCE : (TRI_nd X B D not_colinear_XBD) ≅ₐ (TRI_nd Y C E not_colinear_YCE) := by
    apply cong_trash.acongr_of_AAS
    · exact angle_BXD_eq_neg_angle_CYE
    · exact angle_DBX_eq_neg_angle_ECY
    · exact BD_eq_CE
  exact triangle_XBD_acongr_triangle_YCE.edge₂
end Problem1_7_
