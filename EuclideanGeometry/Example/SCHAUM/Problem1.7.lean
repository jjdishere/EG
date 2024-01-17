import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Line_trash
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex_trash

noncomputable section

namespace EuclidGeom

namespace Schaum

namespace Problem1_7
/-Let $\triangle ABC$ be an isoceles triangle in which $AB = AC$.
Let $D$ and $E$ be points on the segment $BC$ such that $BD = CE$.

Prove that the height of $D$ to $AB$ is the same as the height of $E$ to $AC$.
-/

structure Setting (Plane : Type _) [EuclideanPlane Plane] where
--Let $\triangle ABC$ be an isoceles triangle in which $AB = AC$
  A : Plane
  B : Plane
  C : Plane
  not_collinear_ABC : ¬ collinear A B C
  isoceles_ABC : (▵ A B C).IsIsoceles
--Let $D$ be point on the segment $BC$
  D : Plane
  D_int_BC : D LiesInt (SEG B C)
--Let $E$ be point on the segment $BC$
  E : Plane
  E_int_BC : E LiesInt (SEG B C)
--such that $BD = CE$
  BD_eq_CE : (SEG B D).length = (SEG C E).length
--Claim $B \ne A$
  B_ne_A : B ≠ A :=
  -- This is because vertices $A, B$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.2
--Claim $C \ne A$
  C_ne_A : C ≠ A :=
  -- This is because vertices $A, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.1.symm
--take the foot of the height of $D$ to $AB$ and denote as $X$
  X : Plane
  hd : X = perp_foot D (LIN A B B_ne_A)
--take the foot of the height of $E$ to $AB$ and denote as $Y$
  Y : Plane
  he : Y = perp_foot E (LIN A C C_ne_A)
--Prove that $DX = EY$.

theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : (SEG e.D e.X).length = (SEG e.E e.Y).length := by
/-
In isoceles triangle $ABC$, we have $\angle ABC$ and $\angle ACB$ are acute.
From $D$ lies on $BC$ and $\angle ABC$ is acute, we know that $X$ lies on ray $BA$, so $\angle XBD$ is the same as $\angle ABC$.
From $E$ lies on $BC$ and $\angle ACB$ is acute, we know that $Y$ lies on ray $CA$, so $\angle YCE$ is the same as $\angle ACB$.
In isoceles triangle $ABC$, we have $\angle CBA = - \angle ACB$.
So $\angle DBX = \angle CBA = - \angle BCA = - \angle ECY$.
Since $DX$ is perpendicular to $AB$ at $X$, we have $\angle BXD = \pi/2 (\mod \pi)$.
Since $EY$ is perpendicular to $AC$ at $Y$, we have $\angle CYE = \pi/2 (\mod \pi)$.
Thus, $\angle BXD = \angle CYE (\mod \pi)$.
In $\triangle XBD$ and $\triangle YCE$,
$\cdot $\angle BXD = \angle CYE (\mod \pi)$
$\cdot \angle DBX = - \angle ECY$
$\cdot BD = CE$
Thus, $\triangle XBD \cong_a \triangle YEC$ (by AAS)
Therefore, $DX = EY$.
-/
  -- We have $D \ne B$.
  have D_ne_B : e.D ≠ e.B := by sorry
  -- We have $E \ne C$.
  have E_ne_C : e.E ≠ e.C := by sorry
  -- We have that $A, B, C$ are pairwise distinct.
  have A_ne_B : e.A ≠ e.B := by sorry
  have C_ne_B : e.C ≠ e.B := by sorry
  have A_ne_C : e.A ≠ e.C := by sorry
  -- We have that $D$ doesn't lies on line $AB$.
  have D_not_on_AB : ¬ e.D LiesOn (LIN e.A e.B e.B_ne_A) := by sorry
  -- We have that $E$ doesn't lies on line $AC$.
  have E_not_on_AC : ¬ e.E LiesOn (LIN e.A e.C e.C_ne_A) := by sorry
  --We have that $E$ lies on ray $CB$.
  have E_int_ray_CB : e.E LiesInt (RAY e.C e.B C_ne_B.symm) := by
    -- It suffices to prove that $E$ lies on segment $CB$.
    apply SegND.lies_int_toRay_of_lies_int (seg_nd := (SEG_nd e.C e.B C_ne_B.symm))
    -- By symmetry, we only need to show that $E$ lies on segment $BC$,
    apply (Seg.lies_int_rev_iff_lies_int (seg := (SEG e.B e.C))).mpr
    -- which is what we already know.
    exact e.E_int_BC
  -- We have that $Y$ lies on ray $CA$.
  have Y_int_ray_CA : e.Y LiesInt (RAY e.C e.A A_ne_C) := by
    simp only [e.he, Line.line_of_pt_pt_eq_rev (_h := ⟨A_ne_C.symm⟩)]
    -- We have that $\angle ACE$ is an acute angle.
    have angle_ACE_acute :  Angle.IsAcu (ANG e.A e.C e.E A_ne_C E_ne_C) := by
      -- Because $\angle ACE$ is exactly the same angle as $\angle ACB$, which is the consequence of the fact that $E$ lies on ray $CB$.
      have angle_ACE_is_angle_ACB : (ANG e.A e.C e.E A_ne_C E_ne_C) = (ANG e.A e.C e.B A_ne_C C_ne_B.symm) := by
        symm;
        apply eq_ang_of_lies_int_liesint A_ne_C C_ne_B.symm A_ne_C E_ne_C
        · exact Ray.snd_pt_lies_int_mk_pt_pt e.C e.A A_ne_C
        · exact E_int_ray_CB
      -- and $\angle ACB$ is acute because it's a base angle of the isoceles triangle $ABC$.
      simp only [angle_ACE_is_angle_ACB]
      exact ang_acute_of_is_isoceles_variant e.not_collinear_ABC e.isoceles_ABC
    -- The perpendicular foot from a point on one ray of an acute angle to the other ray always falls on the interior of the other ray, so we know that $Y$, which is the perpendicular foot of $E$ to line $AC$, falls on the interior of ray $CA$.
    exact perp_foot_lies_int_ray_of_acute_ang (A := e.C) (B := e.A) (C := e.E) A_ne_C E_ne_C angle_ACE_acute
  -- We have $Y \ne C$ as Y is on the interior of ray $CA$ and therefore different to the source $C$.
  have Y_ne_C : e.Y ≠ e.C := Y_int_ray_CA.2
  -- We have $Y, C, E$ are not collinear because $E$ doesn't lies on line $AC$ and $C$ doesn't coincide with $Y$.
  have not_collinear_YCE : ¬ collinear e.Y e.C e.E := by exact not_collinear_with_perp_foot_of_ne_perp_foot e.E e.C e.Y (LIN e.A e.C e.C_ne_A) (Line.snd_pt_lies_on_mk_pt_pt e.C_ne_A) E_not_on_AC e.he (Y_ne_C).symm
  -- We have $E \ne Y$.
  have E_ne_Y : e.E ≠ e.Y := by sorry

  --We have that $D$ lies on ray $BC$.
  have D_int_ray_BC : e.D LiesInt (RAY e.B e.C C_ne_B) := by
    -- It suffices to prove that $D$ lies on segment $BC$.
    apply SegND.lies_int_toRay_of_lies_int (seg_nd := (SEG_nd e.B e.C C_ne_B))
    -- which is what we already know.
    exact e.D_int_BC
  -- We have that $X$ lies on ray $BA$.
  have X_int_ray_BA : e.X LiesInt (RAY e.B e.A A_ne_B) := by
    simp only [e.hd, Line.line_of_pt_pt_eq_rev (_h := ⟨A_ne_C.symm⟩)]
    -- We have that $\angle ABD$ is an acute angle.
    have angle_ABD_acute :  Angle.IsAcu (ANG e.A e.B e.D A_ne_B D_ne_B) := by
      -- Because $\angle ABD$ is exactly the same angle as $\angle ABC$, which is the consequence of the fact that $D$ lies on ray $BC$.
      have angle_ABD_is_angle_ABC : (ANG e.A e.B e.D A_ne_B D_ne_B) = (ANG e.A e.B e.C A_ne_B C_ne_B) := by
        symm;
        apply eq_ang_of_lies_int_liesint A_ne_B C_ne_B A_ne_B D_ne_B
        · exact Ray.snd_pt_lies_int_mk_pt_pt e.B e.A A_ne_B
        · exact D_int_ray_BC
      simp only [angle_ABD_is_angle_ABC]
      -- and $\angle ABC$ is acute because it's a base angle of the isoceles triangle $ABC$.
      apply is_acute_of_is_acute_rev C_ne_B A_ne_B
      exact ang_acute_of_is_isoceles e.not_collinear_ABC e.isoceles_ABC
    -- The perpendicular foot from a point on one ray of an acute angle to the other ray always falls on the interior of the other ray, so we know that $X$, which is the perpendicular foot of $D$ to line $AB$, falls on the interior of ray $BA$.
    exact perp_foot_lies_int_ray_of_acute_ang A_ne_B D_ne_B angle_ABD_acute
  -- We have $X \ne B$ as X is on the interior of ray $BA$ and therefore different to the source $B$.
  have X_ne_B : e.X ≠ e.B := X_int_ray_BA.2
  -- We have $X, B, D$ are not collinear because $D$ doesn't lies on line $AB$ and $B$ doesn't coincide with $X$.
  have not_collinear_XBD : ¬ collinear e.X e.B e.D := by
    by_contra h
    haveI : PtNe e.X e.B := ⟨X_ne_B⟩
    have : e.D LiesOn LIN e.X e.B := Line.pt_pt_maximal h
    have : LIN e.X e.B = LIN e.A e.B _ := sorry
    have : e.D LiesOn LIN e.A e.B _ := sorry
    exact D_not_on_AB this
  -- We have $D \ne X$.
  have D_ne_X : e.D ≠ e.X := by sorry
  -- In isoceles triangle $ABC$, we have $\angle CBA = - \angle BCA$.
  have angle_CBA_eq_neg_angle_BCA : ∠ e.C e.B e.A C_ne_B A_ne_B = - ∠ e.B e.C e.A C_ne_B.symm A_ne_C := by
    calc
    ∠ e.C e.B e.A C_ne_B A_ne_B
    -- $\angle CBA = \angle ACB$ because triangle $ABC$ is an isoceles triangle.
    _= ∠ e.A e.C e.B A_ne_C C_ne_B.symm := is_isoceles_tri_iff_ang_eq_ang_of_nd_tri (tri_nd := (TRI_nd e.A e.B e.C e.not_collinear_ABC)).mp e.isoceles_ABC
    -- $\angle ACB = - \angle BCA$ by symmetry.
    _= - ∠ e.B e.C e.A C_ne_B.symm A_ne_C := (ANG e.B e.C e.A C_ne_B.symm A_ne_C).rev_value_eq_neg_value
  -- We have that $\angle BXD = \angle CYE (\mod \pi)$.
  have angle_BXD_eq_neg_angle_CYE : (ANG e.B e.X e.D X_ne_B.symm D_ne_X).dvalue = - (ANG e.C e.Y e.E Y_ne_C.symm E_ne_Y).dvalue := by
    -- We have $\angle BXD = \pi/2 (\mod \pi)$.
    have angle_BXD_is_right_angle : (ANG e.B e.X e.D X_ne_B.symm D_ne_X).dvalue = ↑(π / 2) := by
      calc
      (ANG e.B e.X e.D X_ne_B.symm D_ne_X).dvalue
      -- $\angle BXD = - \angle DXB (\mod \pi)$ by symmetry,
      _= - (ANG e.D e.X e.B D_ne_X X_ne_B.symm).dvalue :=
        (ANG e.D e.X e.B D_ne_X X_ne_B.symm).rev_dvalue_eq_neg_dvalue
      -- $\angle DXB = \pi/2 (\mod \pi)$ because $X$ is the perpendicular foot of $D$ to $AB$,
      _= - ↑ (π / 2) := by
        apply neg_inj.mpr
        sorry
        /- exact Angle.dvalue_eq_pi_div_two_at_perp_foot e.D e.B e.X (LIN e.A e.B e.B_ne_A) (Line.snd_pt_lies_on_mk_pt_pt (_h := ⟨e.B_ne_A⟩)) D_not_on_AB e.hd (X_ne_B).symm -/
      -- $ - \pi/2 = \pi/2 (\mod \pi)$.
      _= ↑ (π / 2) := by simp only [AngDValue.neg_coe_pi_div_two]
    -- We have $\angle CYE = \pi/2 (\mod \pi)$.
    have angle_CYE_is_right_angle : (ANG e.C e.Y e.E Y_ne_C.symm E_ne_Y).dvalue = ↑(π / 2) := by
      calc
      (ANG e.C e.Y e.E Y_ne_C.symm E_ne_Y).dvalue
      -- $\angle CYE = - \angle EYC (\mod \pi)$ by symmetry,
      _= - (ANG e.E e.Y e.C E_ne_Y Y_ne_C.symm).dvalue :=
        (ANG e.E e.Y e.C E_ne_Y Y_ne_C.symm).rev_dvalue_eq_neg_dvalue
      -- $\angle EYC = \pi/2 (\mod \pi)$ because $Y$ is the perpendicular foot of $E$ to $AC$,
      _= - ↑ (π / 2) := by
        apply neg_inj.mpr
        sorry
        /- exact dvalue_eq_pi_div_two_at_perp_foot e.E e.C e.Y (LIN e.A e.C e.C_ne_A) (Line.snd_pt_lies_on_mk_pt_pt e.C_ne_A) E_not_on_AC e.he (Y_ne_C).symm -/
      -- $ - \pi/2 = \pi/2 (\mod \pi)$.
      _= ↑ (π / 2) := by simp only [AngDValue.neg_coe_pi_div_two]
    -- $ - \pi/2 = \pi/2 (\mod \pi)$.
    simp only[angle_BXD_is_right_angle, angle_CYE_is_right_angle, AngDValue.neg_coe_pi_div_two]
  -- We have that $\angle DBX = - \angle ECY$.
  have angle_DBX_eq_neg_angle_ECY : ∠ e.D e.B e.X D_ne_B X_ne_B = - ∠ e.E e.C e.Y E_ne_C Y_ne_C := by
    calc
    ∠ e.D e.B e.X D_ne_B X_ne_B
    -- $\angle DBX = \angle CBA$ because $D$ lies on ray $BC$ and $X$ lies on ray $BA$,
    _= ∠ e.C e.B e.A C_ne_B A_ne_B := by
      symm; exact Angle.value_eq_of_lies_on_ray_pt_pt C_ne_B A_ne_B D_ne_B X_ne_B D_int_ray_BC X_int_ray_BA
    -- $\angle CBA = - \angle BCA$,
    _= - ∠ e.B e.C e.A C_ne_B.symm A_ne_C := angle_CBA_eq_neg_angle_BCA
    -- $\angle BCA = - \angle ECY$ because $e$ lies on ray $CB$ and $Y$ lies on ray $CA$.
    _= - ∠ e.E e.C e.Y E_ne_C Y_ne_C := by
      simp only [Angle.value_eq_of_lies_on_ray_pt_pt C_ne_B.symm A_ne_C E_ne_C Y_ne_C E_int_ray_CB Y_int_ray_CA]
  -- $\triangle XBD \cong_a \triangle YEC$ (by AAS)
  have triangle_XBD_acongr_triangle_YCE : (TRI_nd e.X e.B e.D not_collinear_XBD) ≅ₐ (TRI_nd e.Y e.C e.E not_collinear_YCE) := by
    apply acongr_of_AAS_variant
    -- $\cdot $\angle BXD = \angle CYE (\mod \pi)$
    · exact angle_BXD_eq_neg_angle_CYE
    -- $\cdot \angle DBX = - \angle ECY$
    · exact angle_DBX_eq_neg_angle_ECY
    -- $\cdot BD = CE$
    · exact e.BD_eq_CE
  -- Therefore, $DX = EY$.
  exact triangle_XBD_acongr_triangle_YCE.edge₂
end Problem1_7
end Schaum
end EuclidGeom
