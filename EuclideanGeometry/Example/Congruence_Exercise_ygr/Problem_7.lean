import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence_trash
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex_trash

noncomputable section

namespace EuclidGeom

namespace Problem_7

/-
Let $A, B, C, D$ be four points on the plane such that $A, B, C$ are not colinear, and that $A, B, D$ are not colinear.Let $O$ be the intersection of segment $AD$ and segment $BC$.
If $\angle ACO = - \angle BDO$ and $OA = OB$, Prove that $AD = BC$.
-/

structure Setting (Plane : Type _) [EuclideanPlane Plane] where
-- Let $A, B, C, D$ be four points on the plane,
  A : Plane
  B : Plane
  C : Plane
  D : Plane
-- such that $A, B, C$ are not colinear,
  not_collinear_ABC : ¬ Collinear A B C
-- and that $A, B, D$ are not colinear.
  not_collinear_ABD : ¬ Collinear A B D
-- Let $O$ be the intersection of segment $AD$ and segment $BC$.
  O : Plane
  O_int_AD : O LiesInt (SEG A D)
  O_int_BC : O LiesInt (SEG B C)
-- Claim : $C \ne A$.
  C_ne_A : PtNe C A := ⟨(ne_of_not_collinear not_collinear_ABC).2.1.symm⟩
-- Claim : $D \ne B$.
  B_ne_D : PtNe B D := ⟨(ne_of_not_collinear not_collinear_ABD).1.symm⟩
-- Claim : $O \ne C$.
  O_ne_C : PtNe O C := ⟨(Seg.lies_int_rev_iff_lies_int.mpr O_int_BC).2⟩
-- Claim : $O \ne D$.
  O_ne_D : PtNe O D := ⟨(Seg.lies_int_rev_iff_lies_int.mpr O_int_AD).2⟩
-- If $\angle ACO = - \angle BDO$
  angle_OCA_eq_neg_angle_ODB : ∠ O C A = - (∠ O D B)
-- and $OA = OB$.
  OA_eq_OB : (SEG O A).length = (SEG O B).length
attribute [instance] Setting.C_ne_A Setting.B_ne_D Setting.O_ne_C Setting.O_ne_D

theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : (SEG e.A e.D).length = (SEG e.B e.C).length := by
/-
We have $\angle AOC = \angle DOB$ since they are opposite angles, and $\angle DOB = - \angle BOD$ by symmetry. Therefore, $\angle AOC = - \angle BOD$.
We already know that $\angle OCA = - \angle ODB$ and $OA = OB$ in the hypothesis.
In $\triangle COA$ and $\triangle DOB$,
$\cdot \angle AOC = - \angle BOD$
$\cdot \angle OCA = - \angle ODB$
$\cdot OA = OB$
Thus, $\triangle COA \cong_a \triangle DOB$ (by AAS).
So, we have $AD = AO + OD = BO + OC = BC$, since $O$ lies on $AD$ and $O$ lies on $BC$.
-/

  -- We have that $C, O, A$ are not colinear.
  have not_collinear_COA : ¬ Collinear e.C e.O e.A := by sorry
  -- We have that $D, O, B$ are not colinear.
  have not_collinear_DOB : ¬ Collinear e.D e.O e.B := by sorry
  -- We have $O \ne A$.
  haveI O_ne_A : PtNe e.O e.A := ⟨e.O_int_AD.2⟩
  -- We have $O \ne B$.
  haveI O_ne_B : PtNe e.O e.B := ⟨e.O_int_BC.2⟩
  -- We have $C \ne B$.
  haveI C_ne_B : PtNe e.C e.B := ⟨(ne_of_not_collinear e.not_collinear_ABC).1⟩
  -- We have $A \ne D$.
  haveI A_ne_D : PtNe e.A e.D := ⟨((ne_of_not_collinear e.not_collinear_ABD).2.1)⟩
  -- We have $\angle AOC = - \angle BOD$.
  have angle_AOC_eq_neg_angle_BOD : (∠ e.A e.O e.C) = - (∠ e.B e.O e.D) := by
    calc
    (∠ e.A e.O e.C)
    -- $\angle AOC = - \angle COA$ by symmetry.
    _= - (∠ e.C e.O e.A) := by
      apply Angle.neg_value_of_rev_ang
    -- $\angle COA = \angle BOD$ since they are opposite angles.
    _= - (∠ e.B e.O e.D) := by
      simp only [neg_inj]
      apply ang_eq_ang_of_toDir_eq_neg_toDir
      · calc
        (RAY e.O e.C).toDir
        _= - (RAY e.C e.O).toDir := by apply Ray.toDir_eq_neg_toDir_of_mk_pt_pt
        _= - (RAY e.C e.B).toDir := by
          congr 1;
          apply Ray.pt_pt_toDir_eq_ray_toDir (ray := (RAY e.C e.B)) (A := e.O)
          apply SegND.lies_int_toRay_of_lies_int (X := e.O) (seg_nd := (SEG_nd e.C e.B))
          exact SegND.lies_int_of_lies_int.mpr (Seg.lies_int_rev_iff_lies_int.mpr e.O_int_BC)
        _= (RAY e.B e.C).toDir := by symm; apply Ray.toDir_eq_neg_toDir_of_mk_pt_pt
        _= (RAY e.B e.O).toDir := by
          symm;
          apply Ray.pt_pt_toDir_eq_ray_toDir (ray := (RAY e.B e.C)) (A := e.O)
          apply SegND.lies_int_toRay_of_lies_int (X := e.O) (seg_nd := (SEG_nd e.B e.C))
          exact SegND.lies_int_of_lies_int.mpr e.O_int_BC
        _= - (RAY e.O e.B).toDir := by apply Ray.toDir_eq_neg_toDir_of_mk_pt_pt
      · calc
        (RAY e.O e.A).toDir
        _= - (RAY e.A e.O).toDir := by apply Ray.toDir_eq_neg_toDir_of_mk_pt_pt
        _= - (RAY e.A e.D).toDir := by
          congr 1;
          apply Ray.pt_pt_toDir_eq_ray_toDir (ray := (RAY e.A e.D)) (A := e.O)
          apply SegND.lies_int_toRay_of_lies_int (X := e.O) (seg_nd := (SEG_nd e.A e.D))
          exact SegND.lies_int_of_lies_int.mpr e.O_int_AD
        _= (RAY e.D e.A).toDir := by symm; apply Ray.toDir_eq_neg_toDir_of_mk_pt_pt
        _= (RAY e.D e.O).toDir := by
          symm;
          apply Ray.pt_pt_toDir_eq_ray_toDir (ray := (RAY e.D e.A)) (A := e.O)
          apply SegND.lies_int_toRay_of_lies_int (X := e.O) (seg_nd := (SEG_nd e.D e.A))
          exact SegND.lies_int_of_lies_int.mpr (Seg.lies_int_rev_iff_lies_int.mpr e.O_int_AD)
        _= - (RAY e.O e.D).toDir := by apply Ray.toDir_eq_neg_toDir_of_mk_pt_pt
  have triangle_COA_acongr_triangle_DOB : (TRI_nd e.C e.O e.A not_collinear_COA) ≅ₐ (TRI_nd e.D e.O e.B not_collinear_DOB) := by
    apply acongr_of_AAS'
    · exact e.angle_OCA_eq_neg_angle_ODB
    · exact angle_AOC_eq_neg_angle_BOD
    · exact e.OA_eq_OB
  calc
  (SEG e.A e.D).length
  _= (SEG e.D e.A).length := by apply length_of_rev_eq_length'
  _= (SEG e.D e.O).length + (SEG e.O e.A).length := by
    apply length_eq_length_add_length
    apply Seg.lies_on_rev_iff_lies_on.mp
    apply Seg.lies_on_of_lies_int
    exact e.O_int_AD
  _= (SEG e.C e.O).length + (SEG e.O e.B).length := by
    congr 1
    symm; exact triangle_COA_acongr_triangle_DOB.edge₃
    exact triangle_COA_acongr_triangle_DOB.edge₁
  _= (SEG e.C e.B).length := by
    symm;
    apply length_eq_length_add_length
    apply Seg.lies_on_rev_iff_lies_on.mp
    apply Seg.lies_on_of_lies_int
    exact e.O_int_BC
  _= (SEG e.B e.C).length := by apply length_of_rev_eq_length'
end Problem_7

end EuclidGeom
