import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence_trash

noncomputable section

namespace EuclidGeom

namespace Congruence_exercise_ygr_7

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
  not_colinear_ABC : ¬ colinear A B C
-- and that $A, B, D$ are not colinear.
  not_colinear_ABD : ¬ colinear A B D
-- Let $O$ be the intersection of segment $AD$ and segment $BC$.
  O : Plane
  O_int_AD : O LiesInt (SEG A D)
  O_int_BC : O LiesInt (SEG B C)
-- Claim : $C \ne A$.
  C_ne_A : PtNe C A := ⟨(ne_of_not_colinear not_colinear_ABC).2.1.symm⟩
-- Claim : $D \ne B$.
  B_ne_D : PtNe B D := ⟨(ne_of_not_colinear not_colinear_ABD).1.symm⟩
-- Claim : $O \ne C$.
  O_ne_C : PtNe O C := ⟨ne_source_of_lies_int_seg C B O (Seg.lies_int_rev_iff_lies_int.mpr O_int_BC)⟩
-- Claim : $O \ne D$.
  O_ne_D : PtNe O D := ⟨ne_source_of_lies_int_seg D A O (Seg.lies_int_rev_iff_lies_int.mpr O_int_AD)⟩
-- If $\angle ACO = - \angle BDO$
  angle_OCA_eq_neg_angle_ODB : ∠ O C A = - (∠ O D B)
-- and $OA = OB$.
  OA_eq_OB : (SEG O A).length = (SEG O B).length
attribute [instance] Setting.C_ne_A Setting.B_ne_D Setting.O_ne_C Setting.O_ne_D
theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : (SEG e.A e.D).length = (SEG e.B e.C).length := by
  have not_colinear_COA : ¬ colinear e.C e.O e.A := by sorry
  have not_colinear_DOB : ¬ colinear e.D e.O e.B := by sorry
  haveI O_ne_A : PtNe e.O e.A := ⟨ne_source_of_lies_int_seg e.A e.D e.O e.O_int_AD⟩
  haveI O_ne_B : PtNe e.O e.B := ⟨ne_source_of_lies_int_seg e.B e.C e.O e.O_int_BC⟩
  haveI C_ne_B : PtNe e.C e.B := ⟨(ne_of_not_colinear e.not_colinear_ABC).1⟩
  haveI A_ne_D : PtNe e.A e.D := ⟨((ne_of_not_colinear e.not_colinear_ABD).2.1)⟩
  have angle_AOC_eq_neg_angle_BOD : (∠ e.A e.O e.C) = - (∠ e.B e.O e.D) := by
    calc
    (∠ e.A e.O e.C)
    _= - (∠ e.C e.O e.A) := by
      exact Angle.ang_value_rev_eq_neg_value (ang := ANG e.C e.O e.A)
    _= - (∠ e.B e.O e.D) := by
      simp only [neg_inj]
      apply ang_eq_ang_of_toDir_rev_toDir
      · calc
        (RAY e.O e.C).toDir
        _= - (RAY e.C e.O).toDir := by apply Ray.toDir_eq_neg_toDir_of_mk_pt_pt
        _= - (RAY e.C e.B).toDir := by
          congr 1;
          apply Ray.pt_pt_toDir_eq_ray_toDir (ray := (RAY e.C e.B)) (A := e.O)
          apply SegND.lies_int_toRay_of_lies_int (X := e.O) (seg_nd := (SEG_nd e.C e.B))
          exact lies_int_seg_nd_of_lies_int_seg e.C e.B e.O (Seg.lies_int_rev_iff_lies_int.mpr e.O_int_BC)
        _= (RAY e.B e.C).toDir := by symm; apply Ray.toDir_eq_neg_toDir_of_mk_pt_pt
        _= (RAY e.B e.O).toDir := by
          symm;
          apply Ray.pt_pt_toDir_eq_ray_toDir (ray := (RAY e.B e.C)) (A := e.O)
          apply SegND.lies_int_toRay_of_lies_int (X := e.O) (seg_nd := (SEG_nd e.B e.C))
          exact lies_int_seg_nd_of_lies_int_seg e.B e.C e.O e.O_int_BC
        _= - (RAY e.O e.B).toDir := by apply Ray.toDir_eq_neg_toDir_of_mk_pt_pt
      · calc
        (RAY e.O e.A).toDir
        _= - (RAY e.A e.O).toDir := by apply Ray.toDir_eq_neg_toDir_of_mk_pt_pt
        _= - (RAY e.A e.D).toDir := by
          congr 1;
          apply Ray.pt_pt_toDir_eq_ray_toDir (ray := (RAY e.A e.D)) (A := e.O)
          apply SegND.lies_int_toRay_of_lies_int (X := e.O) (seg_nd := (SEG_nd e.A e.D))
          exact lies_int_seg_nd_of_lies_int_seg e.A e.D e.O e.O_int_AD
        _= (RAY e.D e.A).toDir := by symm; apply Ray.toDir_eq_neg_toDir_of_mk_pt_pt
        _= (RAY e.D e.O).toDir := by
          symm;
          apply Ray.pt_pt_toDir_eq_ray_toDir (ray := (RAY e.D e.A)) (A := e.O)
          apply SegND.lies_int_toRay_of_lies_int (X := e.O) (seg_nd := (SEG_nd e.D e.A))
          exact lies_int_seg_nd_of_lies_int_seg e.D e.A e.O (Seg.lies_int_rev_iff_lies_int.mpr e.O_int_AD)
        _= - (RAY e.O e.D).toDir := by apply Ray.toDir_eq_neg_toDir_of_mk_pt_pt
  have triangle_COA_acongr_triangle_DOB : (TRI_nd e.C e.O e.A not_colinear_COA) ≅ₐ (TRI_nd e.D e.O e.B not_colinear_DOB) := by
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
end Congruence_exercise_ygr_7

end EuclidGeom
