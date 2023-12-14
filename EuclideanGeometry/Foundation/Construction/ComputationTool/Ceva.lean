import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Construction.ComputationTool.Oarea_method

/-!

-/
noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P]

section Ceva's_theorem

--Let $\triangle ABC$ be a (not necessarily nondegenerate) triangle.
variable {A B C : P}

--Let $D$ be a point not lying on $AB$, $BC$ and $CA$.
variable {D : P} (abd_nd : ¬ colinear A B D) (bcd_nd : ¬ colinear B C D) (cad_nd : ¬ colinear C A D)

--$A \ne B$
lemma a_ne_b : A ≠ B := (ne_of_not_colinear abd_nd).2.2.symm

--$B \ne C$
lemma b_ne_c : B ≠ C := (ne_of_not_colinear bcd_nd).2.2.symm

--$C \ne A$
lemma c_ne_a : C ≠ A := (ne_of_not_colinear cad_nd).2.2.symm

--$D \ne A$
lemma d_ne_a : D ≠ A := (ne_of_not_colinear abd_nd).2.1.symm

--$D \ne B$
lemma d_ne_b : D ≠ B := (ne_of_not_colinear bcd_nd).2.1.symm

--$D \ne C$
lemma d_ne_c : D ≠ C := (ne_of_not_colinear cad_nd).2.1.symm

--$BA$ is not parallel to $CD$
variable (ba_npara_cd : ¬ (LIN B A (a_ne_b (abd_nd := abd_nd))) ∥ (LIN C D (d_ne_c (cad_nd := cad_nd))))

--$CB$ is not parallel to $AD$
variable (cb_npara_ad : ¬ (LIN C B (b_ne_c (bcd_nd := bcd_nd))) ∥ (LIN A D (d_ne_a (abd_nd := abd_nd))))

--$AC$ is not parallel to $BD$
variable (ac_npara_bd : ¬ (LIN A C (c_ne_a (cad_nd := cad_nd))) ∥ (LIN B D (d_ne_b (bcd_nd := bcd_nd))))

--Let $E$ be the intersection of $CB$ and $AD$
variable (E : P) (e_def : E = Line.inx (LIN C B (b_ne_c (bcd_nd := bcd_nd))) (LIN A D (d_ne_a (abd_nd := abd_nd))) cb_npara_ad)

--Let $F$ be the intersection of $AC$ and $BD$
variable (F : P) (f_def : F = Line.inx (LIN A C (c_ne_a (cad_nd := cad_nd))) (LIN B D (d_ne_b (bcd_nd := bcd_nd))) ac_npara_bd)

--Let $G$ be the intersection of $BA$ and $CD$
variable (G : P) (g_def : G = Line.inx (LIN B A (a_ne_b (abd_nd := abd_nd))) (LIN C D (d_ne_c (cad_nd := cad_nd))) ba_npara_cd)

--$D,C,A$ are not colinear
lemma ncolin_dca : ¬ colinear D C A := by
  intro h0
  exact cad_nd (perm_colinear_snd_trd_fst h0)

--$E,B,C$ are colinear
lemma colin_ebc : colinear E B C := by
  have h : E LiesOn LIN C B (_ : B ≠ C) := by
    rw [e_def]
    apply Line.inx_lies_on_fst
  exact flip_colinear_fst_trd (Line.pt_pt_linear (_ : B ≠ C) h)

--$E,D,A$ are colinear
lemma colin_eda : colinear E D A := by
  have h : E LiesOn LIN A D (_ : D ≠ A) := by
    rw [e_def]
    apply Line.inx_lies_on_snd
  exact flip_colinear_fst_trd (Line.pt_pt_linear (_ : D ≠ A) h)

--$C\ne E$
lemma c_ne_e : C ≠ E := by
  have h : colinear E D A := (colin_eda (abd_nd := abd_nd) (bcd_nd := bcd_nd) (cb_npara_ad := cb_npara_ad) (e_def := e_def))
  intro k
  rw [←k] at h
  exact (ncolin_dca (cad_nd := cad_nd)) (flip_colinear_fst_snd h)

--$EB/EC=S_{\trian}DBA/S_{\trian}DCA$
lemma dratio_ebc_eq_wedge_div_wedge : divratio E B C = (wedge D B A) / (wedge D C A) := ratio_eq_wedge_div_wedge_of_colinear_colinear_notcoliear E B C D A (colin_ebc (abd_nd := abd_nd) (bcd_nd := bcd_nd) (cb_npara_ad := cb_npara_ad) (e_def := e_def)) (c_ne_e (abd_nd := abd_nd) (bcd_nd := bcd_nd) (cad_nd := cad_nd) (cb_npara_ad := cb_npara_ad) (e_def := e_def)) (colin_eda (abd_nd := abd_nd) (bcd_nd := bcd_nd) (cb_npara_ad := cb_npara_ad) (e_def := e_def)) (ncolin_dca (cad_nd := cad_nd))

--$D,A,B$ are not colinear
lemma ncolin_dab : ¬ colinear D A B := by
  intro h0
  exact abd_nd (perm_colinear_snd_trd_fst h0)

--$F,C,A$ are colinear
lemma colin_fca : colinear F C A := by
  have h : F LiesOn LIN A C (_ : C ≠ A) := by
    rw [f_def]
    apply Line.inx_lies_on_fst
  exact flip_colinear_fst_trd (Line.pt_pt_linear (_ : C ≠ A) h)

--$F,D,B$ are colinear
lemma colin_fdb : colinear F D B := by
  have h : F LiesOn LIN B D (_ : D ≠ B) := by
    rw [f_def]
    apply Line.inx_lies_on_snd
  exact flip_colinear_fst_trd (Line.pt_pt_linear (_ : D ≠ B) h)

--$A\ne F$
lemma a_ne_f : A ≠ F := by
  have h : colinear F D B := (colin_fdb (bcd_nd := bcd_nd) (cad_nd := cad_nd) (ac_npara_bd := ac_npara_bd) (f_def := f_def))
  intro k
  rw [←k] at h
  exact (ncolin_dab (abd_nd := abd_nd)) (flip_colinear_fst_snd h)

--$FC/FA=S_{\trian}DCB/S_{\trian}DAB$
lemma dratio_fca_eq_wedge_div_wedge : divratio F C A = (wedge D C B) / (wedge D A B) := ratio_eq_wedge_div_wedge_of_colinear_colinear_notcoliear F C A D B (colin_fca (bcd_nd := bcd_nd) (cad_nd := cad_nd) (ac_npara_bd := ac_npara_bd) (f_def := f_def)) (a_ne_f (bcd_nd := bcd_nd) (cad_nd := cad_nd) (abd_nd := abd_nd) (ac_npara_bd := ac_npara_bd) (f_def := f_def)) (colin_fdb (bcd_nd := bcd_nd) (cad_nd := cad_nd) (ac_npara_bd := ac_npara_bd) (f_def := f_def)) (ncolin_dab (abd_nd := abd_nd))

--$D,B,C$ are not colinear
lemma ncolin_dbc : ¬ colinear D B C := by
  intro h0
  exact bcd_nd (perm_colinear_snd_trd_fst h0)

--$G,A,B$ are colinear
lemma colin_gab : colinear G A B := by
  have h : G LiesOn LIN B A (_ : A ≠ B) := by
    rw [g_def]
    apply Line.inx_lies_on_fst
  exact flip_colinear_fst_trd (Line.pt_pt_linear (_ : A ≠ B) h)

--$G,D,C$ are colinear
lemma colin_gdc : colinear G D C := by
  have h : G LiesOn LIN C D (_ : D ≠ C) := by
    rw [g_def]
    apply Line.inx_lies_on_snd
  exact flip_colinear_fst_trd (Line.pt_pt_linear (_ : D ≠ C) h)

--$A\ne F$
lemma b_ne_g : B ≠ G := by
  have h : colinear G D C := (colin_gdc (cad_nd := cad_nd) (abd_nd := abd_nd) (ba_npara_cd := ba_npara_cd) (g_def := g_def))
  intro k
  rw [←k] at h
  exact (ncolin_dbc (bcd_nd := bcd_nd)) (flip_colinear_fst_snd h)

--$GA/GB=S_{\trian}DAC/S_{\trian}DBC$
lemma dratio_gab_eq_wedge_div_wedge : divratio G A B = (wedge D A C) / (wedge D B C) := ratio_eq_wedge_div_wedge_of_colinear_colinear_notcoliear G A B D C (colin_gab (cad_nd := cad_nd) (abd_nd := abd_nd) (ba_npara_cd := ba_npara_cd) (g_def := g_def)) (b_ne_g (cad_nd := cad_nd) (abd_nd := abd_nd) (bcd_nd := bcd_nd) (ba_npara_cd := ba_npara_cd) (g_def := g_def)) (colin_gdc (cad_nd := cad_nd) (abd_nd := abd_nd) (ba_npara_cd := ba_npara_cd) (g_def := g_def)) (ncolin_dbc (bcd_nd := bcd_nd))

lemma wedge_div_wedge_mul_eq_minus_one : (wedge D B A)/(wedge D C A) * ((wedge D C B)/(wedge D A B)) * ((wedge D A C)/(wedge D B C)) = -1 := by
  rw [wedge132 D A B, wedge132 D B C, wedge132 D C A]
  have h0 : wedge D A B ≠ 0 := (not_colinear_iff_wedge_ne_zero D A B).mp (ncolin_dab (abd_nd := abd_nd))
  have h1 : wedge D B C ≠ 0 := (not_colinear_iff_wedge_ne_zero D B C).mp (ncolin_dbc (bcd_nd := bcd_nd))
  have h1 : wedge D C A ≠ 0 := (not_colinear_iff_wedge_ne_zero D C A).mp (ncolin_dca (cad_nd := cad_nd))
  field_simp
  ring

theorem ceva_theorem : (divratio E B C) * (divratio F C A) * (divratio G A B) = -1 := by
  rw[dratio_ebc_eq_wedge_div_wedge (abd_nd := abd_nd) (bcd_nd := bcd_nd) (cad_nd := cad_nd) (cb_npara_ad := cb_npara_ad) (e_def := e_def), dratio_fca_eq_wedge_div_wedge (abd_nd := abd_nd) (bcd_nd := bcd_nd) (cad_nd := cad_nd) (ac_npara_bd := ac_npara_bd) (f_def := f_def), dratio_gab_eq_wedge_div_wedge (abd_nd := abd_nd) (bcd_nd := bcd_nd) (cad_nd := cad_nd) (ba_npara_cd := ba_npara_cd) (g_def := g_def), wedge_div_wedge_mul_eq_minus_one (abd_nd := abd_nd) (bcd_nd := bcd_nd) (cad_nd := cad_nd)]

end Ceva's_theorem

end EuclidGeom
