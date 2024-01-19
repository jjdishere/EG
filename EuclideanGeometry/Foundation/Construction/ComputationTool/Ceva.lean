import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Construction.ComputationTool.Oarea_method

/-!

-/
noncomputable section
namespace EuclidGeom

open Classical

class CevaCfgClass (P : outParam <| Type*) [outParam <| EuclideanPlane P] where
  --Let $\triangle ABC$ be a (not necessarily nondegenerate) triangle.
  (A B C : P)
  --Let $D$ be a point not lying on $AB$, $BC$ and $CA$.
  D : P
  abd_nd : ¬Collinear A B D
  bcd_nd : ¬Collinear B C D
  cad_nd : ¬Collinear C A D

  a_ne_b : PtNe A B := ⟨(ne_of_not_collinear abd_nd).2.2.symm⟩
  b_ne_c : PtNe B C := ⟨(ne_of_not_collinear bcd_nd).2.2.symm⟩
  c_ne_a : PtNe C A := ⟨(ne_of_not_collinear cad_nd).2.2.symm⟩
  d_ne_a : PtNe D A := ⟨(ne_of_not_collinear abd_nd).2.1.symm⟩
  d_ne_b : PtNe D B := ⟨(ne_of_not_collinear bcd_nd).2.1.symm⟩
  d_ne_c : PtNe D C := ⟨(ne_of_not_collinear cad_nd).2.1.symm⟩

  --$BA$ is not parallel to $CD$
  (ba_npara_cd : ¬ LIN B A ∥ LIN C D)
  --$CB$ is not parallel to $AD$
  (cb_npara_ad : ¬ LIN C B ∥ LIN A D)
  --$AC$ is not parallel to $BD$
  (ac_npara_bd : ¬ LIN A C ∥ LIN B D)
  --Let $E$ be the intersection of $CB$ and $AD$
  E : P
  e_def : E = Line.inx (LIN C B) (LIN A D) cb_npara_ad
  --Let $F$ be the intersection of $AC$ and $BD$
  F : P
  f_def : F = Line.inx (LIN A C) (LIN B D) ac_npara_bd
  --Let $G$ be the intersection of $BA$ and $CD$
  G : P
  g_def : G = Line.inx (LIN B A) (LIN C D) ba_npara_cd

namespace CevaCfgClass
variable {P : Type*} [EuclideanPlane P] [cfg : CevaCfgClass P]

attribute [instance] a_ne_b b_ne_c c_ne_a d_ne_a d_ne_b d_ne_c

--$D,C,A$ are not collinear
lemma ncolin_dca : ¬ Collinear D C A := by
  intro h0
  exact cad_nd (Collinear.perm₂₃₁ h0)

--$E,B,C$ are collinear
lemma colin_ebc : Collinear E B C := by
  have h : E LiesOn LIN C B := by
    rw [e_def]
    apply Line.inx_lies_on_fst
  exact Collinear.perm₃₂₁ (Line.pt_pt_linear h)

--$E,D,A$ are collinear
lemma colin_eda : Collinear E D A := by
  have h : E LiesOn LIN A D := by
    rw [e_def]
    apply Line.inx_lies_on_snd
  exact Collinear.perm₃₂₁ (Line.pt_pt_linear h)

--$C\ne E$
instance c_ne_e : PtNe C E := Fact.mk <| by
  have h : Collinear E D A := colin_eda
  intro k
  rw [←k] at h
  exact ncolin_dca (Collinear.perm₂₁₃ h)

--$EB/EC=S_{\trian}DBA/S_{\trian}DCA$
lemma dratio_ebc_eq_wedge_div_wedge : divratio E B C = (wedge D B A) / (wedge D C A) :=
  ratio_eq_wedge_div_wedge_of_collinear_collinear_notcoliear E B C D A colin_ebc colin_eda ncolin_dca

--$D,A,B$ are not collinear
lemma ncolin_dab : ¬ Collinear D A B := by
  intro h0
  exact abd_nd (Collinear.perm₂₃₁ h0)

--$F,C,A$ are collinear
lemma colin_fca : Collinear F C A := by
  have h : F LiesOn LIN A C := by
    rw [f_def]
    apply Line.inx_lies_on_fst
  exact Collinear.perm₃₂₁ (Line.pt_pt_linear h)

--$F,D,B$ are collinear
lemma colin_fdb : Collinear F D B := by
  have h : F LiesOn LIN B D := by
    rw [f_def]
    apply Line.inx_lies_on_snd
  exact Collinear.perm₃₂₁ (Line.pt_pt_linear h)

--$A\ne F$
instance a_ne_f : PtNe A F := Fact.mk <| by
  have h : Collinear F D B := colin_fdb
  intro k
  rw [←k] at h
  exact ncolin_dab (Collinear.perm₂₁₃ h)

--$FC/FA=S_{\trian}DCB/S_{\trian}DAB$
lemma dratio_fca_eq_wedge_div_wedge : divratio F C A = (wedge D C B) / (wedge D A B) :=
  ratio_eq_wedge_div_wedge_of_collinear_collinear_notcoliear F C A D B colin_fca colin_fdb ncolin_dab

--$D,B,C$ are not collinear
lemma ncolin_dbc : ¬ Collinear D B C := by
  intro h0
  exact bcd_nd (Collinear.perm₂₃₁ h0)

--$G,A,B$ are collinear
lemma colin_gab : Collinear G A B := by
  have h : G LiesOn LIN B A _ := by
    rw [g_def]
    apply Line.inx_lies_on_fst
  exact Collinear.perm₃₂₁ (Line.pt_pt_linear h)

--$G,D,C$ are collinear
lemma colin_gdc : Collinear G D C := by
  have h : G LiesOn LIN C D _ := by
    rw [g_def]
    apply Line.inx_lies_on_snd
  exact Collinear.perm₃₂₁ (Line.pt_pt_linear h)

--$A\ne F$
instance b_ne_g : PtNe B G := Fact.mk <| by
  have h : Collinear G D C := colin_gdc
  intro k
  rw [←k] at h
  exact ncolin_dbc (Collinear.perm₂₁₃ h)

--$GA/GB=S_{\trian}DAC/S_{\trian}DBC$
lemma dratio_gab_eq_wedge_div_wedge : divratio G A B = (wedge D A C) / (wedge D B C) := ratio_eq_wedge_div_wedge_of_collinear_collinear_notcoliear G A B D C colin_gab colin_gdc ncolin_dbc

lemma wedge_div_wedge_mul_eq_minus_one : (wedge D B A)/(wedge D C A) * ((wedge D C B)/(wedge D A B)) * ((wedge D A C)/(wedge D B C)) = -1 := by
  rw [wedge132 D A B, wedge132 D B C, wedge132 D C A]
  have h0 : wedge D A B ≠ 0 := (not_collinear_iff_wedge_ne_zero D A B).mp ncolin_dab
  have h1 : wedge D B C ≠ 0 := (not_collinear_iff_wedge_ne_zero D B C).mp ncolin_dbc
  have h1 : wedge D C A ≠ 0 := (not_collinear_iff_wedge_ne_zero D C A).mp ncolin_dca
  field_simp
  ring

theorem ceva_theorem : (divratio E B C) * (divratio F C A) * (divratio G A B) = -1 := by
  rw[dratio_ebc_eq_wedge_div_wedge, dratio_fca_eq_wedge_div_wedge, dratio_gab_eq_wedge_div_wedge, wedge_div_wedge_mul_eq_minus_one]

end CevaCfgClass

def CevaCfg (P : Type*) [EuclideanPlane P] := CevaCfgClass P

lemma CevaCfg.ceva_theorem {P : Type*} [EuclideanPlane P] (cfg : CevaCfg P) :
    (divratio cfg.E cfg.B cfg.C) * (divratio cfg.F cfg.C cfg.A) * (divratio cfg.G cfg.A cfg.B) = -1 :=
  CevaCfgClass.ceva_theorem (cfg := cfg)

variable {P : Type*} [EuclideanPlane P] {A B C D : P}
  (abd_nd : ¬Collinear A B D)
  (bcd_nd : ¬Collinear B C D)
  (cad_nd : ¬Collinear C A D)
  (ba_npara_cd : ¬ LIN B A (ne_of_not_collinear abd_nd).2.2.symm ∥ LIN C D (ne_of_not_collinear cad_nd).2.1.symm)
  (cb_npara_ad : ¬ LIN C B (ne_of_not_collinear bcd_nd).2.2.symm ∥ LIN A D (ne_of_not_collinear abd_nd).2.1.symm)
  (ac_npara_bd : ¬ LIN A C (ne_of_not_collinear cad_nd).2.2.symm ∥ LIN B D (ne_of_not_collinear bcd_nd).2.1.symm)
  (E : P)
  (e_def : E = Line.inx (LIN C B (ne_of_not_collinear bcd_nd).2.2.symm) (LIN A D (ne_of_not_collinear abd_nd).2.1.symm) cb_npara_ad)
  (F : P)
  (f_def : F = Line.inx (LIN A C (ne_of_not_collinear cad_nd).2.2.symm) (LIN B D (ne_of_not_collinear bcd_nd).2.1.symm) ac_npara_bd)
  (G : P)
  (g_def : G = Line.inx (LIN B A (ne_of_not_collinear abd_nd).2.2.symm) (LIN C D (ne_of_not_collinear cad_nd).2.1.symm) ba_npara_cd)

theorem ceva_theorem : (divratio E B C) * (divratio F C A) * (divratio G A B) = -1 :=
  let cfg : CevaCfg P :=
  { abd_nd := abd_nd
    bcd_nd := bcd_nd
    cad_nd := cad_nd
    ba_npara_cd := ba_npara_cd
    cb_npara_ad := cb_npara_ad
    ac_npara_bd := ac_npara_bd
    e_def := e_def
    f_def := f_def
    g_def := g_def }
  cfg.ceva_theorem

end EuclidGeom
