import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Linear.Order
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex_trash

noncomputable section

namespace EuclidGeom

namespace Problem_5

/-
Let $l$ be a directed line on the plane.
Let $A, F, C, D$ be four points on $l$ in this order.
Let $B, E$ be two points on the plane such that they lies on different sides of $l$, and that $CB \parallel FE$.
If $\angle BAC = \angle EDF$ and $AF = DC$, prove that $AB = DE$.
-/

structure Setting1 (Plane : Type _) [EuclideanPlane Plane] where
-- Let $l$ be a directed line on the plane
  l : DirLine Plane
-- Let $A, F, C, D$ be four points on $l$ in this order.
  A : Plane
  F : Plane
  C : Plane
  D : Plane
  A_on_l : A LiesOn l
  F_on_l : F LiesOn l
  C_on_l : C LiesOn l
  D_on_l : D LiesOn l
  A_lt_F_on_l : (⟨A, A_on_l⟩ : l.carrier.Elem) < ⟨F, F_on_l⟩
  F_lt_C_on_l : (⟨F, F_on_l⟩ : l.carrier.Elem) < ⟨C, C_on_l⟩
  C_lt_D_on_l : (⟨C, C_on_l⟩ : l.carrier.Elem) < ⟨D, D_on_l⟩
-- Let $B, E$ be two points on the plane,
  B : Plane
  E : Plane
-- such that they lies on different sides of $l$,
  B_E_IsOnOppositeSide_l : IsOnOppositeSide B E l

-- Claim : $A \ne C$.
lemma A_ne_C' {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : e.A ≠ e.C := by
  apply (DirLine.ne_iff_ne_as_line_elem e.A_on_l e.C_on_l).mpr; apply ne_of_lt;
  calc
  (⟨e.A, e.A_on_l⟩ : e.l.carrier.Elem)
  _< ⟨e.F, e.F_on_l⟩ := e.A_lt_F_on_l
  _< ⟨e.C, e.C_on_l⟩ := e.F_lt_C_on_l
instance A_ne_C {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.A e.C := ⟨A_ne_C'⟩
-- Claim : $D \ne F$.
lemma D_ne_F' {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : e.D ≠ e.F := by
  symm; apply (DirLine.ne_iff_ne_as_line_elem e.F_on_l e.D_on_l).mpr; apply ne_of_lt;
  calc
  (⟨e.F, e.F_on_l⟩ : e.l.carrier.Elem)
  _< ⟨e.C, e.C_on_l⟩ := e.F_lt_C_on_l
  _< ⟨e.D, e.D_on_l⟩ := e.C_lt_D_on_l
instance D_ne_F {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.D e.F := ⟨D_ne_F'⟩
lemma not_collinear_BCA {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : ¬ Collinear e.B e.C e.A := by
  have h : IsOnOppositeSide e.B e.E (RAY e.C e.A) := by
    have h3 : (RAY e.C e.A).toLine = e.l.toLine := by
      calc
        _= (LIN e.C e.A) := by
          apply Line.eq_line_of_pt_pt_of_ne
          apply Line.fst_pt_lies_on_mk_pt_pt
          apply Line.snd_pt_lies_on_mk_pt_pt
        _=_ := by
          apply Line.eq_line_of_pt_pt_of_ne
          apply DirLine.lies_on_iff_lies_on_toLine.mpr; exact e.C_on_l
          apply DirLine.lies_on_iff_lies_on_toLine.mpr; exact e.A_on_l
    have : IsOnOppositeSide e.B e.E (RAY e.C e.A) = IsOnOppositeSide e.B e.E e.l := by
      calc
        _= IsOnOppositeSide e.B e.E (RAY e.C e.A).toLine := by rfl
        _=_ := by congr
    simp only [this]
    exact e.B_E_IsOnOppositeSide_l
  have h1 : ¬ Collinear e.C e.A e.B := (not_collinear_of_IsOnOppositeSide e.C e.A e.B e.E h).1
  by_contra h2; absurd h1
  perm_collinear
lemma not_collinear_EFD {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : ¬ Collinear e.E e.F e.D := by
  have h : IsOnOppositeSide e.B e.E (RAY e.F e.D) := by
    have h3 : (RAY e.F e.D).toLine = e.l.toLine := by
      calc
        _= (LIN e.F e.D) := by
          apply Line.eq_line_of_pt_pt_of_ne
          apply Line.fst_pt_lies_on_mk_pt_pt
          apply Line.snd_pt_lies_on_mk_pt_pt
        _=_ := by
          apply Line.eq_line_of_pt_pt_of_ne
          apply DirLine.lies_on_iff_lies_on_toLine.mpr; exact e.F_on_l
          apply DirLine.lies_on_iff_lies_on_toLine.mpr; exact e.D_on_l
    have : IsOnOppositeSide e.B e.E (RAY e.F e.D) = IsOnOppositeSide e.B e.E e.l := by
      calc
        _= IsOnOppositeSide e.B e.E (RAY e.F e.D).toLine := by rfl
        _=_ := by congr
    simp only [this]
    exact e.B_E_IsOnOppositeSide_l
  have h1 : ¬ Collinear e.F e.D e.E := (not_collinear_of_IsOnOppositeSide e.F e.D e.B e.E h).2
  by_contra h2; absurd h1
  perm_collinear
-- Claim : $C \ne B$.
instance C_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.C e.B := ⟨(ne_of_not_collinear not_collinear_BCA).2.2⟩
-- Claim : $A \ne B$.
instance A_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.A e.B := ⟨(ne_of_not_collinear not_collinear_BCA).2.1.symm⟩
-- Claim : $E \ne F$.
instance E_ne_F {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.E e.F := ⟨(ne_of_not_collinear not_collinear_EFD).2.2.symm⟩
-- Claim : $E \ne D$.
instance E_ne_D {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.E e.D := ⟨(ne_of_not_collinear not_collinear_EFD).2.1⟩

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends Setting1 Plane where
  not_collinear_BCA : ¬ Collinear B C A := not_collinear_BCA
  not_collinear_EFD : ¬ Collinear E F D := not_collinear_EFD
-- and that $CB \parallel FE$,
  CB_parallel_FE : (LIN C B) ∥ (LIN F E)
-- If $\angle BAC = - \angle EDF$,
  angle_BAC_eq_angle_EDF : (∠ B A C) = (∠ E D F)
-- and $AF = DC$,
  AF_eq_DC : (SEG A F).length = (SEG D C).length
-- Prove that $AB = DE$.

theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting2 Plane) : (SEG e.A e.B).length = (SEG e.D e.E).length := by
  have F_int_AC : e.F LiesInt (SEG e.A e.C) := by
    apply DirLine.lies_int_seg_of_lt_and_lt e.A_on_l e.F_on_l e.C_on_l
    simp only [e.A_lt_F_on_l]
    simp only [e.F_lt_C_on_l]
  have C_int_DF : e.C LiesInt (SEG e.D e.F) := by
    apply DirLine.lies_int_seg_of_gt_and_gt e.D_on_l e.C_on_l e.F_on_l
    simp only [e.C_lt_D_on_l]
    simp only [e.F_lt_C_on_l]
  have C_ne_F' : e.C ≠ e.F := by
    apply (DirLine.ne_iff_ne_as_line_elem e.C_on_l e.F_on_l).mpr; apply ne_of_gt
    simp only [e.F_lt_C_on_l]
  haveI C_ne_F : PtNe e.C e.F := ⟨C_ne_F'⟩
  have CA_eq_FD : (SEG e.C e.A).length = (SEG e.F e.D).length := by
    calc
    _= (SEG e.A e.C).length := by apply length_of_rev_eq_length'
    _= (SEG e.A e.F).length + (SEG e.F e.C).length := by
      apply length_eq_length_add_length
      apply Seg.lies_on_of_lies_int
      exact F_int_AC
    _= (SEG e.D e.C).length + (SEG e.C e.F).length := by congr 1; exact e.AF_eq_DC; exact length_of_rev_eq_length'
    _= (SEG e.D e.F).length := by
      symm; apply length_eq_length_add_length
      apply Seg.lies_on_of_lies_int
      exact C_int_DF
    _=_ := by apply length_of_rev_eq_length'
  have angle_ACB_eq_angle_DFE : (∠ e.A e.C e.B) = (∠ e.D e.F e.E) := by
    have dir_CA_eq_neg_dir_FD : (RAY e.C e.A).toDir = - (RAY e.F e.D).toDir := by
      calc
      _= - e.l.toDir := by
        apply DirLine.neg_toDir_of_gt e.C_on_l e.A_on_l
        calc
        (⟨e.A, e.A_on_l⟩ : e.l.carrier.Elem)
        _< ⟨e.F, e.F_on_l⟩ := e.A_lt_F_on_l
        _< ⟨e.C, e.C_on_l⟩ := e.F_lt_C_on_l
      _=_ := by
        simp only [neg_inj]; symm
        apply DirLine.eq_toDir_of_lt e.F_on_l e.D_on_l
        calc
        (⟨e.F, e.F_on_l⟩ : e.l.carrier.Elem)
        _< ⟨e.C, e.C_on_l⟩ := e.F_lt_C_on_l
        _< ⟨e.D, e.D_on_l⟩ := e.C_lt_D_on_l
    have dir_CB_eq_neg_dir_FE : (RAY e.C e.B).toDir = - (RAY e.F e.E).toDir := by
      have h : IsOnOppositeSide e.B e.E (SEG_nd e.C e.F) := by
        have h1 : (SEG_nd e.C e.F).toLine = e.l := by
          calc
          _= (LIN e.C e.F) := by
            symm;
            apply Line.eq_line_of_pt_pt_of_ne
            apply SegND.lies_on_toLine_of_lie_on; exact SegND.source_lies_on
            apply SegND.lies_on_toLine_of_lie_on; exact SegND.target_lies_on
          _=_ := by
            apply Line.eq_line_of_pt_pt_of_ne
            exact e.C_on_l
            exact e.F_on_l
        have h2 : IsOnOppositeSide e.B e.E (SEG_nd e.C e.F) = IsOnOppositeSide e.B e.E e.l := by
          calc
          _= IsOnOppositeSide e.B e.E (SEG_nd e.C e.F).toLine := by rfl
          _=_ := by congr
        simp only [h2]; exact e.B_E_IsOnOppositeSide_l
      apply neg_toDir_of_parallel_and_IsOnOppositeSide
      · exact e.CB_parallel_FE
      · exact h
    apply ang_eq_ang_of_toDir_eq_neg_toDir
    · exact dir_CA_eq_neg_dir_FD
    · exact dir_CB_eq_neg_dir_FE
  have triangle_BCA_congr_triangle_EFD : (TRI_nd e.B e.C e.A e.not_collinear_BCA) ≅ (TRI_nd e.E e.F e.D e.not_collinear_EFD) := by
    apply TriangleND.congr_of_ASA
    · exact angle_ACB_eq_angle_DFE
    · exact CA_eq_FD
    · exact e.angle_BAC_eq_angle_EDF
  exact triangle_BCA_congr_triangle_EFD.edge₂
end Problem_5

end EuclidGeom
