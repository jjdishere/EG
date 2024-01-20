import EuclideanGeometry.Foundation.Index

noncomputable section


namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

namespace Shan_Problem_2_11
/- Let $\triangle ABC$ be a regular triangle,
Let $E$ be a point on the extension of $BA$ and $D$ a point on the extension of $BC$
such that $AE = BD$, connect $CE,DE$
Prove that $CE = DE$ -/

structure Setting1  (Plane : Type*) [EuclideanPlane Plane] where
-- Let $\triangle ABC$ be a regular triangle
  A : Plane
  B : Plane
  C : Plane
  hnd : ¬ Collinear A B C
  hreg : (▵ A B C).IsRegular
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
instance A_ne_B {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.A e.B := ⟨(ne_of_not_collinear e.hnd).2.2.symm⟩
instance B_ne_C {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.B e.C := ⟨(ne_of_not_collinear e.hnd).1.symm⟩
instance C_ne_A {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.C e.A := ⟨(ne_of_not_collinear e.hnd).2.1.symm⟩

structure Setting2 (Plane : Type*) [EuclideanPlane Plane] extends Setting1 Plane where
-- Let $E$ be a point on the extension of $BA$ and $D$ a point on the extension of $BC$
  D : Plane
  E : Plane
  hd : D LiesInt (SEG_nd B C).extension
  he : E LiesInt (SEG_nd B A).extension
-- We have $AE = BD$
  h : (SEG A E).length = (SEG B D).length

-- Theorem : $CE = DE$
theorem Result {Plane : Type*} [EuclideanPlane Plane] {e : Setting2 Plane} : (SEG e.C e.E).length = (SEG e.D e.E).length := by
/-
  Extend $BD$ to $F$ such that $DF = BC$.
  Then $BF = BD + DF = AE + AB = BE$, and $\angle FBE = 60^{\circ}$  or $-60^{\circ}$.
  So $\triangle EBF$ is regular, $EF = EB$, $\angle EBC = - \angle EFD$.
  Thus $\triangle BEC$ is anti-congruence to $\triangle FED$ by SAS.
  Therefore $CE = DE$
-/
  -- Claim: $D \ne B$, $E \ne B$
  haveI D_ne_B : PtNe e.D e.B := sorry
  haveI E_ne_B : PtNe e.E e.B := sorry
  -- Extend $BD$ to $F$ such that $DF = CB$
  let e.F := Ray.extpoint (SEG_nd e.B e.D).extension (SEG e.B e.C).length
  have DF_eq_CB : (SEG e.D e.F).length = (SEG e.C e.B).length := by
    calc
      -- $DF = BC$ from defination of $F$
      _ = (SEG e.B e.C).length := by
        apply Ray.dist_of_extpoint (r := (SEG_nd e.B e.D).extension)
        exact Seg.length_nonneg
      -- $BC = CB$ by symmetry
      _ = (SEG e.C e.B).length := by
        simp only [length_of_rev_eq_length']
  -- Claim: $F \ne B$, $D \ne F$, $E \ne F$
  haveI F_ne_B : PtNe e.F e.B := sorry
  haveI D_ne_F : PtNe e.D e.F := sorry
  haveI E_ne_F : PtNe e.E e.F := sorry
  -- $F$ lies in extension of $BD$
  have F_int_BD_extn : e.F LiesInt (SEG_nd e.B e.D).extension := by
    apply Ray.lies_int_of_eq_pos_extpoint (t := (SEG e.B e.C).length)
    apply (SEG_nd e.B e.C).length_pos
    simp only [Seg.length_eq_dist]
  -- $D$ lies on $BF$ because $F$ lies on extension of $BD$
  have D_on_BF : e.D LiesOn (SEG_nd e.B e.F) :=  SegND.lies_on_of_lies_int (SegND.target_lies_int_seg_source_pt_of_pt_lies_int_extn F_int_BD_extn)
  -- $C$ lies on $BF$ because $C$ lies on $BD$ and $D$ lies on $BF$
  --这个sorry应该是一些linear Order的东西
  have C_on_BF : e.C LiesOn (SEG_nd e.B e.F) := sorry
  -- $A$ lies on $BE$ because $E$ lies on exxtension of $BA$
  have A_on_BE : e.A LiesOn (SEG_nd e.B e.E) := SegND.lies_on_of_lies_int (SegND.target_lies_int_seg_source_pt_of_pt_lies_int_extn e.he)
  -- $F$ lies on ray $BC$ because $C$ lies on $BF$
  have C_on_ray_BF : e.C LiesOn (RAY e.B e.F) := SegND.lies_on_toRay_of_lies_on C_on_BF
  -- $E$ lies on ray $BA$ because $A$ lies on $BE$
  have A_on_ray_BE : e.A LiesOn (RAY e.B e.E) := SegND.lies_on_toRay_of_lies_on A_on_BE
  -- $B$ lies on ray $FD$ because $F$ lies on ray $BD$
  have B_on_ray_FD : e.B LiesOn (RAY e.F e.D) := sorry
  -- $BF = BD + DF = AE + AB = BE$
  have BF_eq_BE : (SEG e.B e.F).length = (SEG e.B e.E).length := by
    calc
      -- $BF = BD + DF$ because $D$ lies on $BF$
      _ = (SEG e.B e.D).length + (SEG e.D e.F).length := by
        exact length_eq_length_add_length D_on_BF
      -- $BD + DF = BD + BC$ because $DF = BC$ by the construction of $F$
      _ = (SEG e.B e.D).length + (SEG e.B e.C).length := by
        simp only [length_of_rev_eq_length', DF_eq_CB]
      -- $BD + BC = AE + BC$ because $BD = AE$
      _ = (SEG e.A e.E).length + (SEG e.B e.C).length := by rw [e.h]
      -- $AE + BC = AE + AB$ because $BC = AB$ by $\triangle ABC$ is regular
      _ = (SEG e.A e.E).length + (SEG e.A e.B).length := by
        have AB_eq_BC : (SEG e.B e.C).length = (SEG e.A e.B).length := e.hreg.2
        rw[AB_eq_BC]
      -- $AE + AB = BA + AE$ by symmetry
      _ = (SEG e.B e.A).length + (SEG e.A e.E).length := by
        simp only [length_of_rev_eq_length', add_comm]
      -- $BA + AE = BE$ because $A$ lies on $BE$
      _ = (SEG e.B e.E).length := by
        exact (length_eq_length_add_length A_on_BE).symm
  -- $\angle EBF = \angle ABC$ because they are the same angle
  have ang_EBF_eq_ang_ABC : ∠ e.F e.B e.E = ∠ e.C e.B e.A := (Angle.value_eq_of_lies_on_ray_pt_pt C_on_ray_BF A_on_ray_BE).symm
  -- $\angle FBE = \frac{\pi}{3}$ or $ - \frac{\pi}{3}$ because $\angle FBE = -\angle EBF = -\angle ABC$
  have ang_EBF_eq_sixty : ∠ e.F e.B e.E = ↑ (π / 3) ∨  ∠ e.F e.B e.E = ↑ (- π / 3) := by
    by_cases h₁ : (TRI_nd e.A e.B e.C e.hnd).is_cclock
    have sixty₁ : ∠ e.C e.B e.A = ↑ (π / 3) := (ang_eq_sixty_deg_of_cclock_regular_tri (TRI_nd e.A e.B e.C e.hnd) h₁ e.hreg).2.1
    rw[← ang_EBF_eq_ang_ABC] at sixty₁
    left
    exact sixty₁
    have sixty₂ : ∠ e.C e.B e.A = ↑ (- π / 3) := (ang_eq_sixty_deg_of_acclock_regular_tri (TRI_nd e.A e.B e.C e.hnd) h₁ e.hreg).2.1
    rw[← ang_EBF_eq_ang_ABC] at sixty₂
    right
    exact sixty₂
  -- $BFE$ is not collinear because $\angle FBE = \frac{\pi}{3}$ or $ - \frac{\pi}{3}$
  have BFE_not_collinear : ¬ Collinear e.B e.F e.E := sorry
  have BEF_not_collinear : ¬ Collinear e.B e.E e.F := sorry
  -- $\triangle BFE$ is regular because $BF = EB$ and $\angle FBE = \frac{\pi}{3}$ or $ - \frac{\pi}{3}$
  have BFE_is_regular : (TRI_nd e.B e.F e.E BFE_not_collinear).1.IsRegular := by
    apply regular_tri_of_isoceles_tri_of_fst_ang_eq_sixty_deg
    exact ang_EBF_eq_sixty
    rw[← Seg.length_of_rev_eq_length (seg := (SEG e.B e.E))] at BF_eq_BE
    exact BF_eq_BE.symm
  -- $\angle FBE = - \angle EFB$ because $\triangle BFE$ is regular
  have ang_FBE_eq_ang_EFB : ∠ e.F e.B e.E = ∠ e.E e.F e.B := ((regular_tri_iff_eq_angle_of_nd_tri (TRI_nd e.B e.F e.E BFE_not_collinear)).mp BFE_is_regular).1
  -- $\angle EBC = - \angle EFD$ because $\triangle BFE$ is regular
  have ang_EBC_eq_neg_ang_EFD : ∠ e.E e.B e.C = - ∠ e.E e.F e.D := by
    calc
    --$\angle EBC = \ange EBF$ because they are the same angle
    _ = ∠ e.E e.B e.F := by
      have E_on_ray_BE : e.E LiesOn (SEG_nd e.B e.E).toRay := SegND.lies_on_toRay_of_lies_on SegND.target_lies_on
      exact Angle.value_eq_of_lies_on_ray_pt_pt E_on_ray_BE C_on_ray_BF
    --$\angle EBF = - \angle FBE$ by reverse
    _ = - ∠ e.F e.B e.E := by
      rw[← Angle.rev_value_eq_neg_value (ang := (ANG e.F e.B e.E))]
      constructor
    --$\angle FBE = - \angle EFB$ by the lemma above
    _ = - ∠ e.E e.F e.B := by
      simp only[ang_FBE_eq_ang_EFB]
    --$- \angle EFB = \angle BFE$ by reverse
    _ = ∠ e.B e.F e.E := by
      rw[← Angle.rev_value_eq_neg_value (ang := (ANG e.E e.F e.B))]
      constructor
    --$\angle BFE = \ange DFE$ because they are the same angle
    _ = ∠ e.D e.F e.E := by
      have E_on_ray_FE : e.E LiesOn (SEG_nd e.F e.E).toRay := SegND.lies_on_toRay_of_lies_on SegND.target_lies_on
      exact Angle.value_eq_of_lies_on_ray_pt_pt B_on_ray_FD E_on_ray_FE
    --$\angle DFE = - \angle EFD$ by reverse
    _ = - ∠ e.E e.F e.D := by
      rw[← Angle.rev_value_eq_neg_value (ang := (ANG e.E e.F e.D))]
      constructor
  -- $FE = BE$ because $\triangle BFE$ is regular
  have FE_eq_BE : (SEG e.F e.E).length = (SEG e.B e.E).length := by
    calc
    -- $FE = EB$ because $\triangle BFE$ is regular
    _ = (SEG e.E e.B).length := by
      exact BFE_is_regular.1
    -- $EB = BE$ by symmetry
    _ = (SEG e.B e.E).length := by
      simp only [length_of_rev_eq_length']
  -- $BEC$ is not collinear and $FED$ is not collinear
  have BEC_not_collinear : ¬ Collinear e.B e.E e.C := sorry
  have FED_not_collinear : ¬ Collinear e.F e.E e.D := sorry
  -- $\triangle BCE$ is anti-congruence to $\triangle FDE$
  have cong : (TRI_nd e.B e.E e.C BEC_not_collinear) ≅ₐ (TRI_nd e.F e.E e.D FED_not_collinear) := TriangleND.acongr_of_SAS DF_eq_CB.symm ang_EBC_eq_neg_ang_EFD FE_eq_BE.symm
  -- $EC = ED$ because $\triangle BCE \cong \triangle FDE$
  have EC_eq_ED : (SEG e.E e.C).length = (SEG e.E e.D).length := cong.edge₁
  rw[length_of_rev_eq_length', EC_eq_ED]
  simp only [length_of_rev_eq_length']
end Shan_Problem_2_11

namespace Shan_Problem_2_22
/- In $\triangle ABC$, $D$ is midpoint of $BA$, $E$ us midpoint of $BC$,
$F,G$ are points of trisection of $AC$,
line $DF$ and $EG$ intersect at $H$
Prove that quadrilateral $ABCH$ is parallelogram -/

structure Setting1  (Plane : Type*) [EuclideanPlane Plane] where
-- We have triangle $\triangle ABC$
  A : Plane
  B : Plane
  C : Plane
  hnd : ¬ Collinear A B C
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
instance A_ne_B {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.A e.B := ⟨(ne_of_not_collinear e.hnd).2.2.symm⟩
instance B_ne_C {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.B e.C := ⟨(ne_of_not_collinear e.hnd).1.symm⟩
instance C_ne_A {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.C e.A := ⟨(ne_of_not_collinear e.hnd).2.1.symm⟩

structure Setting2 (Plane : Type*) [EuclideanPlane Plane] extends Setting1 Plane where
-- $D$ is midpoint of $BA$, $E$ is midpoint of $BC$
  D : Plane
  E : Plane
  hd : D = (SEG B A).midpoint
  he : E = (SEG B C).midpoint
-- $F,G$ are points of trisection of $AC$
  F : Plane
  G : Plane
  hf : F LiesInt (SEG_nd A C)
  hg : G LiesInt (SEG_nd A C)
  htri : (SEG A F).length = (SEG F G).length ∧ (SEG F G).length = (SEG G C).length
-- Claim: $F \ne D$ and $G \ne E$
instance F_ne_D {Plane : Type*} [EuclideanPlane Plane] {e : Setting2 Plane} : PtNe e.F e.D := ⟨sorry⟩
instance G_ne_E {Plane : Type*} [EuclideanPlane Plane] {e : Setting2 Plane} : PtNe e.G e.E := ⟨sorry⟩

structure Setting3 (Plane : Type*) [EuclideanPlane Plane] extends Setting2 Plane where
-- $H$ is the intersection of line $DF$ and $EG$
  H : Plane
  hh : is_inx H (LIN D F) (LIN E G)

-- Theorem : quadrilateral $ABCH$ is parallelogram
theorem Result {Plane : Type*} [EuclideanPlane Plane] {e : Setting3 Plane} : QDR e.A e.B e.C e.H IsPRG := sorry

end Shan_Problem_2_22

namespace Shan_Problem_2_36
/- In $\triangle ABC$, $D,E$ are points in $AB,AC$ respectively,
such that $DE \parallel BC$,
$F,G$ are points lies on line $BC$,
such that $FB = CG$ and $AF \parallel BE$ ,
Prove that $AG \parallel DC$-/

structure Setting1  (Plane : Type*) [EuclideanPlane Plane] where
-- We have triangle $\triangle ABC$
  A : Plane
  B : Plane
  C : Plane
  hnd : ¬ Collinear A B C
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
instance A_ne_B {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.A e.B := ⟨(ne_of_not_collinear e.hnd).2.2.symm⟩
instance B_ne_C {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.B e.C := ⟨(ne_of_not_collinear e.hnd).1.symm⟩
instance C_ne_A {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.C e.A := ⟨(ne_of_not_collinear e.hnd).2.1.symm⟩

structure Setting2 (Plane : Type*) [EuclideanPlane Plane] extends Setting1 Plane where
-- $D,E$ are points in $AB,AC$ respectively
  D : Plane
  E : Plane
  hd : D LiesInt (SEG_nd A B)
  he : E LiesInt (SEG_nd A C)
-- $F,G$ are points lies on line $BC$
  F : Plane
  G : Plane
  hf : F LiesOn (LIN B C)
  hg : G LiesOn (LIN B C)
-- We have $FB = CG$
  hedge : (SEG F B).length = (SEG C G).length
-- Claim : $F \ne A$ and $E \ne B$
instance F_ne_A {Plane : Type*} [EuclideanPlane Plane] {e : Setting2 Plane} : PtNe e.F e.A := ⟨sorry⟩
instance E_ne_B {Plane : Type*} [EuclideanPlane Plane] {e : Setting2 Plane} : PtNe e.E e.B := ⟨sorry⟩

structure Setting3 (Plane : Type*) [EuclideanPlane Plane] extends Setting2 Plane where
-- We have $AF \parallel BE$
  hpara : (SEG_nd A F) ∥ (SEG_nd B E)
-- Claim: $G \ne A$ and $D \ne C$
instance G_ne_A {Plane : Type*} [EuclideanPlane Plane] {e : Setting3 Plane} : PtNe e.G e.A := ⟨sorry⟩
instance D_ne_C {Plane : Type*} [EuclideanPlane Plane] {e : Setting3 Plane} : PtNe e.D e.C := ⟨sorry⟩

-- Theorem : $AG \parallel DC$
theorem Result {Plane : Type*} [EuclideanPlane Plane] {e : Setting3 Plane} : (SEG_nd e.A e.G) ∥ (SEG_nd e.C e.D) := sorry

end Shan_Problem_2_36

namespace Shan_Problem_2_37
/- In $\triangle ABC$
$\angle BAC = \pi / 4$,
$BE, CF$ are heights,
such that $AE = 2 EC$
Prove that $AF = 3 FB$ -/

structure Setting1  (Plane : Type*) [EuclideanPlane Plane] where
-- We have acute triangle $\triangle ABC$
  A : Plane
  B : Plane
  C : Plane
  hnd : ¬ Collinear A B C
  hacute : TriangleND.IsAcute (TRI_nd A B C hnd)
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
instance A_ne_B {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.A e.B := ⟨(ne_of_not_collinear e.hnd).2.2.symm⟩
instance B_ne_C {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.B e.C := ⟨(ne_of_not_collinear e.hnd).1.symm⟩
instance C_ne_A {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.C e.A := ⟨(ne_of_not_collinear e.hnd).2.1.symm⟩

structure Setting2 (Plane : Type*) [EuclideanPlane Plane] extends Setting1 Plane where
-- $D,E$ are points in $AB,AC$ respectively
  E : Plane
  F : Plane
  he : E = perp_foot B (LIN A C)
  hf : F = perp_foot C (LIN A B)
-- We have $AE = 2 EC$
  h : (SEG A E).length = 2 * (SEG E C).length

-- Theorem : $AF = 3 FB$
theorem Result {Plane : Type*} [EuclideanPlane Plane] {e : Setting2 Plane} : (SEG e.A e.F).length = 3 * (SEG e.F e.B).length := sorry

end Shan_Problem_2_37

namespace Shan_Problem_2_38
/- In $\triangle ABC$, $D$ is the midpoint of $BC$,
let the angle bisectors of $\angle ADB$ and $\angle ADC$ intersect $AB$ and $AC$ at $E,F$,
Prove that $EF \parallel BC$-/

structure Setting1  (Plane : Type*) [EuclideanPlane Plane] where
-- We have triangle $\triangle ABC$
  A : Plane
  B : Plane
  C : Plane
  hnd : ¬ Collinear A B C
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
instance A_ne_B {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.A e.B := ⟨(ne_of_not_collinear e.hnd).2.2.symm⟩
instance B_ne_C {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.B e.C := ⟨(ne_of_not_collinear e.hnd).1.symm⟩
instance C_ne_A {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.C e.A := ⟨(ne_of_not_collinear e.hnd).2.1.symm⟩

structure Setting2 (Plane : Type*) [EuclideanPlane Plane] extends Setting1 Plane where
-- $D$ is the midpoint of $BC$
  D : Plane
  hd : D = (SEG B C).midpoint
-- Claim: $A \ne D$ and $B \ne D$ and $C \ne D$
instance A_ne_D {Plane : Type*} [EuclideanPlane Plane] {e : Setting2 Plane} : PtNe e.A e.D := ⟨sorry⟩
instance B_ne_D {Plane : Type*} [EuclideanPlane Plane] {e : Setting2 Plane} : PtNe e.B e.D := ⟨sorry⟩
instance C_ne_D {Plane : Type*} [EuclideanPlane Plane] {e : Setting2 Plane} : PtNe e.C e.D := ⟨sorry⟩

structure Setting3 (Plane : Type*) [EuclideanPlane Plane] extends Setting2 Plane where
-- let the angle bisectors of $\angle ADB$ and $\angle ADC$ intersect $AB$ and $AC$ at $E,F$
  E : Plane
  F : Plane
  he : is_inx E (ANG A D B).AngBis (SEG A B)
  hf : is_inx F (ANG A D C).AngBis (SEG A C)
-- Claim: $F \ne E$
instance F_ne_E {Plane : Type*} [EuclideanPlane Plane] {e : Setting3 Plane} : PtNe e.F e.E := ⟨sorry⟩

-- Theorem : $EF \parallel BC$
theorem Result {Plane : Type*} [EuclideanPlane Plane] {e : Setting3 Plane} : (SEG_nd e.E e.F) ∥ (SEG_nd e.B e.C) := sorry

end Shan_Problem_2_38

namespace Shan_Problem_2_42
/- In $\triangle ABC$, $D$ is the midpoint of $AB$,
$E$ lies on $AC$ such that $AE = 2 CE$,
$CD,BE$ intersects at $O$
Prove that $OE = \frac{1}{4} BE$-/

structure Setting1  (Plane : Type*) [EuclideanPlane Plane] where
-- We have triangle $\triangle ABC$
  A : Plane
  B : Plane
  C : Plane
  hnd : ¬ Collinear A B C
-- $D$ is midpoint of $AB$
  D : Plane
  hd : D = (SEG A B).midpoint
-- $E$ lies on $AC$ such that $AE = 2 CE$
  E : Plane
  he : E LiesInt (SEG A C) ∧ (SEG A E).length = 2 * (SEG C E).length
-- $CD,BE$ intersects at $O$
  O : Plane
  ho : is_inx O (SEG C D) (SEG B E)

-- Theorem : $OE = \frac{1}{4} BE$
theorem Result {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : (SEG e.O e.E).length = (1 / 4) * (SEG e.B e.E).length := sorry

end Shan_Problem_2_42

namespace Shan_Problem_2_43
/- In $\triangle ABC$, $E,F$ lies on $AB$ such that $AE = FB$,
The parallel line to $AC$ of $E,F$ intersect $BC$ at $G,H$ respectively,
Prove that $EG + FH = AC$-/

structure Setting1  (Plane : Type*) [EuclideanPlane Plane] where
-- We have triangle $\triangle ABC$
  A : Plane
  B : Plane
  C : Plane
  hnd : ¬ Collinear A B C
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
instance A_ne_B {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.A e.B := ⟨(ne_of_not_collinear e.hnd).2.2.symm⟩
instance B_ne_C {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.B e.C := ⟨(ne_of_not_collinear e.hnd).1.symm⟩
instance C_ne_A {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.C e.A := ⟨(ne_of_not_collinear e.hnd).2.1.symm⟩

structure Setting2 (Plane : Type*) [EuclideanPlane Plane] extends Setting1 Plane where
-- $E,F$ lies on $AB$ such that $AE = FB$
  E : Plane
  F : Plane
  he : E LiesInt (SEG A B)
  hf : F LiesInt (SEG A B)
  hef : (SEG A E).length = (SEG F B).length
-- 此处以后可能会专门加上过一个点做平行线的定义,从而更改条件的叙述
-- $l_1,l_2$ are parallel lines to $AC$ of $E,F$ respectively
  l₁ : Line Plane
  l₂ : Line Plane
  hl₁ : l₁ ∥ (SEG_nd A C) ∧ E LiesOn l₁
  hl₂ : l₂ ∥ (SEG_nd A C) ∧ F LiesOn l₂
-- $l_1,l_2$ intersect $BC$ at $G,H$ respectively
  G : Plane
  H : Plane
  hg : is_inx G l₁ (SEG B C)
  hh : is_inx H l₂ (SEG B C)

-- Theorem : $EG + FH = AC$
theorem Result {Plane : Type*} [EuclideanPlane Plane] {e : Setting2 Plane} : (SEG e.E e.G).length + (SEG e.F e.H).length = (SEG e.A e.C).length := sorry

end Shan_Problem_2_43

namespace Shan_Problem_2_44
/- $A,B,C$ are points on line $l$ such that $\frac{AB}{BC} = \frac{m}{n}$,
$A₁,B₁,C₁$ are points on line $l₁$ such that $AA₁ \parallel BB₁ \parallel CC₁$.
Prove that $BB₁ = \frac{n}{m+n} AA₁ + \frac{m}{m+n} CC₁$-/

structure Setting1  (Plane : Type*) [EuclideanPlane Plane] where
-- We have line $l$ and points $A,B,C$ lies on $l
  l : Line Plane
  A : Plane
  B : Plane
  C : Plane
  ha : A LiesOn l
  hb : B LiesOn l
  hc : C LiesOn l
-- We have $\frac{AB}{BC} = \frac{m}{n}$
  m : ℝ
  n : ℝ
  hpos : m > 0 ∧ n > 0
  hratio : (SEG A B).length / (SEG B C).length = m / n
-- We have line $l₁$ and points $A₁,B₁,C₁$ lies on $l₁$
  l₁ : Line Plane
  A₁ : Plane
  B₁ : Plane
  C₁ : Plane
  ha₁ : A₁ LiesOn l₁
  hb₁ : B₁ LiesOn l₁
  hc₁ : C₁ LiesOn l₁
-- We have $A \ne A₁$, $B \ne B₁$, $C \ne C₁$ and $AA₁ \parallel BB₁ \parallel CC₁$
  nea : PtNe A A₁
  neb : PtNe B B₁
  nec : PtNe C C₁
  hpara₁ : (SEG_nd A A₁) ∥ (SEG_nd B B₁)
  hpara₂ : (SEG_nd B B₁) ∥ (SEG_nd C C₁)

-- Theorem : $BB₁ = \frac{n}{m+n} AA₁ + \frac{m}{m+n} CC₁$
theorem Result {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : (SEG e.B e.B₁).length = (e.n / (e.m+e.n)) * (SEG e.A e.A₁).length + (e.m/(e.m+e.n)) * (SEG e.C e.C₁).length := sorry

end Shan_Problem_2_44

namespace Shan_Problem_2_48
/- $ABCD$ are convex quadrilateral, $AC$ and $BD$ intersect at $E$,
Prove that area of $\triangle ABD$ : area of $\triangle CBD = AE : CE$  -/

structure Setting1  (Plane : Type*) [EuclideanPlane Plane] where
-- We have convex quadrilateral $ABCD$
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  hcvx : (QDR A B C D) IsConvex
-- $AD$ and $BC$ intersect at $E$
  E : Plane
  he : is_inx E (SEG A D) (SEG B C)


-- Theorem : area of $\triangle ABC :$ area of $\triangle DBC = AE : DE$
theorem Result {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : Triangle.area (▵ e.A e.B e.D) / Triangle.area (▵ e.C e.B e.D) = (SEG e.A e.E).length / (SEG e.D e.E).length := sorry

end Shan_Problem_2_48

namespace Shan_Problem_2_52
/- $AD$ is the height of hypotenuse $BC$ of right triangle $\triangle ABC$,
the angle bisector of $\angle ABC$ intersect $AD$ and $AC$ at $M,N$ respectively,
Prove that $AB^2 - AN^2 = BM \times BN$-/

structure Setting1  (Plane : Type*) [EuclideanPlane Plane] where
-- Let triangle $\triangle ABC$
  A : Plane
  B : Plane
  C : Plane
  hnd : ¬ Collinear A B C
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
instance A_ne_B {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.A e.B := ⟨(ne_of_not_collinear e.hnd).2.2.symm⟩
instance B_ne_C {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.B e.C := ⟨(ne_of_not_collinear e.hnd).1.symm⟩
instance C_ne_A {Plane : Type*} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.C e.A := ⟨(ne_of_not_collinear e.hnd).2.1.symm⟩

structure Setting2 (Plane : Type*) [EuclideanPlane Plane] extends Setting1 Plane where
--$\triangle ABC$ is a right triangle with $\angle BAC = 90^{circ}$
  hright : ∠ B A C = ↑ (π / 2)
-- $AD$ is the height of $\triangle ABC$
  D : Plane
  hd : D = perp_foot A (LIN B C)
-- the angle bisector of $\angle ABC$ intersect $AD$ and $AC$ at $M,N$ respectively
  l : Ray Plane
  M : Plane
  N : Plane
  hl : l = (ANG A B C).AngBis
  hm : is_inx M (SEG A D) l
  hn : is_inx N (SEG A C) l

-- Theorem : $AB^2 - AN^2 = BM \times BN$
theorem Result {Plane : Type*} [EuclideanPlane Plane] {e : Setting2 Plane} : (SEG e.A e.B).length * (SEG e.A e.B).length - (SEG e.A e.N).length * (SEG e.A e.N).length = (SEG e.B e.M).length * (SEG e.B e.N).length := sorry

end Shan_Problem_2_52
