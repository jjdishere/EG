import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom
namespace ShanZun

namespace Shan_Problem_2_21

/- In a parallelogram ABCD, E and F lies on the segment AC, and $AE=FC$
Prove that $DE\parallel BF$ -/
structure Setting (Plane : Type*) [EuclideanPlane Plane] where
  -- Let $ ABCD$ be a nontrivial parallelogram
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  -- Claim :$B \ne A$
  B_ne_A : B ≠ A
  -- Claim :$C \ne A$
  C_ne_A : C ≠ A
  -- Claim :$D \ne A$
  D_ne_A : D ≠ A
  -- Claim $C \ne B$
  C_ne_B : C ≠ B
  -- Claim $D \ne B$
  D_ne_B : D ≠ B
  -- Claim $D \ne C$
  D_ne_C : D ≠ C
  -- $ABCD$ is a parallelogram
  hABCD : QDR A B C D IsPRG
  -- $E$ is a point lies in $AC$
  E : Plane
  hE : E LiesInt (SEG_nd A C C_ne_A)
  -- $F$ is a point lies in $AC$
  F : Plane
  hF : F LiesInt (SEG_nd A C C_ne_A)
  -- $AE=FC$
  hEF : (SEG A E).length = (SEG F C).length
  -- Claim $E \ne A$
  E_ne_A : E ≠ A := sorry
  -- Claim $E \ne B$
  E_ne_B : E ≠ B := sorry
  -- Claim $F \ne B$
  F_ne_B : F ≠ B := sorry
  -- Claim $F \ne C$
  F_ne_C : F ≠ C := sorry
  -- Claim $E \ne D$
  E_ne_D : E ≠ D := sorry
  -- Claim $F \ne D$
  F_ne_D : F ≠ D := sorry


-- $DE \parallel BF $
theorem result {Plane : Type*} [EuclideanPlane Plane] (e : Setting Plane) : (LIN e.D e.E e.E_ne_D) ∥ (LIN e.B e.F e.F_ne_B):= by

  -- $\ang BAE=\ang DCF$
  have ang_BAE_eq_ang_DCF : ∠ e.B e.A e.E e.B_ne_A e.E_ne_A = ∠ e.D e.C e.F e.D_ne_C e.F_ne_C := sorry
  -- $▵ABE≅▵CDF$ by SAS
  have ABE_congr_CDF: TRI e.A e.B e.E ≅ TRI e.C e.D e.F := sorry
  -- $∠ AEB = ∠ CFD$
  have ang_AEB_eq_ang_CFD : ∠ e.A e.E e.B e.E_ne_A.symm e.E_ne_B.symm = ∠ e.C e.F e.D e.F_ne_C.symm e.F_ne_D.symm := sorry
  -- The alternate angles are the same
  sorry
end Shan_Problem_2_21

namespace Shan_Problem_2_23
/- In a parallelogram ABCD, E is the midpoint of the segment BC, and F is the midpoint of the segment AD. Let G, H be the intersection of AC with BF and DE respectively.
Prove that $AG=GH=HC$ -/
structure Setting (Plane : Type*) [EuclideanPlane Plane] where
  -- Let $ ABCD$ be a nontrivial parallelogram
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  -- Claim :$B \ne A$
  B_ne_A : B ≠ A
  -- Claim :$C \ne A$
  C_ne_A : C ≠ A
  -- Claim :$D \ne A$
  D_ne_A : D ≠ A
  -- Claim $C \ne B$
  C_ne_B : C ≠ B
  -- Claim $D \ne B$
  D_ne_B : D ≠ B
  -- Claim $D \ne C$
  D_ne_C : D ≠ C
  -- $ABCD$ is a parallelogram
  hABCD : QDR A B C D IsPRG
  --$E$ is the midpoint of $BC$
  E : Plane
  hE : E = (SEG B C).midpoint
  --$F$ is the midpoint of $AD$
  F : Plane
  hF : F = (SEG A D).midpoint
  --Claim $E \ne D$
  E_ne_D : E ≠ D := sorry
  --Claim $F \ne B$
  F_ne_B : F ≠ B := sorry
  -- $AC$ intersects with $BF$ at point $G$
  G : Plane
  hG : is_inx G (LIN A C C_ne_A) (LIN B F F_ne_B)
  --$AC$ intersects with $DE$ at point $H$
  H : Plane
  hH : is_inx H (LIN A C C_ne_A) (LIN D E E_ne_D)

--The pair of points (G,H) divides the segement AC into three segments with the same length.
theorem result {Plane : Type*} [EuclideanPlane Plane] (e : Setting Plane) :(SEG e.A e.G).length=(SEG e.G e.H).length ∧ (SEG e.A e.G).length=(SEG e.H e.C).length := by
  -- $▵AFG$ is nontrivial
  have AFG_nd : ¬ Collinear e.A e.F e.G := sorry
  -- $▵CBG$ is nontrivial
  have CBG_nd : ¬ Collinear e.C e.B e.G :=sorry
  -- $▵ AFG ∼ ▵ CBG$ with ratio 1/2 by AAA
  have AFG_sim_CBG : (TRI_nd e.A e.F e.G AFG_nd) ∼ (TRI_nd e.C e.B e.G CBG_nd) := sorry
--The following three may not be necessary since we can use the above three lemmas instead

  have CEH_nd : ¬ Collinear e.C e.E e.H := sorry
  have ADH_nd : ¬ Collinear e.A e.D e.H := sorry
  -- $▵ CEH ∼ ▵ ADH$ with ratio 1/2 by AAA
  have CEH_sim_ADH : (TRI_nd e.C e.E e.H CEH_nd) ∼ (TRI_nd e.A e.D e.H ADH_nd) := sorry
  -- length of segment AG is half of segment CG
  have AG_eq_half_of_CG : (SEG e.A e.G).length = (SEG e.C e.G).length/2 := sorry
  -- length of segment CH is half of segment AH
  have CH_eq_half_of_AH : (SEG e.C e.H).length = (SEG e.A e.H).length/2 := sorry
  -- The pair of points (G,H) divides the segement AC into three segments with the same length.
  sorry

end Shan_Problem_2_23
end ShanZun
end EuclidGeom
