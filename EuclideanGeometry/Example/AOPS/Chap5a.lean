import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from AOPS Geometry book Chapter 5

namespace EuclidGeom
namespace AOPS
variable {P : Type*} [EuclideanPlane P]

namespace AOPS_Problem_5_7
/- Let $\triangle ABC$ be a triangle, and let $D$, $E$ be two points in the interior of $AB$ and $AC$ respectively such that $DE\parallel BC$ . $X$ lies inside $AB$ and $Y$ lies on the ray $XE$ so that $AY\parallel XC$

Prove that $\frac{EY}{EX}=\frac{AD}{DB}$ -/

structure Setting (Plane : Type*) [EuclideanPlane Plane] where
  -- Let $\triangle ABC$ be a nontrivial triangle
  A : Plane
  B : Plane
  C : Plane
  not_collinear_ABC : ¬ Collinear A B C
  -- Claim :$C \ne A$
  B_ne_A : B ≠ A :=
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.2
  C_ne_A : C ≠ A :=
    -- This is because vertices $A, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.1.symm
  -- Claim $B \ne C$
  C_ne_B : C ≠ B :=
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).1

  --D lies in AB and E lies in AE
  D : Plane
  hD : D LiesInt (SEG_nd A B B_ne_A)
  E : Plane
  hE : E LiesInt (SEG_nd A C C_ne_A)
  -- Claim : $E \ne D$
  E_ne_D : E ≠ D := sorry
  -- $DE \parallel BC$
  hDE : (LIN D E E_ne_D) ∥ (LIN B C C_ne_B)
  --X lies in AB
  X : Plane
  hX : X LiesInt (SEG_nd A B B_ne_A)
  --Claim : $X$ is not $E,C$
  X_ne_C : X ≠ C := sorry
  X_ne_E : X ≠ E := sorry
  --$Y$ is a point on line $XE$
  Y : Plane
  hY₁ : Y LiesOn (LIN X E X_ne_E.symm)
  -- Claim : $Y$ is not $A$
  Y_ne_A : Y ≠ A := sorry
  -- AY parallels to XC
  hY₂ : (LIN A Y Y_ne_A)∥(LIN X C X_ne_C.symm)

--$\frac{EY}{EX}=\frac{AD}{DB}$
theorem result {Plane : Type*} [EuclideanPlane Plane] (e : Setting Plane) :  (SEG e.E e.Y).length/(SEG e.E e.X).length = (SEG e.A e.D).length/(SEG e.D e.B).length := sorry

end AOPS_Problem_5_7


namespace AOPS_Exercise_5_2_3
/- Let $WXYZ$ be a square. $M$ is the midpoint of $YZ$, $A$ lies on $WZ$ and $B$ lies on $XY$, if $AB\perp MX$, prove that
\begin{enumerate}[(a)]
\item $WZ\para XY$
\item $AZ=YB$
\item $XB=XA$
\item $\triangle AZM\sim\triangle MYX$
\item $AZ=XY/4$
\end{enumerate}.
 -/
--Need the definition of square.

end AOPS_Exercise_5_2_3


namespace AOPS_Exercise_5_3_2
/- \triangle ABC$, $E$ lies on the extension of $CA$ while $F$ lies on the extension of $BA$, $I$ lies on the extension of $CE$ and $J$ lies on the extension of $BF$. Assume that $AC=AE=EI$, $AB=AF=FJ$.

Prove that $IJ\prar BC$-/
--It is simpler to use vectors but I think we should avoid vectors.

structure Setting (Plane : Type*) [EuclideanPlane Plane] where
  -- Let $\triangle ABC$ be a nontrivial triangle
  A : Plane
  B : Plane
  C : Plane
  not_collinear_ABC : ¬ Collinear A B C
  -- Claim :$C \ne A$
  B_ne_A : B ≠ A :=
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.2
  C_ne_A : C ≠ A :=
    -- This is because vertices $A, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.1.symm
  -- Claim $B \ne C$
  C_ne_B : C ≠ B :=
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).1
  --E lies on the extension of CA
  E : Plane
  hE₁ : E LiesInt (SEG_nd C A C_ne_A.symm).extension
  --F lies on the extension of BA
  F : Plane
  hF₁ : F LiesInt (SEG_nd B A B_ne_A.symm).extension
  -- Claim : $E \ne C$
  E_ne_C : E ≠ C := sorry
  -- Claim : $F \ne B$
  F_ne_B : F ≠ B := sorry
  --I lies on the extension of CE
  I : Plane
  hI₁ : I LiesInt (SEG_nd C E E_ne_C).extension
  --J lies on the extension of BF
  J : Plane
  hJ₁ : J LiesInt (SEG_nd B F F_ne_B).extension
  -- $AC=AE=EI$, $AB=AF=FJ$
  hE₂ : (SEG A C).length = (SEG A E).length
  hF₂ : (SEG A B).length = (SEG A F).length
  hI₂ : (SEG A C).length = (SEG E I).length
  hJ₂ : (SEG A B).length = (SEG F J).length
  -- Claim : $J \ne I$
  J_ne_I : J ≠ I := sorry
  --$IJ\parallel BC$
theorem result {Plane : Type*} [EuclideanPlane Plane] (e : Setting Plane) : LIN e.I e.J e.J_ne_I ∥ LIN e.B e.C e.C_ne_B := sorry

end AOPS_Exercise_5_3_2
end AOPS
end EuclidGeom
