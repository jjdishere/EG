import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom
namespace ShanZun

namespace Shan_Problem_2_13
/- In $\triangle ABC$. Let $D$ be the midpoint of segment $BC$,
the perpendicular line passing through $D$ of the bisector of $\angle BAC$ intersects $AB,AC$ at $E,F$ respectively.
Prove that $BE=CF=\frac{1}{2}|AB-AC|$.  -/

structure Setting (Plane : Type*) [EuclideanPlane Plane] where
  -- Let $\triangle ABC$ be a nontrivial triangle
  A : Plane
  B : Plane
  C : Plane
  not_collinear_ABC : ¬ Collinear A B C
  -- Claim : $B \ne A$
  B_ne_A : B ≠ A :=
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.2
  -- Claim :$C \ne A$
  C_ne_A : C ≠ A :=
    -- This is because vertices $A, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.1.symm
  -- Claim $B \ne C$
  B_ne_C : B ≠ C :=
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).1.symm
  -- D is the midpoint of the segment $BC$
  D : Plane
  hD : D = (SEG B C).midpoint
  --l is the perpendicular line passing through $D$ of the bisector of $\angle BAC$
  l : Line Plane
  hl : l = perp_line D (ANG B A C B_ne_A C_ne_A).AngBis.toLine
  --E is the intersection of $l$ and $AB$
  E : Plane
  hE : is_inx E (LIN A B B_ne_A) l
  --F is the intersection of $l$ and $AC$
  F : Plane
  hF : is_inx F (LIN A C C_ne_A) l


-- Theorem : $BE=CF=\frac{1}{2}|AB-AC|$
theorem result {Plane : Type*} [EuclideanPlane Plane] (e : Setting Plane) :(SEG e.B e.E).length=|((SEG e.A e.B).length-(SEG e.A e.C).length)|/2 ∧ (SEG e.C e.F).length = |((SEG e.A e.B).length-(SEG e.A e.C).length)|/2 := sorry

end Shan_Problem_2_13

namespace Shan_Problem_2_18
/- In $\triangle ABC$, $AC < BC$. Let $CD$ be the height,
 $CE$ be the bisector of $\angle ACB$ and $CF$ be the median.
Prove that $E$ liesInt $DF$ -/

structure Setting (Plane : Type*) [EuclideanPlane Plane] where
  -- Let $\triangle ABC$ be a nontrivial triangle
  A : Plane
  B : Plane
  C : Plane
  not_collinear_ABC : ¬ Collinear A B C
  -- Claim :$C \ne A$
  C_ne_A : C ≠ A :=
    -- This is because vertices $A, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.1.symm
  -- Claim $B \ne C$
  C_ne_B : C ≠ B :=
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).1
  B_ne_A : B ≠ A :=
    -- This is because vertices $B, C$ of a nondegenerate triangle are distinct.
    (ne_of_not_collinear not_collinear_ABC).2.2
  -- We have triagngle $\triangle ABC$ such that $AC < BC$
  hedge : (SEG_nd A C C_ne_A).length < (SEG_nd B C C_ne_B).length
  --$D$ is the perpendicular foot from $A$ to line $BC$
  D : Plane
  hD : D = perp_foot A (LIN B C C_ne_B)
  -- $E$ is the intersection of the angle bisector of $\angle ACB$ and $AB$
  E : Plane
  hE : is_inx E (ANG A C B C_ne_A.symm C_ne_B.symm).AngBis (SEG A B)
  -- $F$ is the midpoint of $AB$
  F : Plane
  hF : F = (SEG A B).midpoint
  --Claim : $D\ne C$
  D_ne_C : D ≠ C := sorry
  --Claim : $E\ne C$
  E_ne_C : E ≠ C := sorry
  --Claim : $F\ne C$
  F_ne_C : F ≠ C := sorry

theorem result1 {Plane : Type*} [EuclideanPlane Plane] (e : Setting Plane) : e.E LiesInt (SEG e.D e.F) := sorry


-- Theorem : $CE$ is the bisector of $\angle FCD$
theorem result2 {Plane : Type*} [EuclideanPlane Plane] (e : Setting Plane) : ∠ e.F e.C e.E e.F_ne_C e.E_ne_C = ∠ e.E e.C e.D e.E_ne_C e.D_ne_C := sorry


end Shan_Problem_2_18

end ShanZun
end EuclidGeom
