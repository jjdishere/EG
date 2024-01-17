import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

namespace Congruence_Exercise_ygr

namespace Problem_4
/-
$A,D$ are on the opposite side of line $BC$,which satisfies $BD \parallel CA$, $BD = BC$
$E$ liesint $BC$ and $BE = AC$
Prove that $\angle B D E = -\angle C B A $.
-/
structure Setting1  (Plane : Type _) [EuclideanPlane Plane] where
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  --some nondegenerate
  hnd₁ : ¬ collinear B C A
  hnd₂ : ¬ collinear B C D
  --$A,D$ are on the opposite side of line $BC$,which satisfies $BD \para CA$(lemma needed), $BD = BC$
  BD_eq_BC : (SEG B D).length = (SEG B C).length
instance B_ne_C {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.B e.C := ⟨(ne_of_not_collinear e.hnd₁).2.2.symm⟩
instance D_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.D e.B := ⟨(ne_of_not_collinear e.hnd₂).2.1.symm⟩
instance A_ne_C {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.A e.C := ⟨(ne_of_not_collinear e.hnd₁).1⟩

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends Setting1 Plane where
  --$BD \para CA$
  BD_para_CA : (SEG_nd B D) ∥ (SEG_nd C A)
  --$A,D$ are on the opposite side of line $BC$
  A_side : IsOnLeftSide A (SEG_nd B C)
  D_side : IsOnRightSide D (SEG_nd B C)
  --$E$ liesint $BC$ and $BE = AC$
  E : Plane
  E_int : E LiesInt (SEG_nd B C)
  E_position : (SEG B E).length = (SEG A C).length
lemma hnd₃ {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane}: ¬ collinear e.B e.E e.D := by sorry
instance E_ne_D {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane} : PtNe e.E e.D := ⟨(ne_of_not_collinear hnd₃).1.symm⟩
instance A_ne_B {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane} : PtNe e.A e.B := ⟨(ne_of_not_collinear e.hnd₁).2.1.symm⟩
instance B_ne_E {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane} : PtNe e.B e.E := ⟨(ne_of_not_collinear hnd₃).2.2.symm⟩
--Prove that $\angle B D E = -\angle C B A $.
theorem Result {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane} : ∠ e.B e.D e.E = -∠ e.C e.B e.A := by
  /-
  Because $BD \parallel CA$,($A,D$ are on the opposite side of line $BC$),
  $\angle D B E $ and $\angle A C B$ are Alternate Interior Angle, thus equal.
  In $\triangle B E D$ and $\triangle C A B$
  $\cdot DB = BC$
  $\cdot \angle E B D = -\angle A C B$
  $\cdot BE = CA$
  We have $\triangle B E D \congr_a \triangle C A B$
  Thus $\angle B D E = -\angle C B A $.
  -/
  have hnd₁' : ¬ collinear e.C e.A e.B := by
    apply perm_collinear_trd_fst_snd.mt
    exact e.hnd₁
  --$DB = BC$
  have e₂ : (SEG e.D e.B).length = (SEG e.B e.C).length := by
    calc
      _=(SEG e.B e.D).length := by apply length_of_rev_eq_length'
      _=_ := e.BD_eq_BC
  --Because $BD \parallel CA$,($A,D$ are on the opposite side of line $BC$),
  --$\angle D B E $ and $\angle A C B$ are Alternate Interior Angle, thus equal.
  have a₁ : ∠ e.E e.B e.D = -∠ e.A e.C e.B := by
    have hAltint : IsAlternateIntAng (ANG e.D e.B e.E) (ANG e.A e.C e.B) := by
      constructor
      --neg Dir for start ray and same DirLine for end ray
      · show (RAY e.B e.D).toDir = -(RAY e.C e.A).toDir
        -- by $A,D$ are on the opposite side of line $BC$ and $BD \parallel CA$
        apply neg_toDir_of_parallel_and_opposite_side
        · exact e.BD_para_CA
        · show IsOnOppositeSide e.D e.A (SEG_nd e.B e.C)
          unfold IsOnOppositeSide
          unfold IsOnOppositeSide'
          show e.D LiesOnLeft (SEG_nd e.B e.C) ∧ e.A LiesOnRight (SEG_nd e.B e.C) ∨ e.D LiesOnRight (SEG_nd e.B e.C) ∧ e.A LiesOnLeft (SEG_nd e.B e.C)
          simp only [e.D_side, e.A_side, and_self, or_true]
        · exact B_ne_C.out
      · show (RAY e.B e.E).toDirLine = (RAY e.C e.B).toDirLine.reverse
        calc
          _=(SEG_nd e.B e.C).toDirLine :=
            SegND.dirLine_source_pt_eq_toDirLine_of_lies_int (e.E_int)
          _=(SEG_nd e.C e.B).toDirLine.reverse := by
            symm
            apply SegND.toDirLine_rev_eq_rev_toDirLine
          _=(RAY e.C e.B).toDirLine.reverse := by
            congr

    calc
      _=-∠ e.D e.B e.E := by apply Angle.neg_value_of_rev_ang --anti-symm
      _=-∠ e.A e.C e.B := by --Alternate interior angle
        have neg : ∠ e.D e.B e.E = ∠ e.A e.C e.B := value_eq_of_isAlternateIntAng (hAltint)
        simp only [neg]
  --$BE = CA$
  have e₃ : (SEG e.B e.E).length = (SEG e.C e.A).length := by
    calc
      _=(SEG e.A e.C).length := by exact e.E_position --given
      _=_ := by simp only [length_of_rev_eq_length'] --symm
  --We have $\triangle B E D \congr_a \triangle C A B$
  have h : (TRI_nd e.B e.E e.D hnd₃) ≅ₐ (TRI_nd e.C e.A e.B hnd₁') := by
    apply TriangleND.acongr_of_SAS
    · exact e₂
    · exact a₁
    · exact e₃
  exact h.angle₃
end Problem_4
end Congruence_Exercise_ygr
