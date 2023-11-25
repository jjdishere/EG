import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

namespace Problem1_8_

/-
Let $\triangle ABC$ be a regular triangle. Let $D$, $E$, $F$ be points on the extensions of $BC$, $CA$ and $AB$, respectively,
such that $CD = AE = BF$.

Prove that $AD = BE = CF$
-/

--Let $\triangle ABC$ be a regular triangle.
variable {A B C : Plane} {hnd : ¬ colinear A B C} {hreg : (▵ A B C).IsRegular}
--Claim $A \ne B$
lemma a_ne_b : A ≠ B := (ne_of_not_colinear hnd).2.2.symm
--Claim $B \ne C$
lemma b_ne_c : B ≠ C := (ne_of_not_colinear hnd).1.symm
--Claim $C \ne A$
lemma c_ne_a : C ≠ A := (ne_of_not_colinear hnd).2.1.symm
--let $D$ be point on the extension of $BC$
variable {D : Plane} {D_on_ext : D LiesInt (SEG_nd B C b_ne_c.symm).extension}
--let $E$ be point on the extension of $CA$
variable {E : Plane} {E_on_ext : E LiesInt (SEG_nd C A c_ne_a.symm).extension}
--let $F$ be point on the extension of $AB$
variable {F : Plane} {F_on_ext : F LiesInt (SEG_nd A B a_ne_b.symm).extension}
--such that $CD = AE = BF$
variable {D_E_F_ray_position : ((SEG C D).length = (SEG A E).length) ∧ ((SEG A E).length = (SEG B F).length)}
--Prove that $AD = BE = CF$
theorem Problem1_8_ : ((SEG A D).length = (SEG B E).length) ∧ ((SEG B E).length = (SEG C F).length) := by
  have ad_eq_be : (SEG A D).length = (SEG B E).length := by
    have hnd_bda : ¬ colinear B D A := by sorry
    have hnd_ceb : ¬ colinear C E B := by sorry
    have d_ne_b : D ≠ B := by sorry
    have a_ne_b : A ≠ B := by sorry
    have e_ne_c : E ≠ C := by sorry
    have b_ne_c : B ≠ C := by sorry
    have ab_eq_bc : (SEG A B).length = (SEG B C).length := hreg.2.symm
    have bc_eq_ca : (SEG B C).length = (SEG C A).length := hreg.1
    have c_lieson_bd : C LiesOn (SEG B D) := by sorry
    have a_lieson_ce : A LiesOn (SEG C E) := by sorry
    let angle_dba := Angle.mk_pt_pt_pt D B A d_ne_b a_ne_b
    let angle_ecb := Angle.mk_pt_pt_pt E C B e_ne_c b_ne_c
    have angle_dba_eq_angle_ecb : Angle.value angle_dba = Angle.value angle_ecb := by
      calc
      Angle.value angle_dba
      _= Angle.value (∠ C B A _ a_ne_b) := by sorry
      _= Angle.value (∠ A C B _ b_ne_c) := by sorry
      _= Angle.value angle_ecb := by sorry
    have bd_eq_ce : (SEG B D).length = (SEG C E).length := by
      calc
      (SEG B D).length
      _= (SEG B C).length + (SEG C D).length := by
        apply length_eq_length_add_length
        exact c_lieson_bd
      _= (SEG C A).length + (SEG C D).length := by rw [bc_eq_ca]
      _= (SEG C A).length + (SEG A E).length := by rw [D_E_F_ray_position.1]
      _= (SEG C E).length := by
        symm;apply length_eq_length_add_length
        exact a_lieson_ce
    have trngl_abd_congr_trngl_bce : Triangle_nd.IsCongr (TRI_nd B D A hnd_bda) (TRI_nd C E B hnd_ceb) := by
      apply Triangle_nd.congr_of_SAS
      · exact ab_eq_bc
      · exact angle_dba_eq_angle_ecb
      · exact bd_eq_ce
    calc
    (SEG A D).length = (SEG D A).length := by apply length_of_rev_eq_length'
    _= (SEG E B).length := trngl_abd_congr_trngl_bce.edge₁
    _= (SEG B E).length := by apply length_of_rev_eq_length'
  have be_eq_cf : (SEG B E).length = (SEG C F).length := by sorry
  exact ⟨ad_eq_be, be_eq_cf⟩
end Problem1_8_
