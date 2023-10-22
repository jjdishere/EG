import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Shan_Problem_1_7
/- In $\triangle ABC$, $\angle ACB = \pi /2$. Let $D$ be the midpoint of $AB$. 

Prove that $CD = AB / 2$. -/
variable {A B C : P} {hnd : ¬ colinear A B C}
-- Claim: $A \ne B$ and $A \ne C$ and $B \ne C$.
-- This is because vertices of nondegenerate triangles are distinct.
lemma b_ne_a : B ≠ A := (ne_of_not_colinear hnd).2.2
lemma c_ne_a : C ≠ A := (ne_of_not_colinear hnd).2.1.symm
lemma b_ne_c : B ≠ C := (ne_of_not_colinear hnd).1.symm
--∠ A C B = π/2
variable {hot : ∠ A C B c_ne_a.symm b_ne_c = π/2 }
-- D is the midpoint of segment AB 
variable {D : P} {hd : D = (SEG A B).midpoint}
--Introduce the midpoint E of AC
lemma d_ne_a: D ≠ A := by
  rw[hd]
  apply (Seg_nd.midpt_lies_int (SEG_nd A B (b_ne_a).symm)).2.1
  use C
  by_contra h
  have : colinear A B C :=by 
    apply flip_colinear_fst_snd h
  trivial
variable {E : P} {he : E=  (SEG A C).midpoint}
lemma hnd₁: ¬ colinear A D E := by
  intro h'
  have : colinear A D B := by
    apply colinear_of_vec_eq_smul_vec'
    use 2
    simp only [hd,Seg.midpoint,one_div, seg_toVec_eq_vec, Complex.real_smul, Complex.ofReal_inv,Complex.ofReal_ofNat, vec_of_pt_vadd_pt_eq_vec, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,mul_inv_cancel_left₀]
  have : colinear A B E := by
    apply colinear_of_colinear_colinear_ne this h' d_ne_a
    use B
    use C
    exact hnd
    exact hd
lemma hnd₂: ¬ colinear C D E := sorry
-- lemma ade_sim_abc: (TRI_nd A D E) ∼ (TRI_nd A B C) :=sorry
lemma ade_cong_cde : TRI A D E ≅ TRI C D E := sorry
lemma cd : (TRI C D E).edge₃.length = (SEG C D).length:=by
  simp only [Triangle.edge₃]
lemma ad : (TRI A D E).edge₃.length = (SEG A D).length:=by
  simp only [Triangle.edge₃]
lemma cd_eq_ad: (SEG C D).length = (SEG A D).length := by
    rw[← cd,←ad]
    apply ade_cong_cde.edge₃ 
    trivial
    trivial
theorem Shan_Problem_1_7 : (SEG C D).length = (SEG A B).length/2 := by
  rw[length_eq_length_add_length (SEG A B) D,← dist_target_eq_dist_source_of_eq_midpt,half_add_self]
  simp only [Seg.source]
  rw [cd_eq_ad]
  trivial
  trivial
  rw[hd]
  apply Seg.midpt_lies_on

end Shan_Problem_1_7

namespace Shan_Problem_1_8
/- In $\triangle ABC$, let $BD$ and $CE$ be the heights, with foots $D$ and $E$, respectively. Let $F$ and $G$ be the midpoint of $BC$ and $DE$, respectively. 

Prove that $FG \perp DE$. -/



end Shan_Problem_1_8