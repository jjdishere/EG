import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]
namespace Shan_Problem_1_21
/- Let $\parallelogram ABCD$ be a parallelogram, E lies on AC while F lies on BD, AE = FC.

Prove that $DE ∥ BF$. -/

-- Introduce a parallelogram ABCD
variable {A B C D: P} {h : QDR A B C D IsPRG}

lemma c_ne_a : C ≠ A := sorry
lemma d_ne_b : B ≠ D := sorry

variable {E F : P } {he : E LiesInt (SEG_nd A C c_ne_a).1} {hf : F LiesInt (SEG_nd B D d_ne_b).1} {hef: (SEG A E).length = (SEG C F).length}

-- The lines DE and FB are nontrivial.
lemma d_ne_e : D ≠ E := sorry
lemma f_ne_b : F ≠ B := sorry

-- The angles are nontrivial
lemma d_ne_a : D ≠ A := sorry
lemma e_ne_a : E ≠ A := sorry
lemma b_ne_c : B ≠ C := sorry
lemma f_ne_c : F ≠ C := sorry

-- ∠ D A E
lemma dae_eq_bcf : ∠ D A E d_ne_a e_ne_a = ∠ B C F b_ne_c f_ne_b:= sorry
lemma ad_eq_cb : (SEG A D).length= (SEG C B).length := sorry
-- ▵ A D E ≅ ▵ C B F
lemma ade_cong_cbf : (▵ A D E).IsCongr (▵ C B F) := sorry

theorem Shan_Problem_1_21 : (SEG_nd D E d_ne_e) ∥ (SEG_nd B F f_ne_b) := sorry

end Shan_Problem_1_21

namespace Shan_Problem_1_23
/-Let ABCD be a parallelogram, E is the midpoint of BC while F is the midpoint of AD. Let G be the intersection of BF and AC, H be the intersection of DE and AC

Prove that $2AG=GC,2CH=HA$-/
variable {A B C D : P} {h : QDR A B C D IsPRG}
--Introduce the midpoints
variable {E F : P} {he : E = (SEG A D).midpoint} {hf : F = (SEG B C).midpoint}
--Introduce the intersection point G (H, resp.) of BF (DE, resp.) and AC
variable {G H : P} {hg: is_inx G (SEG B F) (SEG A C)} {hh: is_inx H (SEG D E) (SEG A C)}

-- We need triangles AFG,CBG,CEH,ADH to be nontrivial.
lemma hndg: ¬ colinear A F G := sorry
lemma hndg': ¬ colinear C B G := sorry
lemma hndh: ¬ colinear C E H := sorry
lemma hndh': ¬ colinear A D H := sorry

-- ▵ A F G ∼ ▵ C B G, the ratio is 1/2
lemma afg_sim_cbg : TRI_nd A F G hndg ∼ TRI_nd C B G hndg' := sorry
-- ▵ C E H ∼ ▵ A D H, the ratio is 1/2
lemma ceh_sim_adh : TRI_nd C E H hndh ∼ TRI_nd A D H hndh' := sorry

theorem Shan_Problem_1_23: 2*(SEG A G).length=(SEG G C).length ∧ 2*(SEG C H).length = (SEG H A).length := sorry

end Shan_Problem_1_23
