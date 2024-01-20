import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

namespace Shan_Problem_2_21
/- In a parallelelogram ABCD, E and F lies on the segment AC, and $AE=FC$
Prove that $DE\parallel BF$ -/
variable {A B C D : P} {h : (QDR A B C D) IsPRG}

-- The diagonal is nondegenerate
lemma c_ne_a : C ≠ A :=sorry
-- Point E and F lie on the diagonal AC
variable {E F : P} {he : E LiesInt (SegND A C c_ne_a)} {hf : F LiesInt (SegND A C c_ne_a)}
-- Extra assumption that $AF=FC$
variable {hef : (SEG A E).length=(SEG F C).length}
-- Point B is not A
lemma b_ne_a : B ≠ A := sorry
-- Point D is not C
lemma d_ne_c : D ≠ C := sorry
-- point F is not C
lemma f_ne_c : F ≠ C := sorry

-- Point A is not the same as E
lemma a_ne_e : A ≠ E := sorry
-- Point B is not the same as E
lemma b_ne_e : B ≠ E := sorry
-- Point D is not the same as E
lemma d_ne_e : D ≠ E := sorry

-- Point B is not the same as F
lemma b_ne_f : B ≠ F := sorry
-- Point C is not the same as F
lemma c_ne_f : C ≠ F := sorry
-- Point D is not the same as f
lemma d_ne_f : D ≠ F := sorry

-- $\ang BAE=\ang DCF$
lemma ang_bae_eq_ang_dcf : ∠ B A E b_ne_a a_ne_e.symm = ∠ D C F d_ne_c f_ne_c := sorry
-- $▵ABE≅▵CDF$ by SAS
lemma abe_congr_cdf: TRI A B E ≅ TRI C D F := sorry
-- $∠ AEB = ∠ CFD$
lemma ang_aeb_eq_ang_cfd : ∠ A E B a_ne_e.symm b_ne_e = ∠ C F D c_ne_f d_ne_f := sorry
-- $DE \parallel BF because the alternate angle is the same
theorem Shan_Problem_2_21 : (LIN D E d_ne_e) ∥ (LIN B F b_ne_f):= sorry
end Shan_Problem_2_21

namespace Shan_Problem_2_23
/- In a parallelelogram ABCD, E is the midpoint of the segment BC, and F is the midpoint of the segment AD. Let G, H be the intersection of AC with BF and DE respectively.
Prove that $AG=GH=HC$ -/
variable {A B C D : P} {h : (QDR A B C D) IsPRG}

-- The diagonal is nondegenerate
lemma c_ne_a : C ≠ A := sorry
-- Point E and F are the midpoints of BC and AD, respectively.
variable {E F : P} {he : E = (SEG B C).midpoint} {hf : F = (SEG A D).midpoint}
-- Point D is not the same as E
lemma d_ne_e : D ≠ E := sorry
-- Point B is not the same as F
lemma b_ne_f : B ≠ F := sorry
-- G is the intersection point of AC and BF, H is the intersection point of AC and DE
variable {G H : P} {hg : is_inx G (LIN A C c_ne_a.symm) (LIN B F b_ne_f)} {hh : is_inx H (LIN A C c_ne_a.symm) (LIN D E d_ne_e)}
-- $▵AFG$ is nontrivial
lemma afg_nd : ¬ Collinear A F G := sorry
-- $▵CBG$ is nontrivial
lemma cbg_nd : ¬ Collinear C B G :=sorry
-- $▵ AFG ∼ ▵ CBG$ with ratio 1/2 by AAA
lemma afg_sim_cbg : (TRI_nd A F G afg_nd) ∼ (TRI_nd C B G cbg_nd) := sorry
--The following three may not be necessary since we can use the above three lemmas instead
--
lemma ceh_nd : ¬ Collinear C E H := sorry
lemma adh_nd : ¬ Collinear A D H :=sorry
-- $▵ CEH ∼ ▵ ADH$ with ratio 1/2 by AAA
lemma ceh_sim_adh : (TRI_nd C E H ceh_nd) ∼ (TRI_nd A D H adh_nd) := sorry
-- length of segment AG is half of segment CG
lemma ag_eq_half_of_cg : (SEG A G).length = (SEG C G).length/2 := sorry
-- length of segment CH is half of segment AH
lemma ch_eq_half_of_ah : (SEG C H).length = (SEG A H).length/2 := sorry
-- The pair of points (G,H) divides the segement AC into three segments with the same length.
theorem Shan_Problem_2_23 : (SEG A G).length=(SEG G H).length ∧ (SEG A G).length=(SEG H C).length := sorry

end Shan_Problem_2_23
