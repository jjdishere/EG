import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Shan_Problem_1_5
/- In $\triangle ABC$, let $AD$ be the median.  Let $E$ be a point on $AD$ such that $BE = AC$. The line $BE$ intersects $AC$ at $F$.

Prove that $AF = EF$. -/

-- Let $\triangle ABC$ be an triangle.
variable {A B C : P} {hnd : ¬ colinear A B C}
def tri : Triangle P := ▵ A B C
-- Claim: $B \ne C$. This is because vertices of nondegenerate triangles are distinct.
lemma a_ne_c : A ≠ C := (ne_of_not_colinear hnd).2.1
lemma b_ne_c : B ≠ C := (ne_of_not_colinear hnd).1.symm
-- Claim: $BC$ is non degenerate. This is because $B \ne C$.
def seg_nd_ac : Seg_nd P := ⟨(SEG A C), Ne.symm (a_ne_c (hnd := hnd) ) ⟩
def seg_nd_bc : Seg_nd P := ⟨(SEG B C), Ne.symm (b_ne_c (hnd := hnd) ) ⟩
-- Let $D$ be the midpoint of $BC$.
variable {D : P} {d_mid : D = (SEG B C).midpoint}
-- $D$ Liesin $BC$. This is because $BC$ is non degenerate.
lemma d_int_bc : D LiesInt (SEG B C) := by rw [d_mid]; exact Seg_nd.midpt_lies_int (seg_nd_bc (hnd := hnd) )
lemma a_ne_d : A ≠ D := ((▵ A B C).ne_vertex_of_lies_int_fst_edge (d_int_bc (hnd := hnd) (d_mid := d_mid))).1.symm
def line_ad : Line P := LIN A D (a_ne_d (hnd := hnd) (d_mid := d_mid)).symm
variable {E : P} {he : E LiesOn (line_ad (hnd := hnd) (d_mid := d_mid))}
variable {be_eq_ac : (SEG B E).length = (SEG A C).length}
lemma b_ne_e : B ≠ E := by
  have h : ¬(SEG B E).length = 0 := by
    rw [be_eq_ac, (triv_iff_length_eq_zero (l := SEG A C)).symm.not, ← ne_eq]
    exact (a_ne_c (hnd := hnd)).symm
  rw [ne_eq]
  rw [(triv_iff_length_eq_zero (l := SEG B E)).symm.not] at h
  exact Ne.symm h
def seg_nd_be : Seg_nd P := ⟨SEG B E, Ne.symm (b_ne_e (hnd := hnd) (be_eq_ac := be_eq_ac))⟩
variable {be_not_parallel_ac : ¬ (seg_nd_be (hnd := hnd) (be_eq_ac := be_eq_ac)) ∥ (seg_nd_ac (hnd := hnd))}
theorem Shan_Problem_1_5 : (SEG A F).length = (SEG E F).length := by sorry

end Shan_Problem_1_5

namespace Shan_Problem_1_6
/- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.

Prove that For any point $D$ on the base $BC$, the sum of the the distance of $D$ to $AB$ and to $AC$ is independent of $D$. -/


end Shan_Problem_1_6
