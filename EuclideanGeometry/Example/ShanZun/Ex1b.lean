import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Shan_Problem_1_5
/- In $\triangle ABC$, let $AD$ be the median.  Let $E$ be a point on $AD$ such that $BE = AC$. The line $BE$ intersects $AC$ at $F$.

Prove that $AF = EF$. -/

-- Let $\triangle ABC$ be an triangle.
variable {A B C : P} {hnd : ¬ collinear A B C}
def tri : Triangle P := ▵ A B C
-- Claim: $B \ne C$. This is because vertices of nondegenerate triangles are distinct.
lemma A_ne_C : A ≠ C := (ne_of_not_collinear hnd).2.1
lemma B_ne_C : B ≠ C := (ne_of_not_collinear hnd).1.symm
-- Claim: $BC$ is non degenerate. This is because $B \ne C$.
def SegND_ac : SegND P := SEG_nd A C (Ne.symm (A_ne_C (hnd := hnd)))
def SegND_bc : SegND P := ⟨(SEG B C), Ne.symm (B_ne_C (hnd := hnd) ) ⟩
-- Let $D$ be the midpoint of $BC$.
variable {D : P} {d_mid : D = (SEG B C).midpoint}
-- $D$ Liesin $BC$. This is because $BC$ is non degenerate.
lemma d_int_bc : D LiesInt (SEG B C) := by rw [d_mid]; exact (SegND_bc (hnd := hnd)).midpt_lies_int
lemma a_ne_d : A ≠ D := ((TRI_nd A B C hnd).ne_vertex_of_lies_int_fst_edge (d_int_bc (hnd := hnd) (d_mid := d_mid))).1.symm
def line_ad : Line P := LIN A D (a_ne_d (hnd := hnd) (d_mid := d_mid)).symm
variable {E : P} {he : E LiesOn (line_ad (hnd := hnd) (d_mid := d_mid))}
variable {be_eq_ac : (SEG B E).length = (SEG A C).length}
lemma B_ne_E : B ≠ E := by
  have h : ¬(SEG B E).length = 0 := by
    rw [be_eq_ac, ((SEG A C).length_eq_zero_iff_deg).not, ← ne_eq]
    exact (A_ne_C (hnd := hnd)).symm
  rw [ne_eq]
  rw [((SEG B E).length_eq_zero_iff_deg).not] at h
  exact Ne.symm h
def SegND_be : SegND P := ⟨SEG B E, Ne.symm (B_ne_E (hnd := hnd) (be_eq_ac := be_eq_ac))⟩
variable {be_not_parallel_ac : ¬ (SegND_be (hnd := hnd) (be_eq_ac := be_eq_ac)) ∥ (SegND_ac (hnd := hnd))}

-- Theorem : $AF = EF$
theorem Shan_Problem_1_5 {F} : (SEG A F).length = (SEG E F).length := by sorry

end Shan_Problem_1_5

namespace Shan_Problem_1_6
/- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.

Prove that for any point $D$ on the base $BC$,
the sum of the the distance of $D$ to $AB$ and to $AC$ is independent of $D$. -/

-- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : P} {hnd : ¬ collinear A B C} {isoceles_ABC : (▵ A B C).IsIsoceles}
-- Claim: $A \ne B$ and $B \ne C$ and $C \ne A$.
lemma A_ne_B : A ≠ B := sorry
lemma B_ne_C : B ≠ C := sorry
lemma c_ne_a : C ≠ A := sorry
-- For any $D$, let $htsum(D)$ be the sum of the the distance of $D$ to $AB$ and to $AC$
def htsum (D : P) : ℝ := dist_pt_line D (LIN A B A_ne_B.symm) + dist_pt_line D (LIN A C c_ne_a)
-- $D₁, D₂$ are arbitary points on segment $BC$
variable {D₁ D₂ : P} {hd₁ : D₁ LiesInt (SEG B C)} {hd₂ : D₂ LiesInt (SEG B C)}

-- Theorem : For any point $D$ on the base $BC$, the sum of the the distance of $D$ to $AB$ and to $AC$ is independent of $D$
theorem Shan_Problem_1_6 : htsum (A := A) (B := B) (C := C) D₁ = htsum (A := A) (B := B) (C := C) D₂ := sorry

end Shan_Problem_1_6
