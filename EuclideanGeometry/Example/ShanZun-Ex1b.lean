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
  lemma b_ne_c : B ≠ C := (ne_of_not_colinear hnd).1.symm
  variable {D : P} {median_D_position : D = (SEG B C).midpoint}
  variable {median : SegND P} {defmedian: median = (SEG A D)}
  variable {E : P} {E_on_ray : E LiesInt (SEG A D)}
  variable {E_ray_position : (SEG B E).length = (SEG A C).length}
  variable {F : P} {intersection_bridge : F LiesInt (SEG A C) ∧ F LiesInt (SEG B E)}
  theorem Shan_Problem_1_5 : (SEG A F).length = (SEG E F).length := by sorry

end Shan_Problem_1_5

namespace Shan_Problem_1_6
/- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.

Prove that For any point $D$ on the base $BC$, the sum of the the distance of $D$ to $AB$ and to $AC$ is independent of $D$. -/
  -- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
  variable {A B C : P} {hnd : ¬ colinear A B C} {hisoc : (▵ A B C).IsIsoceles}
  -- Claim: $A \ne B$ and $A \neq C$. This is because vertices of nondegenerate triangles are distinct.
  lemma b_ne_a : B ≠ A := (ne_of_not_colinear hnd).2.2
  lemma c_ne_a : C ≠ A := (ne_of_not_colinear hnd).2.1.symm
  -- Claim: For any point $D$ on the interior of the segment of $BC$, $D ≠ B$ and $D ≠ C$. This is because: $D$ is an interior point of an edge of a triangle, so it is not equal to the vertexs $B$ and $C$ of the triangle.
  variable {D : P}{hd : D LiesInt (SEG B C)}
  lemma d_ne_b {D : P} {hd : D LiesInt (SEG B C)} : D ≠ B := ((TRI_nd A B C hnd).ne_vertex_of_lies_int_fst_edge hd).2.1
  lemma d_ne_c {D : P} {hd : D LiesInt (SEG B C)} : D ≠ C := ((TRI_nd A B C hnd).ne_vertex_of_lies_int_fst_edge hd).2.2

  theorem Shan_Problem_1_6 : ∃ (const : ℝ) , ∀ D : P , (hd : D LiesInt (SEG B C)) →
    dist_pt_line D (LIN A B (b_ne_a (hnd := hnd))) + dist_pt_line D (LIN A C (c_ne_a (hnd := hnd))) = const := by
    sorry

end Shan_Problem_1_6
