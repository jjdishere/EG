import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from AOPS Geometry book Chapter 3

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Exercise_3_4_4

/- Statement: Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$. Let $X$ and $Y$ be points on the interior of the segments of $AC$ and $AB$, respectively, such that $\angle XBA = \angle ACY$. Let $M$ denote the intersection of the segment $BX$ and $CY$.
Theorem: We have $BX = CY$ and $MX = MY$.
-/

-- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : P} {hnd : ¬ colinear A B C} {hisoc : (▵ A B C).IsIsoceles}
-- Claim: $A \ne B$ and $A \neq C$. This is because vertices of nondegenerate triangles are distinct.
lemma a_ne_b : A ≠ B := (ne_of_not_colinear hnd).2.2.symm
lemma a_ne_c : A ≠ C := (ne_of_not_colinear hnd).2.1
-- Let $X$ and $Y$ be points on the interior of the segments of $AC$ and $AB$, respectively.
variable {X Y : P} {hx : X LiesInt (SEG A C)} {hy : Y LiesInt (SEG A B)}
-- Claim: $X \neq B$ and $Y \neq C$. This is because: $X$ is an interior point of an edge of a triangle, so it is not equal to a vertex $B$ of the triangle; similarly, $Y$ is an interior point of an edge of a triangle, so it is not equal to a vertex $C$ of the triangle.
lemma x_ne_b : X ≠ B := ((▵ A B C).ne_vertex_of_lies_int_snd_edge (Seg.lies_int_iff_lies_int_rev.mp hx)).2.1
lemma y_ne_c : Y ≠ C := ((▵ A B C).ne_vertex_of_lies_int_trd_edge hy).2.2
-- We have $\angle XBA = \angle ACY$.
variable (hang : ∠ X B A x_ne_b a_ne_b = - ∠ A C Y a_ne_c y_ne_c)



theorem Exercise_3_4_4 : (SEG B X).length = (SEG C Y).length ∧ (SEG M X).length = (SEG M Y) :=
begin
  sorry
end

theorem notttteq : X ≠ B := by
  Triangle_nd.not_lie_on_snd_and_trd_of_int_fst

-- variable (oang₁ oang₂ : OAngle P) (hang1 : oang₁ = ∠ X B A)

trind := Triangle_nd.mk (▵ A O B) hnd
let oang₁ = ∠ 
end Exercise_3_4_4


end EuclidGeom