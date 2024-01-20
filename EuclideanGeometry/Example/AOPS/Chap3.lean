import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from AOPS Geometry book Chapter 3

namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

namespace Exercise_3_4_4

/- Statement: Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$. Let $X$ and $Y$ be points on the interior of the segments of $AC$ and $AB$, respectively, such that $\angle XBA = \angle ACY$. Let $M$ denote the intersection of the segment $BX$ and $CY$.
Theorem: We have $BX = CY$ and $MX = MY$.
-/

-- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable {A B C : P} {hnd : ¬ Collinear A B C} {isoceles_ABC : (▵ A B C).IsIsoceles}
-- Claim: $A \ne B$ and $A \neq C$. This is because vertices of nondegenerate triangles are distinct.
lemma A_ne_B : A ≠ B := (ne_of_not_collinear hnd).2.2.symm
lemma A_ne_C : A ≠ C := (ne_of_not_collinear hnd).2.1
-- Let $X$ and $Y$ be points on the interior of the segments of $AC$ and $AB$, respectively.
variable {X Y : P} {hx : X LiesInt (SEG A C)} {hy : Y LiesInt (SEG A B)}
-- Claim: $X \neq B$ and $Y \neq C$. This is because: $X$ is an interior point of an edge of a triangle, so it is not equal to a vertex $B$ of the triangle; similarly, $Y$ is an interior point of an edge of a triangle, so it is not equal to a vertex $C$ of the triangle.
lemma x_ne_B : X ≠ B := ((TRI_nd A B C hnd).ne_vertex_of_lies_int_snd_edge (Seg.lies_int_rev_iff_lies_int.mp hx)).2.1
lemma y_ne_C : Y ≠ C := ((TRI_nd A B C hnd).ne_vertex_of_lies_int_trd_edge hy).2.2
-- We have $\angle XBA = \angle ACY$.
variable (hang : ∠ X B A x_ne_B A_ne_B = - ∠ A C Y A_ne_C y_ne_C)



--theorem Exercise_3_4_4 : (SEG B X).length = (SEG C Y).length ∧ (SEG M X).length = (SEG M Y) :=

end Exercise_3_4_4


end EuclidGeom
