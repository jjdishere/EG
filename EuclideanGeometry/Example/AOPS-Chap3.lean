import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from AOPS Geometry book Chapter 3

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Exercise_3_4_4

/- Statement: Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$. Let $X$ and $Y$ be points on the interior of the segments of $AC$ and $AB$, respectively, such that $\measuredangle XBA = - \measuredangle YCA$. Let $M$ denote the intersection of the segment $BX$ and $CY$.
Theorem: We have $BX = CY$ and $MX = MY$.
-/

-- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$.
variable (A B C : P) (hnd : ¬ colinear A B C) (tr_nd : Triangle_nd P) (htri : tr_nd = ⟨ ▵ A B C, hnd⟩) (hisoc : tr_nd.1.IsIsoceles)
-- Let $X$ and $Y$ be points on the interior of the segments of $AC$ and $AB$, respectively.
variable (X Y : P) (hx : X LiesInt (SEG A C)) (hy : Y LiesInt (SEG A B))
-- Then $X \neq

lemma hxb : X ≠ B := by 


-- We have $\measuredangle XBA = - \measuredangle YCA$.





  have c1 : ¬ X LiesOn tr_nd.1.edge₃ := by 
    let h3 := Seg.lies_int_rev_iff_lies_int.mp hx
    simp [Seg.reverse] at h3
    unfold Triangle.edge₃
    exact (tr_nd.not_lie_on_trd_and_fst_of_int_snd h3).1
    sorry
    

  sorry

let h3 := Seg.lies_int_rev_iff_lies_int.mp hx
    simp [Seg.reverse] at h3
    unfold Triangle_nd.1.edge₃
    exact (tr_nd.not_lie_on_trd_and_fst_of_int_snd h3).1
variable (angXBA angYCA: Angle P) (hoXBA : angXBA = ANG X B A (ne_of_not_mem_of_mem (Triangle_nd.not_lie_on_trd_and_fst_of_int_snd (eq_source_iff_lies_on_ray_lies_on_ray_rev hx).1 tr_nd.edge₃.target_lies_on) )




variable (M : P) (hm1 : M = )

theorem Exercise_3_4_4 : (SEG B X).length = (SEG C Y).length ∧ (SEG M X).length = (SEG M Y) :=
begin
  sorry
end

theorem notttteq : X ≠ B := by
  Triangle_nd.not_lie_on_snd_and_trd_of_int_fst

-- variable (ang₁ ang₂ : Angle P) (hang1 : ang₁ = ANG X B A)

trind := Triangle_nd.mk (▵ A O B) hnd
let ang₁ = ANG 
end Exercise_3_4_4


end EuclidGeom