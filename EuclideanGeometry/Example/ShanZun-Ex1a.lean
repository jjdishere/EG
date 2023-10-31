import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Shan_Problem_1_3
/- Let $\triangle ABC$ be an isosceles triangle in which $AB = AC$. Let $D$ be a point in the extension of $AB$ such that $BD = AB$. Let $E$ be the midpoint of $AB$.

Prove that $CD = 2 \cdot CE$. -/
  -- Define an isosceles triangle ABC
  variable {A B C : P} {hnd : ¬ colinear A B C} {hisoc : (▵ A B C).IsIsoceles}
  -- A ≠ B
  lemma a_ne_b : A ≠ B := (ne_of_not_colinear hnd).2.2.symm
  -- Since D is on line AB and AB = BD, it is trivial that D is on ray AB. Position can be determined here.
  variable {D : P} {D_on_ray : D LiesInt (RAY A B a_ne_b) }
  variable {D_ray_position : (SEG A B).length = (SEG B D).length }
  -- As E is on AB, AE = EB, we can do the same with regard to E.
  variable {E : P} {E_on_ray : E LiesInt (RAY A B a_ne_b) }
  variable {E_ray_position : (SEG A E).length = (SEG B E).length }
  -- State the main goal
  theorem Shan_Problem_1_3 : (SEG C D).length = 2 * (SEG C E).length :=
    have h: (SEG B C).length = 1 := by
      sorry
    sorry
end Shan_Problem_1_3

namespace Shan_Problem_1_4
/- Let $\triangle ABC$ be a triangle in which $\angle BCA = 2 \cdot \angle CBA$. Let $AD$ be the height of $\triangle ABC$ over $BC$.

Prove that $BD = AC + CD$.-/

  -- Define a triangle ABC
  variable {A B C : P} {hnd : ¬ colinear A B C}
  -- Possibly needed non-linear conditions
  lemma a_ne_b : A ≠ B := (ne_of_not_colinear hnd).2.2.symm
  lemma a_ne_c : A ≠ C := (ne_of_not_colinear hnd).2.1
  lemma c_ne_b : C ≠ B := (ne_of_not_colinear hnd).1
  lemma b_ne_c : B ≠ C := (ne_of_not_colinear hnd).1.symm
  -- Get a point P on BC
  variable {D : P} {hd : D LiesInt (SEG B C)}
  -- Direct from the problem statement
  variable (hang : 2 * ∠ C B A c_ne_b a_ne_b = ∠ A C B a_ne_c b_ne_c)
  -- Define segment AD, with A ≠ D
  variable {height : Seg_nd P} {defheight : height = (SEG A D)}
  -- Define base BC. Possible improvement here.
  variable {base : Seg_nd P} {defbase : base = (SEG B C)}
  -- Perpendicular base and height, directly stated
  variable {heightproperty : height ⟂ base}
  -- Main theorem statement
  theorem Shan_Problem_1_4 : (SEG B D).length = (SEG A C).length + (SEG C D).length := sorry
end Shan_Problem_1_4
