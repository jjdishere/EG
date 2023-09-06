import EuclideanGeometry.Foundation.Axiom.Position

noncomputable section
namespace EuclidGeom

class Line (P : Type _) [EuclideanPlane P] where 
  carrier : Set P
  linear : ∀ (A B C : P), (A ∈ carrier) → (B ∈ carrier) → (C ∈ carrier) → colinear A B C  
  maximal : ∀ (A B : P), (A ∈ carrier) → (B ∈ carrier) → (A ≠ B) → (∀ (C : P), colinear A B C → (C ∈ carrier))
  nontriv : ∃ (A B : P), (A ∈ carrier) ∧ (B ∈ carrier) ∧ (A ≠ B)

namespace Line

variable  {P : Type _} [EuclideanPlane P] 

-- define a line from two points 

def mk_pt_pt (A B : P) (h : B ≠ A) : Line P := sorry --careful here! should I use B ≠ A or A ≠ B ? 

end Line

scoped notation "LIN" => Line.mk_pt_pt 

variable {P : Type _} [EuclideanPlane P]

/- def coe from ray to line-/
instance : Coe (Ray P) (Line P) where
  coe := sorry

/- Def of point lies on a line -/
def IsOnLine (a : P) (l : Line P) : Prop :=
  a ∈ l.carrier

scoped infix : 50 "LiesOnLine" => IsOnLine


section Compaitiblity_of_coersions


-- If a point lies on a ray, then it lies on the line associated to the ray.
theorem lies_on_line_of_ray_of_lies_on_ray (a : P) (l : Ray P) (h : a LiesOnRay l) : a LiesOnLine l := sorry

-- If A and B are two distinct points, they lie on the line AB
theorem source_or_ray_lies_on_line_of_ray (l : Ray P) : l.source LiesOnLine l := sorry

theorem pt_lies_on_line_of_pt_pt (A B : P) (h: B ≠ A) : A LiesOnLine LIN A B h ∧ B LiesOnLine LIN A B h := sorry


-- The line defined from two distinct points is equal to the line defined from the ray associated to two distinct points

theorem line_eq_line_of_ray_of_pt_pt {A B : P} (h : B ≠ A) : LIN A B h = ((RAY A B h) : Line P) := sorry
-- `not clear whether I should remove : Line P (it compiles)`

theorem line_eq_line_of_pt_pt {A B : P} {l : Line P} (h : B ≠ A) (hA : A LiesOnLine l) (hB : B LiesOnLine l) : l = Line.mk_pt_pt A B h := sorry -- p ≠ q or q ≠ p ?

theorem lieson_of_colinear_ne {A B C : P} (c : colinear A B C) (h : B ≠ A) : C LiesOnLine LIN A B h := sorry

end Compaitiblity_of_coersions

section Archimedean_property
-- there are two distinct points on a line

-- Given distinct A B on a line, there exist C s.t. C LiesOn AB (a cor of Archimedean_property in Seg) and there exist D s.t. B LiesOn AD
end Archimedean_property

end EuclidGeom