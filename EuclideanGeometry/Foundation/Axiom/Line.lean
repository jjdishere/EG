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

theorem line_eq_line_of_pt_pt {A B : P} {l : Line P} (h : B ≠ A) (hA : A LiesOnLine l) (hB : B LiesOnLine l) : l = Line.mk_pt_pt A B h := sorry -- p ≠ q or q ≠ p ?

theorem lieson_of_colinear_ne {A B C : P} (c : colinear A B C) (h : B ≠ A) : C LiesOnLine LIN A B h := sorry

section Archimedean_property
-- there are two distinct points on a line

-- Given distinct A B on a line, there exist C s.t. C LiesOn AB (a cor of Archimedean_property in Seg) and there exist D s.t. B LiesOn AD
end Archimedean_property

end EuclidGeom