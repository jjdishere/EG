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

scoped notation "LIN" => Line.mk' 

/- def coe from ray to line-/
instance {P : Type _} [EuclideanPlane P] : Coe (Ray P) (Line P) where
  coe := sorry

/- Def of point lies on a line -/
def IsOnLine {P : Type _} [EuclideanPlane P] (a : P) (l : Line P) : Prop :=
  a ∈ l.carrier

scoped infix : 50 "LiesOnLine" => IsOnLine

theorem line_eq_line_of_two_pt {P : Type _} [EuclideanPlane P] {p q : P} {l : Line P} (h : q ≠ p) (hp : p LiesOnLine l) (hq : q LiesOnLine l) : l = Line.mk_pt_pt p q h := sorry -- p ≠ q or q ≠ p  

end EuclidGeom