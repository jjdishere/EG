import EuclideanGeometry.Axiom.Position

noncomputable section
namespace EuclidGeom

class Line (P : Type _) [EuclideanPlane P] where 
  carrier : Set P
  linear : ∀ (A B C : P), (A ∈ carrier) → (B ∈ carrier) → (C ∈ carrier) → colinear A B C  
  maximal : ∀ (A B : P), (A ∈ carrier) → (B ∈ carrier) → (A ≠ B) → (∀ (C : P), colinear A B C → (C ∈ carrier))

namespace Line

variable  {P : Type _} [EuclideanPlane P] 

def mk'(A B : P) (h : A ≠ B) : Line P := sorry

end Line

/- def coe from ray to line-/
instance {P : Type _} [EuclideanPlane P] : Coe (Ray P) (Line P) where
  coe := sorry

end EuclidGeom