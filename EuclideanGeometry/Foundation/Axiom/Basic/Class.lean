/- define class of On and In and FallsOn, define LiesOn and IsIntersection, every geometric figure should be an instance of these classes -/

import EuclideanGeometry.Foundation.Axiom.Basic.Plane

noncomputable section
namespace EuclidGeom

-- class PlaneFigure (P: Type _) [EuclideanPlane P] (α : Type _) where

class Carrier (P: Type _) [EuclideanPlane P] (α : Type _) where
  carrier : α → Set P

class Interior (P: Type _) [EuclideanPlane P] (α : Type _) where
  interior : α → Set P


def lies_on {P : Type _} [EuclideanPlane P] {α : Type _} [Carrier P α] (p : P) (F : α) := p ∈ (Carrier.carrier F)

def lies_int {P : Type _} [EuclideanPlane P] {α : Type _} [Interior P α] (p : P) (F : α) := p ∈ (Interior.interior F)

-- def lies_in {P : Type _} [EuclideanPlane P] {α : Type _} [Carrier P α] [Interior P α] (p : P) (F : α) : Prop := lies_int p F ∨ lies_on p F

def is_intx {P : Type _} [EuclideanPlane P] {α β: Type _} [Carrier P α] [Carrier P β] (p : P) (F : α) (G : β) := p ∈ (Carrier.carrier F) ∧ p ∈ (Carrier.carrier G)

theorem is_intx.symm {P : Type _} [EuclideanPlane P] {α β: Type _} [Carrier P α] [Carrier P β] {p : P} {F : α} {G : β} (h : is_intx p F G) : is_intx p G F := And.symm h

scoped infix : 50 "LiesOn" => lies_on
scoped infix : 50 "LiesInt" => lies_int
-- scoped infix : 50 "LiesIn" => lies_in
-- scoped notation p "IsIntx" F G => (is_intx p F G) -- this notation doesn't work as imagined


class Convex2D (P: Type _) [EuclideanPlane P] (α : Type _) extends (Carrier P α), (Interior P α) where
  convexity : ∀ (F : α) (A B : P), (A LiesOn F) → (B LiesOn F) → ∃ (t : ℝ), t • (B -ᵥ A) +ᵥ A LiesOn F
  int_of_carrier : ∀ (F : α) (A : P), (A LiesInt F) → ∃ (B₁ B₂ B₃ : P) (t₁ t₂ t₃ : ℝ), (B₁ LiesOn F) ∧ (B₂ LiesOn F) ∧ (B₃ LiesOn F) ∧ (0 < t₁) ∧ (0 < t₂) ∧ (0 < t₃) ∧ (t₁ • VEC A B₁ + t₂ • VEC A B₂ + t₃ • VEC A B₃ = 0)

/- Theorem interior is convex-/

/- Intersection -/

/-! 
-- scoped notation p "LiesInt" F => HasLiesInt.lies_int p F

def IsFallsOn {α β : Type _} (A : α) (B : β) [HasLiesOn P α] [HasLiesOn P β] : Prop := ∀ (p : P), (p LiesOn A) → (p LiesOn B) 

def IsFallsIn {α β : Type _} (A : α) (B : β) [HasLiesIn P α] [HasLiesIn P β] : Prop := ∀ (p : P), (p LiesIn A) → (p LiesIn B) 

-- LiesOn → LiesInt is FallsInt ?

scoped notation A "FallsOn" B "Over" P => IsFallsOn P A B
scoped notation A "FallsIn" B "Over" P => IsFallsIn P A B

namespace IsFallsOn

protected theorem refl {P : Type _} {α : Type _} (A : α) [HasLiesOn P α] : A FallsOn A Over P := by tauto

protected theorem trans {P : Type _} {α β γ : Type _} (A : α) (B : β) (C : γ) [HasLiesOn P α] [HasLiesOn P β] [HasLiesOn P γ] : (A FallsOn B Over P) → (B FallsOn C Over P) → (A FallsOn C Over P)   := by tauto

end IsFallsOn

namespace IsFallsIn

protected theorem refl {P : Type _} {α : Type _} (A : α) [HasLiesIn P α] : A FallsIn A Over P := by tauto

protected theorem trans {P : Type _} {α β γ : Type _} (A : α) (B : β) (C : γ) [HasLiesIn P α] [HasLiesIn P β] [HasLiesIn P γ] : (A FallsIn B Over P) → (B FallsIn C Over P) → (A FallsIn C Over P)   := by tauto

end IsFallsIn

def IsIntersectionPoint {P : Type _} {α β : Type _} (p : P) (A : α) (B : β) [HasLiesOn P α] [HasLiesOn P β] := (p LiesOn A) ∧ (p LiesOn B)

scoped notation p "IsIntersectionOf" A B => IsIntersectionPoint p A B

/- 
class HasProj (α : Type _) where
  toProj : (α → Proj)

def parallel {α β : Type _} (A : α) (B : β) [HasProj α] [HasProj β] : Prop := HasProj.toProj A = HasProj.toProj B 

scoped notation A "IsParallelTo" B => parallel A B
scoped notation A "∥" B => parallel A B

namespace parallel

protected theorem refl {α : Type _} (A : α) [HasProj α] : A ∥ A := rfl

protected theorem symm {α β : Type _} (A : α) (B : β) [HasProj α] [HasProj β] : (A ∥ B) → (B ∥ A) := Eq.symm

protected theorem trans {α β γ : Type _} (A : α) (B : β) (C : γ) [HasProj α] [HasProj β] [HasProj γ]: (A ∥ B) → (B ∥ C) → (A ∥ C) := Eq.trans

end parallel 

def perpendicular {α β : Type _} (A : α) (B : β) [HasProj α] [HasProj β] : Prop := sorry

scoped notation A "IsPerpendicularTo" B => perpendicular A B
scoped notation A "⟂" B => perpendicular A B

namespace perpendicular

protected theorem irrefl {α : Type _} (A : α) [HasProj α] : ¬ (A ⟂ A) := by sorry

protected theorem symm {α β : Type _} (A : α) (B : β) [HasProj α] [HasProj β] : (A ⟂ B) → (B ⟂ A) := sorry

end perpendicular

theorem parallel_of_perp_perp {α β γ : Type _} (A : α) (B : β) (C : γ) [HasProj α] [HasProj β] [HasProj γ] : (A ⟂ B) → (B ⟂ C) → (A ∥ C)  := sorry
-/ -/
end EuclidGeom