/- define class of On and In and FallsOn, define LiesOn and IsIntersection, every geometric figure should be an instance of these classes -/

import EuclideanGeometry.Foundation.Axiom.Basic.Plane

noncomputable section
namespace EuclidGeom

-- class PlaneFigure (P: Type _) [EuclideanPlane P] (α : Type _) where

class Carrier (P: Type _) [EuclideanPlane P] (α : Type _) where
  carrier : α → Set P

class Interior (P: Type _) [EuclideanPlane P] (α : Type _) where
  interior : α → Set P


def lies_on {P : Type _} [EuclideanPlane P] {α : Type _} [Carrier P α] (A : P) (F : α) := A ∈ (Carrier.carrier F)

def lies_int {P : Type _} [EuclideanPlane P] {α : Type _} [Interior P α] (A : P) (F : α) := A ∈ (Interior.interior F)

-- def lies_in {P : Type _} [EuclideanPlane P] {α : Type _} [Carrier P α] [Interior P α] (A : P) (F : α) : Prop := lies_int A F ∨ lies_on A F

def is_inx {P : Type _} [EuclideanPlane P] {α β: Type _} [Carrier P α] [Carrier P β] (A : P) (F : α) (G : β) := A ∈ (Carrier.carrier F) ∧ A ∈ (Carrier.carrier G)

theorem is_inx.symm {P : Type _} [EuclideanPlane P] {α β: Type _} [Carrier P α] [Carrier P β] {A : P} {F : α} {G : β} (h : is_inx A F G) : is_inx A G F := And.symm h

scoped infix : 50 "LiesOn" => lies_on
scoped infix : 50 "LiesInt" => lies_int
-- scoped infix : 50 "LiesIn" => lies_in
-- scoped notation A "IsInx" F G => (is_inx A F G) -- this notation doesn't work as imagined

section compatibility

theorem ne_of_lieson_and_not_lieson {P : Type _} [EuclideanPlane P] {α : Type _} [Carrier P α] {F : α} {X Y : P} (hx : X LiesOn F) (hy : ¬ Y LiesOn F) : X ≠ Y := by 
  by_contra h
  rw [h] at hx
  tauto

theorem ne_of_liesint_and_not_liesint {P : Type _} [EuclideanPlane P] {α : Type _} [Interior P α] {F : α} {X Y : P} (hx : X LiesInt F) (hy : ¬ Y LiesInt F) : X ≠ Y := by 
  by_contra h
  rw [h] at hx
  tauto
end compatibility

/- Three figures concurrent at a point -/
def concurrent {P : Type _} [EuclideanPlane P] {α β γ: Type _} [Carrier P α] [Carrier P β] [Carrier P γ] (A : P) (F : α) (G : β) (H : γ) : Prop := A LiesOn F ∧ A LiesOn G ∧ A LiesOn H

class Convex2D (P: Type _) [EuclideanPlane P] (α : Type _) extends (Carrier P α), (Interior P α) where
  convexity : ∀ (F : α) (A B : P), (A LiesOn F) → (B LiesOn F) → ∃ (t : ℝ), t • (B -ᵥ A) +ᵥ A LiesOn F
  int_of_carrier : ∀ (F : α) (A : P), (A LiesInt F) → ∃ (B₁ B₂ B₃ : P) (t₁ t₂ t₃ : ℝ), (B₁ LiesOn F) ∧ (B₂ LiesOn F) ∧ (B₃ LiesOn F) ∧ (0 < t₁) ∧ (0 < t₂) ∧ (0 < t₃) ∧ (t₁ • VEC A B₁ + t₂ • VEC A B₂ + t₃ • VEC A B₃ = 0)

/- Theorem interior is convex-/

/- Intersection -/

end EuclidGeom