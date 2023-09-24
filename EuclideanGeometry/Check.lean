import Mathlib.Analysis.InnerProductSpace.PiL2

import EuclideanGeometry.Foundation.Index
/- here checks things-/

/-
## Part O: Code Gallery
Here exhibits unfamiliar codes for learning.
-/

section HEq
def T {A A' B : Type _} (e : A = A') (f : A → B) : A' → B := by
  rw [← e]
  exact f
theorem heq {A A' B : Type _} (e : A = A') (f : A → B) : HEq f (T e f) := by 
  subst e
  rfl
theorem heq' {g : Type _ → Type _ } {A A' B : Type _} (e : g A = g A') (f : g A → B) : HEq f (T e f) := by
  exact heq e f

#check heq
#check Eq.rec
#check HEq.rec
#check Eq.ndrec
#check Eq.mpr

theorem heq_funext' {c₁ c₂ d : Type _} (e : c₁ = c₂) {f₁ : c₁ → d} {f₂ : c₂ → d} (h : ∀ (s : c₁) (t : c₂), (HEq s t) → f₁ s = f₂ t) : HEq f₁ f₂ := by
  exact Function.hfunext e (fun s t g => (heq_of_eq (h s t g)))

theorem heq_funext_prop {c₁ c₂ : Prop} {d : Type _} (e : c₁ = c₂) {f₁ : c₁ → d} {f₂ : c₂ → d} (h : ∀ (s : c₁) (t : c₂), f₁ s = f₂ t) : HEq f₁ f₂ := by
  exact Function.hfunext e (fun s t _ => (heq_of_eq (h s t)))

theorem heq_funext {c₁ c₂ d: Sort _} (e : c₁ = c₂) {f₁ : c₁ → d} {f₂ : c₂ → d} (h : ∀ (s : c₁) (t : c₂), f₁ s = f₂ t) : HEq f₁ f₂ := Function.hfunext e (fun _ _ _ => (heq_of_eq (h _ _)))


end HEq

/- 
## Part I: Geometric Playground
Check whether geometric constructions, theorems are mathematically correct.
-/


/-
## Part II: Type Reassurance
Check the where a type is behaved as designed 
-/
namespace EuclidGeom
/- check instance VAdd-/
section VAddCheck

variable (P : Type _) [EuclidGeom.EuclideanPlane P] (l : Ray P)
#check l.toDir.toVec
#check @AddAction.toVAdd _ _ _ (@AddTorsor.toAddAction _ _ _ (@NormedAddTorsor.toAddTorsor _ P _ _ _))

end VAddCheck

section raymk

#check Ray.mk

end raymk

/- check angle notation-/
section anglecheck

variable {P : Type _} [h : EuclideanPlane P] (O : P) (A : P) (B : P)
#check ANG A O B

variable (l : GDirSeg P)
#check l.toVec

end anglecheck

variable {P : Type _} [EuclideanPlane P]
theorem test_is_on (A : P) (seg : Seg P) : (p LiesOn seg) = (Seg.IsOn p seg) := rfl


end EuclidGeom