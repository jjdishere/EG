import Mathlib.Analysis.InnerProductSpace.PiL2

import EuclideanGeometry.Foundation.Index
/- here checks things-/

/-
## Part O: Code Gallery
Here exhibits unfamiliar codes for learning.
-/

section HEq
def T {A A' B : Type*} (e : A = A') (f : A → B) : A' → B := by
  rw [← e]
  exact f
theorem heq {A A' B : Type*} (e : A = A') (f : A → B) : HEq f (T e f) := by
  subst e
  rfl
theorem heq' {g : Type* → Type* } {A A' B : Type*} (e : g A = g A') (f : g A → B) : HEq f (T e f) := by
  exact heq e f

#check heq
#check Eq.rec
#check HEq.rec
#check Eq.ndrec
#check Eq.mpr

theorem heq_funext' {c₁ c₂ d : Type*} (e : c₁ = c₂) {f₁ : c₁ → d} {f₂ : c₂ → d} (h : ∀ (s : c₁) (t : c₂), (HEq s t) → f₁ s = f₂ t) : HEq f₁ f₂ := by
  exact Function.hfunext e (fun s t g => (heq_of_eq (h s t g)))

theorem heq_funext_prop {c₁ c₂ : Prop} {d : Type*} (e : c₁ = c₂) {f₁ : c₁ → d} {f₂ : c₂ → d} (h : ∀ (s : c₁) (t : c₂), f₁ s = f₂ t) : HEq f₁ f₂ := by
  exact Function.hfunext e (fun s t _ => (heq_of_eq (h s t)))

theorem heq_funext {c₁ c₂ d: Sort*} (e : c₁ = c₂) {f₁ : c₁ → d} {f₂ : c₂ → d} (h : ∀ (s : c₁) (t : c₂), f₁ s = f₂ t) : HEq f₁ f₂ := Function.hfunext e (fun _ _ _ => (heq_of_eq (h _ _)))


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

variable (P : Type*) [EuclidGeom.EuclideanPlane P] (l : Ray P)
#check l.toDir.toVec
#check @AddAction.toVAdd _ _ _ (@AddTorsor.toAddAction _ _ _ (@NormedAddTorsor.toAddTorsor _ P _ _ _))

end VAddCheck

section raymk

#check Ray.mk

end raymk

/- check angle notation-/
section anglecheck

variable {P : Type*} [h : EuclideanPlane P] (O : P) (A : P) (B : P)
#check ANG A O B

variable (l : GDirSeg P)
#check l.toVec

end anglecheck

variable {P : Type*} [EuclideanPlane P]
theorem test_is_on (A : P) (seg : Seg P) : (p LiesOn seg) = (Seg.IsOn p seg) := rfl


theorem let_test (a : α) (p : α → Prop) : (let x := a; p x) ↔ (∀x, x = a → p x) := by
  constructor
  simp only [forall_eq, imp_self]
  simp only [forall_eq, imp_self]

theorem let_test_prop (α : Prop) (a : α) (p : α → Prop) : (let x := a; p x) ↔ ((a : α) → p a) := by
  constructor
  · simp only
    intro x _
    exact x
  · simp only
    intro x
    exact x _

def main_theorem (A B C : P) (h : ¬ Collinear A B C) : Prop := by
  let hAB : B≠A := by exact (ne_of_not_collinear h).2.2
  let hCB : C ≠ B := by exact (ne_of_not_collinear h).1
  let l₁ := LIN A B hAB
  let l₂ := LIN B C hCB
  let h' : ¬ l₁ ∥ l₂ := sorry
  let E := Line.inx l₁ l₂ h'
  exact (E = B)

example (A B C : P) (h : ¬ Collinear A B C) : main_theorem A B C h := by
  unfold main_theorem
  -- rw [let_test (α := B≠A) (a := (ne_of_not_collinear h).2.2) (p := fun x => let hCB := (_ : C ≠ B);
-- let l₁ := LIN A B x;
-- let l₂ := LIN B C hCB;
-- let h' := (_ : ¬LIN A B (_ : B ≠ A)∥LIN B C (_ : C ≠ B));
-- let E := LineInx l₁ l₂ h';
-- E = B) ]
  rw [let_test_prop (B≠A) (ne_of_not_collinear h).2.2 (fun x => let hCB := (_ : C ≠ B);
 let l₁ := LIN A B x;
 let l₂ := LIN B C hCB;
 let h' := (_ : ¬LIN A B (_ : B ≠ A)∥LIN B C (_ : C ≠ B));
 let E := LineInx l₁ l₂ h';
 E = B) ]
  intro a
  intro x hAB
  simp
  sorry


end EuclidGeom
