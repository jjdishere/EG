import Lean.Meta.Basic
import Lean.Elab
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence

namespace EuclidGeom

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic

def insert_everywhere {α : Type _} (x : α) (lst : List α) : List (List α) := 
  match lst with 
  | [] => [[x]]
  | y :: ys => [x :: y :: ys] ++ (List.map (y :: ·) (insert_everywhere x ys))

#eval insert_everywhere 0 [1,2,3]

def PermList {α : Type _} (lst : List α) : List (List α) := 
  match lst with
  | [] => [[]]
  | x :: xs => List.join $ List.map (insert_everywhere x ·) $ PermList xs
#eval PermList [1,2,3]

def tryCloseMainGoal (candidate : List Expr) : TacticM Unit := do
  for e in candidate do
    try
      closeMainGoal e
    catch
    | _ => continue -- should show some information, if failed

def tryEvalExact (candidate : List Term) : TacticM Unit := do
  for t in candidate do
    try
      evalExact t
    catch
    | _ => 
      IO.println s!"  {t}"
      continue
    break

-- the tactic `by_SAS`
syntax (name := SAS) "by_SAS" (ppSpace colGt term:max) (ppSpace colGt term:max) (ppSpace colGt term:max) : tactic

--`should modify syntax using macro, so that I don't need to fill {P} [Euclidean P]...`
def mkSASExpr (l : List Expr) : Expr := mkAppN (.const `EuclidGeom.congr_of_SAS [Level.zero]) (Array.mk l)

def mkSASSyntax (l : List Term) : Term := Syntax.mkApp (mkIdent `EuclidGeom.congr_of_SAS) (Array.mk l)

-- the following can be modified to ensuring type when elab, if we get the goal type first, then try 3! times of elabTermEnsuringType.
@[tactic SAS] -- should provide more information when failed
def evalSAS : Tactic := fun stx =>
  match stx with
  | `(tactic| by_SAS $t₁ $t₂ $t₃) => do
    let TermList : List Term := [t₁, t₂, t₃]
    let TermCandidate : List Term := List.map mkSASSyntax (PermList TermList)
    IO.println s!"  {TermCandidate}"
    -- tryEvalExact TermCandidate
    evalExact (Syntax.mkApp (mkIdent `EuclidGeom.congr_of_SAS) (Array.mk [t₁, t₂, t₃]))
  | _ => throwUnsupportedSyntax

/-
-- the following can be modified to ensuring type when elab, if we get the goal type first, then try 3! times of elabTermEnsuringType.
@[tactic SAS] -- should provide more information when failed
def evalSAS : Tactic := fun stx =>
  match stx with
  | `(tactic| by_SAS $t₁ $t₂ $t₃) => do
    let e₁ ← Tactic.elabTerm t₁ .none 
    let e₂ ← Tactic.elabTerm t₂ .none
    let e₃ ← Tactic.elabTerm t₃ .none
    let ExprList : List Expr := [e₁, e₂, e₃]
    let ExprCandidate : List Expr := List.map mkSASExpr (PermList ExprList)
    tryCloseMainGoal ExprCandidate

  | _ => throwUnsupportedSyntax
-/

example {P : Type _} [EuclideanPlane P] {tr_nd₁ tr_nd₂ : Triangle_nd P} (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) : tr_nd₁.1 IsCongrTo tr_nd₂.1 := by
  -- exact congr_of_SAS e₂ a₁ e₃
  by_SAS e₂ a₁ e₃
