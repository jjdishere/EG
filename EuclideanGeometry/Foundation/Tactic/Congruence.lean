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

-- #eval insert_everywhere 0 [1,2,3]

def PermList {α : Type _} (lst : List α) : List (List α) := 
  match lst with
  | [] => [[]]
  | x :: xs => List.join $ List.map (insert_everywhere x ·) $ PermList xs
-- #eval PermList [1,2,3]


def tryCloseMainGoal (candidate : List Expr) : TacticM Unit := do
  for e in candidate do
    try
      closeMainGoal e
    catch
    | _ => continue -- should show some information, if failed

def tryEvalExact (candidate : List Term) : TacticM Unit := do
  for t in candidate do
    IO.println s!"Try Block"
    try
      (
      closeMainGoalUsing (checkUnassigned := false)
        fun type => do
          let mvarCounterSaved := (← getMCtx).mvarCounter
          let r ← elabTermEnsuringType t type
          logUnassignedAndAbort (← filterOldMVars (← getMVars r) mvarCounterSaved)
          return r
      )
      IO.println s!"  successfully tried"
    catch
    | _ => 
      IO.println s!"  failed. continue"
      continue
    IO.println s!"After try block"

-- the tactic `by_SAS`
syntax (name := SAS) "by_SAS" (ppSpace colGt term:max) (ppSpace colGt term:max) (ppSpace colGt term:max) : tactic

def mkSASSyntax (l : List Term) : Term := Syntax.mkApp (mkIdent `EuclidGeom.congr_of_SAS) (Array.mk l)

@[tactic SAS]
def evalSAS : Tactic := fun stx =>
  match stx with
  | `(tactic| by_SAS $t₁ $t₂ $t₃) => do
    let TermList : List Term := [t₁, t₂, t₃]
    let TermCandidate : List Term := List.map mkSASSyntax (PermList TermList)
    tryEvalExact TermCandidate
    IO.println s!" Checkpoint2 reached"
  | _ => throwUnsupportedSyntax
/-
example {P : Type _} [EuclideanPlane P] {tr_nd₁ tr_nd₂ : Triangle_nd P} (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) : tr_nd₁.1 IsCongrTo tr_nd₂.1 := by
  -- exact congr_of_SAS e₂ a₁ e₃
  by_SAS a₁ e₂ e₃
-/