import Lean.Meta.Basic
import Lean.Elab
import Lean.Message
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence

namespace EuclidGeom

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic

def tryCloseMainGoal (candidate : List Expr) : TacticM Unit := do
  for e in candidate do
    try
      closeMainGoal e
    catch
    | _ => continue -- should show some information, if failed

def tryEvalExact (candidate : List Term) : TacticM Unit := do
  let goaltype ← getMainTarget
  IO.println s!"{candidate.length}"
  for t in candidate do
    let r ← elabTermEnsuringType t goaltype
    IO.println s!"Loop at {t}"
    IO.println s!"Try Block"
    try
      closeMainGoalUsing (checkUnassigned := false)
        fun type => do
          let mvarCounterSaved := (← getMCtx).mvarCounter
          let r ← elabTermEnsuringType t type
          logUnassignedAndAbort (← filterOldMVars (← getMVars r) mvarCounterSaved)
          return r
    catch
    | .error s mes => 
      IO.println s!"  {s}failed. {← mes.toString} continue"
      continue
    | _ => 
      IO.println s!"  failed. internal error. continue"
      continue
    IO.println s!"Not Catched, after try block"

-- the tactic `by_SAS`
syntax (name := SAS) "by_SAS" (ppSpace colGt term:max) (ppSpace colGt term:max) (ppSpace colGt term:max) : tactic

def mkSASSyntax (l : List Term) : Term := Syntax.mkApp (mkIdent `EuclidGeom.congr_of_SAS) (Array.mk l)

@[tactic SAS]
def evalSAS : Tactic := fun stx =>
  match stx with
  | `(tactic| by_SAS $t₁ $t₂ $t₃) => do
    let TermList : List Term := [t₁, t₂, t₃]
    let TermCandidate : List Term := List.map mkSASSyntax (TermList.permutations)
    IO.println s!"{TermCandidate}"
    tryEvalExact TermCandidate
    IO.println s!" Checkpoint2 reached"
  | _ => throwUnsupportedSyntax


example {P : Type _} [EuclideanPlane P] {tr_nd₁ tr_nd₂ : Triangle_nd P} (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) : tr_nd₁.1 IsCongrTo tr_nd₂.1 := by
  sorry
  -- exact congr_of_SAS e₂ a₁ e₃
  -- by_SAS a₁ e₂ e₃

-- the tactic `by_add_comm`
syntax (name := by_add_comm) "by_add_comm" (ppSpace colGt term:max) (ppSpace colGt term:max) : tactic

def mkAddCommSyntax (l : List Term) : Term := Syntax.mkApp (mkIdent `Nat.add_comm) (Array.mk l)

@[tactic by_add_comm]
def evalByAddComm : Tactic := fun stx =>
  match stx with
  | `(tactic| by_add_comm $t₁ $t₂) => do
    let TermList : List Term := [t₁, t₂]
    let TermCandidate : List Term := List.map mkAddCommSyntax (TermList.permutations)
    IO.println s!"{TermCandidate}"
    tryEvalExact TermCandidate
    IO.println s!" Checkpoint2 reached"
  | _ => throwUnsupportedSyntax

example (m n : Nat) : n + m = m + n := by
sorry
  -- exact add_comm n m
  -- by_add_comm m n
  -- by_add_comm n m

syntax (name:= by_SAS') "by_SAS'" (ppSpace colGt term:max) (ppSpace colGt term:max) (ppSpace colGt term:max) : tactic

@[tactic by_SAS']
def evalBySAS' : Tactic := sorry