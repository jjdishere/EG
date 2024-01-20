import EuclideanGeometry.Foundation.Axiom.Linear.Collinear

namespace EuclidGeom

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Qq

variable {P : Type*} [EuclideanPlane P]

def extractCollinear (expr : Q(Prop)) : MetaM (Option Expr) :=
  match expr with
  | ~q(@EuclidGeom.Collinear _ (_) _ _ _) =>
      return .some expr
  | _ => return .none

def getCollinearDeclNames : TacticM (List Name) := withMainContext do
  flip (<- getLCtx).foldlM [] fun acc x => do
    let type := x.type
    pure $ match <- (extractCollinear type) with
    | .some _ => x.userName :: acc
    | .none => acc

syntax (name := perm_collinear) "perm_collinear"  : tactic

@[tactic perm_collinear]
def evalPerm_collinear : Tactic := fun stx =>
  match stx with
  | `(tactic| perm_collinear) => withTheReader Term.Context ({· with errToSorry := false }) do
    let collinearDeclNames <- getCollinearDeclNames
    for x0 in collinearDeclNames do
      let x0 := mkIdent x0
      try
        let t <- `(tactic| refine $x0)
        evalTactic t
        return
      catch
        _ => pure ()
      try
        let t <- `(tactic| refine Collinear.perm₁₃₂ $x0)
        evalTactic t
        return
      catch
        _ => pure ()
      try
        let t <- `(tactic| refine Collinear.perm₂₁₃ $x0)
        evalTactic t
        return
      catch
        _ => pure ()
      try
        let t <- `(tactic| refine Collinear.perm₃₁₂ $x0)
        evalTactic t
        return
      catch
        _ => pure ()
      try
        let t <- `(tactic| refine Collinear.perm₂₃₁ $x0)
        evalTactic t
        return
      catch
        _ => pure ()
      try
        let t <- `(tactic| refine Collinear.perm₃₂₁ $x0)
        evalTactic t
        return
      catch
        _ => pure ()
      logInfo "`perm_collinear` doesn't close any goals"
  | _ => throwUnsupportedSyntax


example {A B C : P} {h : Collinear B C A} : Collinear A B C := by
  perm_collinear

end EuclidGeom
