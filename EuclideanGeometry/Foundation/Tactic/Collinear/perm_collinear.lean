import EuclideanGeometry.Foundation.Axiom.Linear.Collinear

namespace EuclidGeom

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Qq

variable {P : Type _} [EuclideanPlane P]

def extractCollinear (expr : Q(Prop)) : MetaM (Option Expr) :=
  match expr with
  | ~q(@EuclidGeom.collinear _ (_) _ _ _) =>
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
        let t <- `(tactic| refine flip_collinear_fst_snd $x0)
        evalTactic t
        return
      catch
        _ => pure ()
      try
        let t <- `(tactic| refine flip_collinear_snd_trd $x0)
        evalTactic t
        return
      catch
        _ => pure ()
      try
        let t <- `(tactic| refine flip_collinear_fst_snd (flip_collinear_snd_trd $x0))
        evalTactic t
        return
      catch
        _ => pure ()
      try
        let t <- `(tactic| refine flip_collinear_snd_trd (flip_collinear_fst_snd $x0))
        evalTactic t
        return
      catch
        _ => pure ()
      try
        let t <- `(tactic| refine flip_collinear_fst_snd (flip_collinear_snd_trd (flip_collinear_fst_snd $x0)))
        evalTactic t
        return
      catch
        _ => pure ()
      logInfo "`perm_collinear` doesn't close any goals"
  | _ => throwUnsupportedSyntax


example {A B C : P} {h : collinear B C A} : collinear A B C := by
  perm_collinear

end EuclidGeom
