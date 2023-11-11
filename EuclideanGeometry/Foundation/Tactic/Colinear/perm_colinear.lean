import EuclideanGeometry.Foundation.Axiom.Linear.Colinear

namespace EuclidGeom

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Qq

variable {P : Type _} [EuclideanPlane P]

def extractColinear (expr : Q(Prop)) : MetaM (Option Expr) :=
  match expr with
  | ~q(@EuclidGeom.colinear _ (_) _ _ _) =>
      return .some expr
  | _ => return .none

def getColinearDeclNames : TacticM (List Name) := withMainContext do
  flip (<- getLCtx).foldlM [] fun acc x => do
    let type := x.type
    pure $ match <- (extractColinear type) with
    | .some _ => x.userName :: acc
    | .none => acc

syntax (name := perm_colinear) "perm_colinear"  : tactic

@[tactic perm_colinear]
def evalPerm_colinear : Tactic := fun stx =>
  match stx with
  | `(tactic| perm_colinear) => withTheReader Term.Context ({· with errToSorry := false }) do
    let colinearDeclNames <- getColinearDeclNames
    for x0 in colinearDeclNames do
      let x0 := mkIdent x0
      try
        let t <- `(tactic| refine $x0)
        evalTactic t
        return
      catch
        _ => pure ()
      try
        let t <- `(tactic| refine flip_colinear_fst_snd $x0)
        evalTactic t
        return
      catch
        _ => pure ()
      try
        let t <- `(tactic| refine flip_colinear_snd_trd $x0)
        evalTactic t
        return
      catch
        _ => pure ()
      try
        let t <- `(tactic| refine flip_colinear_fst_snd (flip_colinear_snd_trd $x0))
        evalTactic t
        return
      catch
        _ => pure ()
      try
        let t <- `(tactic| refine flip_colinear_snd_trd (flip_colinear_fst_snd $x0))
        evalTactic t
        return
      catch
        _ => pure ()
      try
        let t <- `(tactic| refine flip_colinear_fst_snd (flip_colinear_snd_trd (flip_colinear_fst_snd $x0)))
        evalTactic t
        return
      catch
        _ => pure ()
      logInfo "`perm_colinear` doesn't close any goals"
  | _ => throwUnsupportedSyntax


example {A B C : P} {h : colinear B C A} : colinear A B C := by
  perm_colinear

end EuclidGeom
