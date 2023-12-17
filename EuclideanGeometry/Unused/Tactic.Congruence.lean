import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence
import EuclideanGeometry.Foundation.Tactic.Congruence.Attr

namespace EuclidGeom

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic
open Qq

def liftOrElse [Monad m] (xs : m $ Option A) (ys : m $ Option A) : m (Option A) := do
  match <- xs with
  | .some x => return x
  | .none => do match <- ys with
    | .some y => return y
    | .none => return .none

def extractSegLengthEq (expr : Q(Prop)) : MetaM (Option Unit) :=
  match expr with
  | ~q(@EuclidGeom.Seg.length _ (_) _ = @EuclidGeom.Seg.length _ (_) _) =>
      return ()
  | _ => return .none

def extractAngleValueEq (expr : Q(Prop)) : MetaM (Option Unit) :=
  match expr with
  | ~q(@EuclidGeom.Angle.value _ (_) _ = @EuclidGeom.Angle.value _ (_) _) =>
      return ()
  | _ => return .none

def getCongrDeclNames : TacticM (List Name) := withMainContext do
  flip (<- getLCtx).foldlM [] fun acc x => do
    let type := x.type
    pure $ match <- liftOrElse (extractSegLengthEq type) (extractAngleValueEq type) with
    | .some _ => x.userName :: acc
    | .none => acc

def getCongrSaLemmas : MetaM (List Name) := do return congrSaExtension.getState (← getEnv)

syntax (name := congr_sa) "congr_sa" : tactic

@[tactic congr_sa]
def evalCongrSa : Tactic := fun stx =>
  match stx with
  | `(tactic| congr_sa) => withTheReader Term.Context ({ · with errToSorry := false }) do
      let congrDeclNames <- getCongrDeclNames
      let congrSaLemmas <- getCongrSaLemmas
      for lemmaName in congrSaLemmas do
        for x0 in congrDeclNames do
          for x1 in congrDeclNames do
            for x2 in congrDeclNames do
              let lemmaName := mkIdent lemmaName
              let x0 := mkIdent x0
              let x1 := mkIdent x1
              let x2 := mkIdent x2
              try
                let t <- `(tactic| refine $lemmaName $x0 $x1 $x2)
                evalTactic t
                return
              catch
                _ => continue
      logInfo "`congr_sa` doesn't close any goals"
  | _ => throwUnsupportedSyntax

example {P : Type _} [EuclideanPlane P] {tr_nd₁ tr_nd₂ : TriangleND P}
  (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length)
  (a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value)
  (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length)
    : tr_nd₁.1 IsCongrTo tr_nd₂.1 := by
      congr_sa
