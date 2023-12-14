import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence

namespace EuclidGeom

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Qq

section congr

def liftOrElse {m A} [Monad m] (xs : m $ Option A) (ys : m $ Option A) : m (Option A) := do
  match <- xs with
  | .some x => return x
  | .none => match <- ys with
    | .some y => return y
    | .none => return .none

def extractSegLengthEq (expr : Q(Prop)) : MetaM (Option Expr) :=
  match expr with
  | ~q(@EuclidGeom.Seg.length _ (_) _ = @EuclidGeom.Seg.length _ (_) _) =>
      return .some expr
  | _ => return .none

def extractAngleValueEq (expr : Q(Prop)) : MetaM (Option Expr) :=
  match expr with
  | ~q(@EuclidGeom.Angle.value _ (_) _ = @EuclidGeom.Angle.value _ (_) _) =>
      return .some expr
  | _ => return .none

def getCongrDeclNames : TacticM (List Name) := withMainContext do
  flip (<- getLCtx).foldlM [] fun acc x => do
    let type := x.type
    pure $ match <- liftOrElse (extractSegLengthEq type) (extractAngleValueEq type) with
    | .some _ => x.userName :: acc
    | .none => acc

def congrSaLemmas : List Name :=
  [ ``TriangleND.congr_of_SAS
  , ``TriangleND.congr_of_ASA
  , ``TriangleND.congr_of_AAS
  ]

syntax (name := congr_sa) "congr_sa" : tactic

@[tactic congr_sa]
def evalCongrSa : Tactic := fun stx =>
  match stx with
  | `(tactic| congr_sa) => withTheReader Term.Context ({ · with errToSorry := false }) do
      let congrDeclNames <- getCongrDeclNames
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

end congr

section acongr

def extractNegAngleValueEq (expr : Q(Prop)) : MetaM (Option Expr) :=
  match expr with
  | ~q(@EuclidGeom.Angle.value _ (_) _ = - @EuclidGeom.Angle.value _ (_) _) =>
      return .some expr
  | _ => return .none

def getACongrDeclNames : TacticM (List Name) := withMainContext do
  flip (<- getLCtx).foldlM [] fun acc x => do
    let type := x.type
    pure $ match <- liftOrElse (extractSegLengthEq type) (extractNegAngleValueEq type) with
    | .some _ => x.userName :: acc
    | .none => acc

def acongrSaLemmas : List Name :=
  [ ``TriangleND.acongr_of_SAS
  , ``TriangleND.acongr_of_ASA
  , ``TriangleND.acongr_of_AAS
  ]

syntax (name := acongr_sa) "acongr_sa" : tactic

@[tactic acongr_sa]
def evalACongrSa : Tactic := fun stx =>
  match stx with
  | `(tactic| acongr_sa) => withTheReader Term.Context ({ · with errToSorry := false }) do
      let acongrDeclNames <- getACongrDeclNames
      for lemmaName in acongrSaLemmas do
        for x0 in acongrDeclNames do
          for x1 in acongrDeclNames do
            for x2 in acongrDeclNames do
              let lemmaName := mkIdent lemmaName
              let x0 := mkIdent x0
              let x1 := mkIdent x1
              let x2 := mkIdent x2
              try
                let t <- `(tactic| exact $lemmaName $x0 $x1 $x2)
                evalTactic t
                return
              catch
                _ => continue
      logInfo "`acongr_sa` doesn't close any goals"
  | _ => throwUnsupportedSyntax

end acongr

section examples

variable {P : Type _} [EuclideanPlane P] {tr_nd₁ tr_nd₂ : TriangleND P}

example (a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value) (e₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length)
  (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) : tr_nd₁.IsCongr tr_nd₂ := by
    congr_sa
/-
-- `This tactic fails now, fix it!!!`
example (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) (a₂ : tr_nd₁.angle₂.value = tr_nd₂.angle₂.value)
  (a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value) : tr_nd₁.IsCongr tr_nd₂ := by
    congr_sa

example (a₁ : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value) (e₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length)
  (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) : tr_nd₁.IsACongr tr_nd₂ := by
    acongr_sa

example (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) (a₁ : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value)
  (a₂ : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value) : tr_nd₁.IsACongr tr_nd₂ := by
    acongr_sa

end examples

end EuclidGeom
-/
