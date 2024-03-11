import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence_trash

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

syntax (name := CONGR_SA) "CONGR_SA" : tactic

@[tactic CONGR_SA]
def evalCONGRSA : Tactic := fun stx =>
  match stx with
  | `(tactic| CONGR_SA) => withTheReader Term.Context ({ · with errToSorry := false }) do
      for lemmaName in congrSaLemmas do
        let lemmaName := mkIdent lemmaName
        try
          let t <- `(tactic| apply $lemmaName)
          evalTactic t
          let goals ← Lean.Elab.Tactic.getGoals
          for _ in goals do
            let t1 <- `(tactic| assumption)
            evalTactic t1
          return
        catch
          _ => pure ()
        try
          let t <- `(tactic| apply congr_of_perm_congr; apply $lemmaName)
          evalTactic t
          let goals ← Lean.Elab.Tactic.getGoals
          for _ in goals do
            let t1 <- `(tactic| assumption)
            evalTactic t1
          return
        catch
          _ => pure ()
        try
          let t <- `(tactic| apply congr_of_perm_congr; apply congr_of_perm_congr; apply $lemmaName)
          evalTactic t
          let goals ← Lean.Elab.Tactic.getGoals
          for _ in goals do
            let t1 <- `(tactic| assumption)
            evalTactic t1
          return
        catch
          _ => pure ()
      logInfo "`CONGR_SA` doesn't close any goals"
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

syntax (name := ACONGR_SA) "ACONGR_SA" : tactic

@[tactic ACONGR_SA]
def evalACONGRSA : Tactic := fun stx =>
  match stx with
  | `(tactic| ACONGR_SA) => withTheReader Term.Context ({ · with errToSorry := false }) do
      for lemmaName in acongrSaLemmas do
        let lemmaName := mkIdent lemmaName
        try
          let t <- `(tactic| apply $lemmaName)
          evalTactic t
          let goals ← Lean.Elab.Tactic.getGoals
          for _ in goals do
            let t1 <- `(tactic| assumption)
            evalTactic t1
          return
        catch
          _ => pure ()
        try
          let t <- `(tactic| apply acongr_of_perm_acongr; apply $lemmaName)
          evalTactic t
          let goals ← Lean.Elab.Tactic.getGoals
          for _ in goals do
            let t1 <- `(tactic| assumption)
            evalTactic t1
          return
        catch
          _ => pure ()
        try
          let t <- `(tactic| apply acongr_of_perm_acongr; apply acongr_of_perm_acongr; apply $lemmaName)
          evalTactic t
          let goals ← Lean.Elab.Tactic.getGoals
          for _ in goals do
            let t1 <- `(tactic| assumption)
            evalTactic t1
          return
        catch
          _ => pure ()
      logInfo "`ACONGR_SA` doesn't close any goals"
  | _ => throwUnsupportedSyntax

end acongr

section examples

variable {P : Type*} [EuclideanPlane P] {tr_nd₁ tr_nd₂ : TriangleND P}

example (a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value) (e₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length)
  (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) : tr_nd₁.IsCongr tr_nd₂ := by
    congr_sa

-- `This tactic fails now, fix it!!!`
example (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) (a₂ : tr_nd₁.angle₂.value = tr_nd₂.angle₂.value)
  (a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value) : tr_nd₁.IsCongr tr_nd₂ := by
    CONGR_SA

example (a₁ : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value) (e₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length)
  (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) : tr_nd₁.IsACongr tr_nd₂ := by
    acongr_sa

example (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) (a₁ : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value)
  (a₂ : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value) : tr_nd₁.IsACongr tr_nd₂ := by
    ACONGR_SA

end examples

section specific_examples

variable {P : Type*} [EuclideanPlane P] {A B C D E F : P} (not_collinear_ABC : ¬ Collinear A B C) (not_collinear_DEF : ¬ Collinear D E F)

example (a₁ : ∠ B A C (ne_of_not_collinear not_collinear_ABC).2.2 (ne_of_not_collinear not_collinear_ABC).2.1.symm = ∠ E D F (ne_of_not_collinear not_collinear_DEF).2.2 (ne_of_not_collinear not_collinear_DEF).2.1.symm) (e₂ : dist C A = dist F D) (e₃ : (SEG A B).length = (SEG D E).length) : (TRI_nd A B C not_collinear_ABC).IsCongr (TRI_nd D E F not_collinear_DEF) := by
  CONGR_SA

end specific_examples

end EuclidGeom
