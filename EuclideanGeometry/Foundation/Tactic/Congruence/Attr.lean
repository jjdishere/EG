import Lean

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

initialize congrSaExtension : SimpleScopedEnvExtension Name (List Name) <-
  registerSimpleScopedEnvExtension
    { initial := []
    , addEntry := flip (· :: ·)
    }

initialize registerBuiltinAttribute {
  name := `congr_sa
  descr := "Marks a lemma as congr_sa lemma"
  add := fun declName _stx _kind => congrSaExtension.add declName
}
