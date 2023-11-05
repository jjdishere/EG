import EuclideanGeometry.Foundation.Index
--新加的open和import

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Qq

noncomputable section

-- All exercises are from Aref-Wernick book: Problems and Solutions in Euclidean Geometry Chapter 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Aref_Wernick_Exercise_1_1
/- Two triangles are congruent if two sides and the enclosed median in one triangle are respectively equal to two sides and the enclosed median of the other.

In other words, let $\triangle A_1B_1C_1$ and $\triangle A_2B_2C_2$ be two triangles and let $A_1M_1$ and $A_2M_2$ be the corresponding medians. Suppose that $A_1B_1 = A_2B_2$, $A_1C_1 = A_2C_2$, and $A_1M_1 = A_2M_2$.

Prove that $\triangle A_1B_1C_1$ is congruent to $\triangle A_2B_2C_2$. -/

-- Don't prove this yet, the way to prove this is to extend $A_1M_1$ to $D_1$ so that $A_1 B_1 D_1 C_1$ is a parallelogram... Parallelogram.lean is not ready yet.

end Aref_Wernick_Exercise_1_1

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

namespace Aref_Wernick_Exercise_1_2
/- Let $D$ and $E$ be points on two sides $AB$ and $AC$ of a triangle $ABC$, respectively, such that $BD = BC = CE$. The segments $BE$ and $CD$ intersect at $F$.

Prove that $\angle BFD = \pi / 2 - \angle CAB$. -/

end Aref_Wernick_Exercise_1_2



end EuclidGeom
