/- define class of On and In and FallsOn, define LiesOn and IsIntersection, every geometric figure should be an instance of these classes -/

import EuclideanGeometry.Foundation.Axiom.Plane

noncomputable section
namespace EuclidGeom

variable (P : Type _) [EuclideanPlane P]

class HasLiesOn (α : Type _) where
  lies_on : P → α → Prop

class HasLiesIn (α : Type _) where
  lies_in : P → α → Prop

scoped notation p "LiesOn" F => HasLiesOn.lies_on p F
scoped notation p "LiesIn" F => HasLiesIn.lies_in p F

class HasFallsOn (α β : Type _) [HasLiesOn P α] [HasLiesOn P β] where
  falls_on : α → β → Prop
  lies_on_falls_on : ∀ (p : P) (A : α) (B : β), HasLiesOn.lies_on p A → falls_on A B → HasLiesOn.lies_on p B

class HasFallsIn (α β : Type _) [HasLiesIn P α] [HasLiesIn P β] where
  falls_in : α → β → Prop
  lies_in_falls_in : ∀ (p : P) (A : α) (B : β), HasLiesIn.lies_in p A → falls_in A B → HasLiesIn.lies_in p B

scoped notation A "FallsOn" B => HasFallsOn.falls_on A B
scoped notation A "FallsIn" B => HasFallsIn.falls_in A B

def IsIntersectionPoint {α β : Type _} (p : P) (A : α) (B : β) [HasLiesOn P α] [HasLiesOn P β] := (p LiesOn A) ∧ (p LiesOn B)

scoped notation p "IsIntersectionOf" A B => IsIntersectionPoint p A B

class HasProj (α : Type _) where
  toProj : (α → Proj)


def parallel {α β : Type _} (A : α) (B : β) [HasProj α] [HasProj β] : Prop := HasProj.toProj A = HasProj.toProj B 

scoped notation A "IsParallelTo" B => parallel A B
scoped notation A "∥" B => parallel A B

namespace parallel

protected theorem refl {α : Type _} (A : α) [HasProj α] : A ∥ A := rfl 

protected theorem symm {α β : Type _} (A : α) (B : β) [HasProj α] [HasProj β] : (A ∥ B) → (B ∥ A) := Eq.symm

protected theorem trans {α β γ : Type _} (A : α) (B : β) (C : γ) [HasProj α] [HasProj β] [HasProj γ]: (A ∥ B) → (B ∥ C) → (A ∥ C)  := Eq.trans

end parallel

end EuclidGeom