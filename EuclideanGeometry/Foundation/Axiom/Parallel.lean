import EuclideanGeometry.Foundation.Axiom.Line

noncomputable section
namespace EuclidGeom

inductive LinearObj (P : Type _) [EuclideanPlane P] where 
  | vec (v : Vec) (h : v ≠ 0)
  | dir (v : Dir)
  | ray (r : Ray P)
  | seg (s : Seg P) (hs : s.is_nontriv)
  | line (l : Line P)

variable {P : Type _} [EuclideanPlane P]

namespace LinearObj

def toProj (l : LinearObj P) : Proj :=
  match l with
  | vec v h => Vec.toProj_of_nonzero v h
  | dir v => v.toProj
  | ray r => r.toProj
  | seg s nontriv => s.toProj_of_nontriv nontriv
  | line l => l.toProj

def IsOnLinearObj (a : P) (l : LinearObj P) : Prop :=
  match l with
  | vec v h => False
  | dir v => False
  | ray r => a LiesOnRay r
  | seg s nontriv => a LiesOnSeg s
  | line l => a ∈ l.carrier

end LinearObj

scoped infix : 50 "LiesOnLinearObj" => LinearObj.IsOnLinearObj

def parallel (l₁ l₂: LinearObj P) : Prop := l₁.toProj = l₂.toProj

instance : IsEquiv (LinearObj P) parallel where
  refl _ := rfl
  symm _ _ := Eq.symm
  trans := sorry -- a big, messy theorem

scoped infix : 50 "ParallelTo" => parallel

scoped infix : 50 "∥" => parallel

/- lots of trivial parallel relation of vec of 2 pt lies on Line, coersions, ... -/

section LiesOn

end LiesOn

end EuclidGeom