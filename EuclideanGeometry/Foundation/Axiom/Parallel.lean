import EuclideanGeometry.Foundation.Axiom.Line

noncomputable section
namespace EuclidGeom

inductive LinearObj (P : Type _) [EuclideanPlane P] where 
  | vec (v : ℝ × ℝ) (h : v ≠ 0)
  | uni_vec (v : UniVec)
  | ray (r : Ray P)
  | seg (s : Seg P) (nontriv : s.is_nontriv)
  | line (l : Line P)

variable {P : Type _} [EuclideanPlane P]

namespace LinearObj

def toProj (l : LinearObj P) : Proj :=
  match l with
  | vec v h => StdR2.toProj_of_nonzero v h
  | uni_vec v => v.toProj
  | ray r => r.toProj
  | seg s nontriv => s.toProj_of_nontriv nontriv
  | line l => l.toProj

def IsOnLinearObj (a : P) (l : LinearObj P) : Prop :=
  match l with
  | vec v h => False
  | uni_vec v => False
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


end EuclidGeom