import EuclideanGeometry.Foundation.Axiom.Line

noncomputable section
namespace EuclidGeom

inductive LinearObj (P : Type _) [EuclideanPlane P] where 
  | vec (v : ℝ × ℝ) (h : v ≠ 0)
  | uni_vec (v : UniVec)
  | ray (r : Ray P)
  | seg (s : Seg P) (nontriv : s.is_nontriv)
  | line (l : Line P)

namespace LinearObj

variable {P : Type _} [EuclideanPlane P]

def toProj (l : LinearObj P) : Proj :=
  match l with
  | vec v h => (UniVec.normalize v h : Proj)
  | uni_vec v => (v : Proj)
  | ray r => (r.direction : Proj)
  | seg s nontriv => ((Seg.toRay_of_nontriv s nontriv).direction : Proj)
  | line l => sorry

def parallel (l₁ l₂: LinearObj P) : Prop := sorry

end LinearObj

end EuclidGeom