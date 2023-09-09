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

section coersion

-- `Is this correct?`

instance : Coe (Dir) (LinearObj P) where
  coe := fun v => LinearObj.dir v

instance : Coe (Ray P) (LinearObj P) where
  coe := fun r => LinearObj.ray r

instance : Coe (Line P) (LinearObj P) where
  coe := fun l => LinearObj.line l

end coersion

namespace LinearObj

def toProj (l : LinearObj P) : Proj :=
  match l with
  | vec v h => Vec.toProj_of_nonzero v h
  | dir v => v.toProj
  | ray r => r.toProj
  | seg s nontriv => s.toProj_of_nontriv nontriv
  | line l => l.toProj

/- No need to define this. Should never talk about a LinearObj directly in future. Only mention it for ∥ ⟂.  
def IsOnLinearObj (a : P) (l : LinearObj P) : Prop :=
  match l with
  | vec v h => False
  | dir v => False
  | ray r => a LiesOn r
  | seg s nontriv => a LiesOn s
  | line l => a ∈ l.carrier
-/

end LinearObj

/-
scoped infix : 50 "LiesOnarObj" => LinearObj.IsOnLinearObj
-/

def parallel (l₁ l₂: LinearObj P) : Prop := l₁.toProj = l₂.toProj

instance : IsEquiv (LinearObj P) parallel where
  refl _ := rfl
  symm _ _ := Eq.symm
  trans _ _ _ := Eq.trans

scoped infix : 50 "ParallelTo" => parallel

scoped infix : 50 "∥" => parallel

/- lots of trivial parallel relation of vec of 2 pt lies on Line, coersions, ... -/

section parallel_theorem

theorem ray_parallel_to_line_assoc_ray (ray : Ray P) : LinearObj.ray ray ParallelTo ray.toLine := sorry

theorem seg_parallel_to_ray_assoc_seg_of_nontriv {seg : Seg P} (nontriv : seg.is_nontriv) : LinearObj.seg seg nontriv ParallelTo seg.toRay_of_nontriv nontriv := sorry


end parallel_theorem

-- If ray₁ and ray₂ are two rays that are not parallel, then the following function returns the unique point of the intersection of the associated two lines. This function is a bit tricky, will come back to this.

def Intersection_of_Rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : P := sorry

scoped notation "RayInt" => Intersection_of_Rays

theorem ray_intersection_lies_on_lines_of_rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : (RayInt h) LiesOnLine ray₁.toLine ∧ (RayInt h) LiesOnLine ray₂.toLine := by sorry

-- If two lines l₁ and l₂ are parallel, then there is a unique point on l₁ ∩ l₂.  The definition of the point uses the ray intersection by first picking a point

theorem exists_unique_intersection_of_nonparallel_lines (l₁ l₂ : Line P) (h : ¬ (l₁ ∥ (LinearObj.line l₂))) : ∃! (p : P), p LiesOnLine l₁ ∧ p LiesOnLine l₂ := by sorry

def intersection_of_nonparallel_line (l₁ l₂ : Line P) (h : ¬ (l₁ ∥ (LinearObj.line l₂))) :  P := by
  choose p _ using (exists_unique_intersection_of_nonparallel_lines l₁ l₂ h)
  use p

scoped notation "LineInt" => intersection_of_nonparallel_line

-- theorem ray_intersection_eq_line_intersection_of_rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : RayInt h = LineInt (Ne.trans (ray_parallel_to_line_assoc_ray ray₁) h) := sorry

end EuclidGeom