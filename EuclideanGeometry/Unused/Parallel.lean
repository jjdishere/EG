import EuclideanGeometry.Foundation.Axiom.Linear.Line

noncomputable section
namespace EuclidGeom

inductive LinearObj (P : Type _) [EuclideanPlane P] where
  | vec_nd (v : VecND)
  | dir (v : Dir)
  | ray (r : Ray P)
  | seg_nd (s : SegND P)
  | line (l : Line P)

variable {P : Type _} [EuclideanPlane P]

section coercion

-- `Is this correct?`

instance : Coe VecND (LinearObj P) where
  coe := fun v => LinearObj.vec_nd v

instance : Coe Dir (LinearObj P) where
  coe := fun d => LinearObj.dir d

instance : Coe (Ray P) (LinearObj P) where
  coe := fun r => LinearObj.ray r

instance : Coe (SegND P) (LinearObj P) where
  coe := fun s => LinearObj.seg_nd s

instance : Coe (Line P) (LinearObj P) where
  coe := fun l => LinearObj.line l

end coercion

namespace LinearObj

def toProj (l : LinearObj P) : Proj :=
  match l with
  | vec_nd v => v.toProj
  | dir v => v.toProj
  | ray r => r.toProj
  | seg_nd s => s.toProj
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
scoped infix : 50 " LiesOnarObj " => LinearObj.IsOnLinearObj
-/

-- Our definition of parallel for LinearObj is very general. Not only can it apply to different types of Objs, but also include degenerate cases, such as ⊆(inclusions), =(equal).

def parallel' {α β: Type _} (l₁ : α) (l₂ : β) [Coe α (LinearObj P)] [Coe β (LinearObj P)] : Prop :=  LinearObj.toProj (P := P) (Coe.coe l₁) = LinearObj.toProj (P := P) (Coe.coe l₂)

-- class PlaneFigure' (P : Type _) [EuclideanPlane P] {α : Type _} where

-- instance : PlaneFigure' P (LinearObj P) where



def parallel (l₁ l₂: LinearObj P) : Prop := l₁.toProj = l₂.toProj

instance : IsEquiv (LinearObj P) parallel where
  refl _ := rfl
  symm _ _ := Eq.symm
  trans _ _ _ := Eq.trans

scoped infix : 50 " ParallelTo " => parallel

scoped infix : 50 " ∥ " => parallel

/- lots of trivial parallel relation of vec of 2 pt lies on Line, coercions, ... -/

section parallel_theorem

theorem ray_parallel_toLine_assoc_ray (ray : Ray P) :  parallel (LinearObj.ray ray) ray.toLine := sorry

theorem seg_parallel_toray_assoc_seg_of_nontriv (seg_nd : SegND P) : LinearObj.seg_nd seg_nd ∥ seg_nd.toRay := sorry

end parallel_theorem


section intersection_theorem

-- Let us consider the intersection of lines first.
-- If two lines l₁ and l₂ are parallel, then there is a unique point on l₁ ∩ l₂.  The definition of the point uses the ray intersection by first picking a point

theorem exists_intersection_of_nonparallel_lines {l₁ l₂ : Line P} (h : ¬ (l₁ ∥ (LinearObj.line l₂))) : ∃ p : P, p LiesOn l₁ ∧ p LiesOn l₂ := by
  rcases l₁.nontriv with ⟨A, ⟨B, hab⟩⟩
  rcases l₂.nontriv with ⟨C, ⟨D, hcd⟩⟩
  have e' : SegND.toProj ⟨SEG A B, hab.2.2⟩ ≠ SegND.toProj ⟨SEG C D, hcd.2.2⟩ := by
    rw [line_toProj_eq_seg_nd_toProj_of_lies_on hab.1 hab.2.1 hab.2.2, line_toProj_eq_seg_nd_toProj_of_lies_on hcd.1 hcd.2.1 hcd.2.2]
    exact h
  have w : ∃ x y, VEC A C = x • VEC A B + y • VEC C D := linear_combination_of_not_colinear _ e'
  rcases w with ⟨x, ⟨y, e⟩⟩
  let X := x • VEC A B +ᵥ A
  use X
  constructor
  exact (lies_on_iff_colinear_of_ne_lies_on_lies_on hab.2.2 hab.1 hab.2.1 _).2 (colinear_of_vec_eq_smul_vec (vec_of_pt_vadd_pt_eq_vec _ _))
  apply (lies_on_iff_colinear_of_ne_lies_on_lies_on hcd.2.2 hcd.1 hcd.2.1 _).2
  have e'' : VEC C X = (-y) • VEC C D := by
    rw [← vec_sub_vec A _ _, vec_of_pt_vadd_pt_eq_vec _ _, e]
    simp
  exact colinear_of_vec_eq_smul_vec e''

theorem exists_unique_intersection_of_nonparallel_lines {l₁ l₂ : Line P} (h : ¬ (l₁ ∥ (LinearObj.line l₂))) : ∃! p : P, p LiesOn l₁ ∧ p LiesOn l₂ := by
  rcases (exists_intersection_of_nonparallel_lines h) with ⟨X, ⟨h₁, h₂⟩⟩
  use X
  simp [h₁, h₂]
  intro X' h₁' h₂'
  by_contra n
  have e : l₁ = l₂ := by
    rw [← eq_line_of_pt_pt_of_ne n h₁ h₁']
    exact eq_line_of_pt_pt_of_ne n h₂ h₂'
  tauto

def intersection_of_nonparallel_line (l₁ l₂ : Line P) (h : ¬ (l₁ ∥ (LinearObj.line l₂))) : P :=
  Classical.choose (exists_unique_intersection_of_nonparallel_lines h)
  -- by choose X _ using (exists_unique_intersection_of_nonparallel_lines h)
  -- use X

scoped notation "LineInt" => intersection_of_nonparallel_line

theorem intersection_of_nonparallel_line_lies_on_fst_line {l₁ l₂ : Line P} (h : ¬ (l₁ ∥ (LinearObj.line l₂))) : (LineInt l₁ l₂ h) LiesOn l₁ := by
  exact (Classical.choose_spec (exists_unique_intersection_of_nonparallel_lines h)).1.1

theorem intersection_of_nonparallel_line_lies_on_snd_line {l₁ l₂ : Line P} (h : ¬ (l₁ ∥ (LinearObj.line l₂))) : (LineInt l₁ l₂ h) LiesOn l₂ := by
  exact (Classical.choose_spec (exists_unique_intersection_of_nonparallel_lines h)).1.2

-- Now let's come to rays.
-- If ray₁ and ray₂ are two rays that are not parallel, then the following function returns the unique point of the intersection of the associated two lines. This function is a bit tricky, will come back to this.
-- `Should we define this concept? Why don't we just use Intersection of Lines and use coercion (ray : Line)`
def Intersection_of_Lines_of_Rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : P := sorry

scoped notation "RayInx" => Intersection_of_Lines_of_Rays

theorem ray_intersection_lies_on_lines_of_rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : (RayInx h) LiesOn ray₁.toLine ∧ (RayInx h) LiesOn ray₂.toLine := by sorry

-- theorem ray_intersection_eq_line_intersection_of_rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : RayInt h = LineInt (Ne.trans (ray_parallel_toLine_assoc_ray ray₁) h) := sorry

end intersection_theorem

end EuclidGeom
