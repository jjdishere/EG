import EuclideanGeometry.Foundation.Axiom.Linear.Line'
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex

noncomputable section
namespace EuclidGeom

inductive LinearObj (P : Type _) [EuclideanPlane P] where 
  | vec_nd (v : Vec_nd)
  | dir (v : Dir)
  | ray (r : Ray P)
  | seg_nd (s : Seg_nd P)
  | line (l : Line P)

variable {P : Type _} [EuclideanPlane P]

section coersion

-- `Is this correct?`

instance : Coe Vec_nd (LinearObj P) where
  coe := fun v => LinearObj.vec_nd v

instance : Coe Dir (LinearObj P) where
  coe := fun d => LinearObj.dir d

instance : Coe (Ray P) (LinearObj P) where
  coe := fun r => LinearObj.ray r

instance : Coe (Seg_nd P) (LinearObj P) where
  coe := fun s => LinearObj.seg_nd s

instance : Coe (Line P) (LinearObj P) where
  coe := fun l => LinearObj.line l

end coersion

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
scoped infix : 50 "LiesOnarObj" => LinearObj.IsOnLinearObj
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

scoped infix : 50 "ParallelTo" => parallel

scoped infix : 50 "∥" => parallel

/- lots of trivial parallel relation of vec of 2 pt lies on Line, coersions, ... -/

section parallel_theorem

theorem Ray.para_toLine (ray : Ray P) :  (LinearObj.ray ray) ∥ ray.toLine := sorry

theorem Seg_nd.para_toRay (seg_nd : Seg_nd P) : LinearObj.seg_nd seg_nd ∥ seg_nd.toRay := sorry

theorem Seg_nd.para_toLine (seg_nd : Seg_nd P) : LinearObj.seg_nd seg_nd ∥ seg_nd.toLine := sorry

-- many more...

theorem Ray.para_toLine_of_para (ray ray' : Ray P) (h : LinearObj.ray ray ∥ ray') : (LinearObj.line ray.toLine) ∥ ray'.toLine := h

theorem Ray.not_para_of_not_para_toLine (ray ray' : Ray P) (h : ¬ (LinearObj.line ray.toLine) ∥ ray'.toLine ) : ¬ LinearObj.ray ray ∥ ray' := h

end parallel_theorem

section intersection_of_line

section construction

def intx_of_extn_line (r₁ r₂ : Ray P) (h : r₂.toProj ≠ r₁.toProj) : P := (cu r₁.toDir.toVec_nd r₂.toDir.toVec_nd (VEC r₁.source r₂.source) • r₁.toDir.toVec +ᵥ r₁.source)

theorem intx_lies_on_fst_extn_line (r₁ r₂ : Ray P) (h : r₂.toProj ≠ r₁.toProj) : ((intx_of_extn_line r₁ r₂ h) ∈ r₁.carrier ∪ r₁.reverse.carrier) := sorry

theorem intx_lies_on_snd_extn_line (r₁ r₂ : Ray P) (h : r₂.toProj ≠ r₁.toProj) : ((intx_of_extn_line r₁ r₂ h) ∈ r₂.carrier ∪ r₂.reverse.carrier) := sorry

-- `key theorem`
theorem intx_eq_of_same_extn_line {a₁ b₁ a₂ b₂ : Ray P} (g₁ : same_extn_line a₁ a₂) (g₂ : same_extn_line b₁ b₂) (h₁ : b₁.toProj ≠ a₁.toProj) (h₂ : b₂.toProj ≠ a₂.toProj) : intx_of_extn_line a₁ b₁ h₁ = intx_of_extn_line a₂ b₂ h₂ := by
  sorry

-- This theorem deals only with `HEq`
theorem heq_funext {c₁ c₂ d: Sort _} (e : c₁ = c₂) {f₁ : c₁ → d} {f₂ : c₂ → d} (h : ∀ (s : c₁) (t : c₂), f₁ s = f₂ t) : HEq f₁ f₂ := Function.hfunext e (fun _ _ _ => (heq_of_eq (h _ _)))

theorem heq_of_intx_of_extn_line (a₁ b₁ a₂ b₂ : Ray P) (h₁ : a₁ ≈ a₂) (h₂ : b₁ ≈ b₂) : HEq (fun h => intx_of_extn_line a₁ b₁ h) (fun h => intx_of_extn_line a₂ b₂ h) := by
  have e : (Ray.toProj b₁ ≠ Ray.toProj a₁) = (Ray.toProj b₂ ≠ Ray.toProj a₂) := by
    rw [h₁.1, h₂.1]
  exact @heq_funext (Ray.toProj b₁ ≠ Ray.toProj a₁) (Ray.toProj b₂ ≠ Ray.toProj a₂) P e (fun h => intx_of_extn_line a₁ b₁ h) (fun h => intx_of_extn_line a₂ b₂ h) (intx_eq_of_same_extn_line h₁ h₂)

/- the construction of the intersection point of two lines-/
def Line.intx (l₁ l₂ : Line P) (h : l₂.toProj ≠ l₁.toProj) : P := @Quotient.hrecOn₂ (Ray P) (Ray P) same_extn_line.setoid same_extn_line.setoid (fun l l' => (Line.toProj l' ≠ Line.toProj l) → P) l₁ l₂ intx_of_extn_line heq_of_intx_of_extn_line h

theorem Line.intx_is_intx (l₁ l₂ : Line P) (h : l₂.toProj ≠ l₁.toProj) : is_intx (Line.intx l₁ l₂ h) l₁ l₂ := sorry

end construction

section property

-- In this section, we discuss the property of intersection point using `is_intx` instead of `Line.intx`. As a corollory, we deduce the symmetry of Line.intx.  

theorem unique_of_intx_of_line_of_not_para {A B : P} {l₁ l₂ : Line P} (h : l₂.toProj ≠ l₁.toProj) (a : is_intx A l₁ l₂) (b : is_intx B l₁ l₂) : B = A := by
  by_contra d
  let p := (SEG_nd A B d).toProj
  sorry

-- theorem unique_of_intx_of_not_para

/-!
theorem exists_intersection_of_nonparallel_lines {l₁ l₂ : Line P} (h : ¬ (l₁ ∥ (LinearObj.line l₂))) : ∃ p : P, p LiesOn l₁ ∧ p LiesOn l₂ := by
  rcases l₁.nontriv with ⟨A, ⟨B, hab⟩⟩
  rcases l₂.nontriv with ⟨C, ⟨D, hcd⟩⟩
  have e' : Seg_nd.toProj ⟨SEG A B, hab.2.2⟩ ≠ Seg_nd.toProj ⟨SEG C D, hcd.2.2⟩ := by
    rw [line_toProj_eq_seg_nd_toProj_of_lies_on hab.1 hab.2.1 hab.2.2, line_toProj_eq_seg_nd_toProj_of_lies_on hcd.1 hcd.2.1 hcd.2.2]
    exact h
  have w : ∃ x y, VEC A C = x • VEC A B + y • VEC C D := by
    let u := VEC A B
    use ((VEC A B).1 * (VEC C D).2 - (VEC A B).2 * (VEC C D).1)⁻¹ * ((VEC A C).1 * (VEC C D).2 - (VEC C D).1 * (VEC A C).2)
    use ((VEC A B).1 * (VEC C D).2 - (VEC A B).2 * (VEC C D).1)⁻¹ * ((VEC A C).1 * (VEC A B).2 - (VEC A B).1 * (VEC A C).2)
    have cal := linear_combination_of_not_colinear (VEC A C) e'
    simp only at cal
    exact cal
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
-- `Should we define this concept? Why don't we just use Intersection of Lines and use coersion (ray : Line)`
def Intersection_of_Lines_of_Rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : P := sorry

scoped notation "RayIntx" => Intersection_of_Lines_of_Rays

theorem ray_intersection_lies_on_lines_of_rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : (RayIntx h) LiesOn ray₁.toLine ∧ (RayIntx h) LiesOn ray₂.toLine := by sorry

-- theorem ray_intersection_eq_line_intersection_of_rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : RayInt h = LineInt (Ne.trans (ray_parallel_to_line_assoc_ray ray₁) h) := sorry
-/

end property

end intersection_of_line

end EuclidGeom