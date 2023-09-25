import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex
import EuclideanGeometry.Foundation.Axiom.Linear.Line_ex

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

end LinearObj

-- Our definition of parallel for LinearObj is very general. Not only can it apply to different types of Objs, but also include degenerate cases, such as ⊆(inclusions), =(equal). 

def parallel (l₁ l₂: LinearObj P) : Prop := l₁.toProj = l₂.toProj

instance : IsEquiv (LinearObj P) parallel where
  refl _ := rfl
  symm _ _ := Eq.symm
  trans _ _ _ := Eq.trans

scoped infix : 50 "ParallelTo" => parallel

scoped infix : 50 "∥" => parallel

/- lots of trivial parallel relation of vec of 2 pt lies on Line, coersions, ... -/

section parallel_theorem
---- `eq_toProj theorems should be relocate to this file, they are in Line_ex now`.
theorem Ray.para_toLine (ray : Ray P) : (LinearObj.ray ray) ∥ ray.toLine := sorry

theorem Seg_nd.para_toRay (seg_nd : Seg_nd P) : LinearObj.seg_nd seg_nd ∥ seg_nd.toRay := sorry

theorem Seg_nd.para_toLine (seg_nd : Seg_nd P) : LinearObj.seg_nd seg_nd ∥ seg_nd.toLine := sorry

-- many more...

theorem Ray.para_toLine_of_para (ray ray' : Ray P) (h : LinearObj.ray ray ∥ ray') : (LinearObj.line ray.toLine) ∥ ray'.toLine := h

theorem Ray.not_para_of_not_para_toLine (ray ray' : Ray P) (h : ¬ (LinearObj.line ray.toLine) ∥ ray'.toLine ) : ¬ LinearObj.ray ray ∥ ray' := h

end parallel_theorem

section intersection_of_line

section construction

def inx_of_extn_line (r₁ r₂ : Ray P) (h : r₂.toProj ≠ r₁.toProj) : P := (cu r₁.toDir.toVec_nd r₂.toDir.toVec_nd (VEC r₁.source r₂.source) • r₁.toDir.toVec +ᵥ r₁.source)

theorem inx_of_extn_line_symm (r₁ r₂ : Ray P) (h : r₂.toProj ≠ r₁.toProj) :
    inx_of_extn_line r₁ r₂ h = inx_of_extn_line r₂ r₁ h.symm := by
  have hsymm : cu r₁.toDir.toVec_nd r₂.toDir.toVec_nd (VEC r₁.source r₂.source) • r₁.toDir.toVec =
      cu r₂.toDir.toVec_nd r₁.toDir.toVec_nd (VEC r₂.source r₁.source) • r₂.toDir.toVec + 
      (r₂.source -ᵥ r₁.source) := by
    have h := linear_combination_of_not_colinear_dir (VEC r₁.source r₂.source) h
    nth_rw 1 [← cu_cv, Vec.mk_pt_pt] at h
    rw [h, ← neg_vec r₁.source r₂.source, cu_neg, Complex.real_smul, neg_smul]
    exact eq_neg_add_of_add_eq rfl
  rw [inx_of_extn_line, inx_of_extn_line, hsymm, add_vadd, Complex.real_smul, vsub_vadd]

theorem inx_lies_on_fst_extn_line (r₁ r₂ : Ray P) (h : r₂.toProj ≠ r₁.toProj) : ((inx_of_extn_line r₁ r₂ h) ∈ r₁.carrier ∪ r₁.reverse.carrier) := by
  rw [inx_of_extn_line]
  by_cases hn : cu r₁.toDir.toVec_nd r₂.toDir.toVec_nd (VEC r₁.source r₂.source) ≥ 0
  · left
    use cu r₁.toDir.toVec_nd r₂.toDir.toVec_nd (VEC r₁.source r₂.source)
    exact ⟨hn, vec_of_pt_vadd_pt_eq_vec _ _⟩
  · right
    use - cu r₁.toDir.toVec_nd r₂.toDir.toVec_nd (VEC r₁.source r₂.source)
    constructor
    linarith
    dsimp [Ray.reverse]
    rw [vec_of_pt_vadd_pt_eq_vec, Complex.ofReal_neg, mul_neg, neg_mul, neg_neg]

theorem inx_lies_on_snd_extn_line (r₁ r₂ : Ray P) (h : r₂.toProj ≠ r₁.toProj) : ((inx_of_extn_line r₁ r₂ h) ∈ r₂.carrier ∪ r₂.reverse.carrier) := by
  rw [inx_of_extn_line_symm]
  exact inx_lies_on_fst_extn_line r₂ r₁ h.symm

-- `key theorem`
theorem inx_eq_of_same_extn_line {a₁ b₁ a₂ b₂ : Ray P} (g₁ : same_extn_line a₁ a₂) (g₂ : same_extn_line b₁ b₂) (h₁ : b₁.toProj ≠ a₁.toProj) (h₂ : b₂.toProj ≠ a₂.toProj) : inx_of_extn_line a₁ b₁ h₁ = inx_of_extn_line a₂ b₂ h₂ := by
  have ha1 : inx_of_extn_line a₁ b₁ h₁ LiesOn a₁.toLine := inx_lies_on_fst_extn_line a₁ b₁ h₁
  have hb1 : inx_of_extn_line a₁ b₁ h₁ LiesOn b₁.toLine := inx_lies_on_snd_extn_line a₁ b₁ h₁
  rw [ray_toLine_eq_of_same_extn_line g₁] at ha1
  rw [ray_toLine_eq_of_same_extn_line g₂] at hb1
  by_contra hn
  have heq : a₂.toLine = b₂.toLine := eq_of_pt_pt_lies_on_of_ne hn 
    (inx_lies_on_fst_extn_line a₂ b₂ h₂) ha1 (inx_lies_on_snd_extn_line a₂ b₂ h₂) hb1
  exact h₂.symm (congrArg Line.toProj heq)
  
-- This theorem deals only with `HEq`
theorem heq_funext {c₁ c₂ d: Sort _} (e : c₁ = c₂) {f₁ : c₁ → d} {f₂ : c₂ → d} (h : ∀ (s : c₁) (t : c₂), f₁ s = f₂ t) : HEq f₁ f₂ := Function.hfunext e (fun _ _ _ => (heq_of_eq (h _ _)))

theorem heq_of_inx_of_extn_line (a₁ b₁ a₂ b₂ : Ray P) (h₁ : a₁ ≈ a₂) (h₂ : b₁ ≈ b₂) : HEq (fun h => inx_of_extn_line a₁ b₁ h) (fun h => inx_of_extn_line a₂ b₂ h) := by
  have e : (Ray.toProj b₁ ≠ Ray.toProj a₁) = (Ray.toProj b₂ ≠ Ray.toProj a₂) := by
    rw [h₁.1, h₂.1]
  exact @heq_funext (Ray.toProj b₁ ≠ Ray.toProj a₁) (Ray.toProj b₂ ≠ Ray.toProj a₂) P e (fun h => inx_of_extn_line a₁ b₁ h) (fun h => inx_of_extn_line a₂ b₂ h) (inx_eq_of_same_extn_line h₁ h₂)

/- the construction of the intersection point of two lines-/
def Line.inx (l₁ l₂ : Line P) (h : l₂.toProj ≠ l₁.toProj) : P := @Quotient.hrecOn₂ (Ray P) (Ray P) same_extn_line.setoid same_extn_line.setoid (fun l l' => (Line.toProj l' ≠ Line.toProj l) → P) l₁ l₂ inx_of_extn_line heq_of_inx_of_extn_line h

theorem Line.inx_is_inx {l₁ l₂ : Line P} (h : l₂.toProj ≠ l₁.toProj) : is_inx (Line.inx l₁ l₂ h) l₁ l₂ := sorry

end construction

section property

-- In this section, we discuss the property of intersection point using `is_inx` instead of `Line.inx`. As a corollory, we deduce the symmetry of Line.inx.  

theorem unique_of_inx_of_line_of_not_para {A B : P} {l₁ l₂ : Line P} (h : l₂.toProj ≠ l₁.toProj) (a : is_inx A l₁ l₂) (b : is_inx B l₁ l₂) : B = A := by
  by_contra d
  exact h (congrArg Line.toProj (eq_of_pt_pt_lies_on_of_ne d a.1 b.1 a.2 b.2).symm)

theorem Line.inx.symm {l₁ l₂ : Line P} (h : l₂.toProj ≠ l₁.toProj) : Line.inx l₂ l₁ h.symm = Line.inx l₁ l₂ h := unique_of_inx_of_line_of_not_para h (Line.inx_is_inx h) <| is_inx.symm (Line.inx_is_inx h.symm)

theorem eq_of_parallel_and_pt_lies_on {A : P} {l₁ l₂ : Line P} (h₁ : A LiesOn l₁) (h₂ : A LiesOn l₂) (h : LinearObj.line l₁ ∥ l₂) : l₁ = l₂ := sorry

theorem exists_intersection_of_nonparallel_lines {l₁ l₂ : Line P} (h : ¬ (l₁ ∥ (LinearObj.line l₂))) : ∃ p : P, p LiesOn l₁ ∧ p LiesOn l₂ := by
  rcases l₁.nontriv with ⟨A, ⟨B, hab⟩⟩
  rcases l₂.nontriv with ⟨C, ⟨D, hcd⟩⟩
  have e' : Seg_nd.toProj ⟨SEG A B, hab.2.2⟩ ≠ Seg_nd.toProj ⟨SEG C D, hcd.2.2⟩ := by
    rw [line_toProj_eq_seg_nd_toProj_of_lies_on hab.1 hab.2.1 hab.2.2, line_toProj_eq_seg_nd_toProj_of_lies_on hcd.1 hcd.2.1 hcd.2.2]
    exact h
  let x := ((VEC A B).1 * (VEC C D).2 - (VEC A B).2 * (VEC C D).1)⁻¹ * ((VEC A C).1 * (VEC C D).2 - (VEC C D).1 * (VEC A C).2)
  let y := ((VEC A B).1 * (VEC C D).2 - (VEC A B).2 * (VEC C D).1)⁻¹ * ((VEC A B).1 * (VEC A C).2 - (VEC A C).1 * (VEC A B).2)
  have e : VEC A C = x • VEC A B + y • VEC C D := by 
    apply linear_combination_of_not_colinear_vec_nd (VEC A C) e'
  let X := x • VEC A B +ᵥ A
  use X
  constructor
  exact (lies_on_iff_colinear_of_ne_lies_on_lies_on hab.2.2 hab.1 hab.2.1 _).2 (colinear_of_vec_eq_smul_vec (vec_of_pt_vadd_pt_eq_vec _ _))
  apply (lies_on_iff_colinear_of_ne_lies_on_lies_on hcd.2.2 hcd.1 hcd.2.1 _).2
  have e'' : VEC C X = (-y) • VEC C D := by
    rw [← vec_sub_vec A _ _, vec_of_pt_vadd_pt_eq_vec _ _, e]
    simp only [Complex.real_smul, sub_add_cancel', neg_smul]
  exact colinear_of_vec_eq_smul_vec e''

theorem exists_unique_intersection_of_nonparallel_lines {l₁ l₂ : Line P} (h : ¬ (l₁ ∥ (LinearObj.line l₂))) : ∃! p : P, p LiesOn l₁ ∧ p LiesOn l₂ := by
  rcases (exists_intersection_of_nonparallel_lines h) with ⟨X, ⟨h₁, h₂⟩⟩
  use X
  simp only [h₁, h₂, and_self, and_imp, true_and]
  intro _ h₁' h₂'
  by_contra n
  exact h (congrArg LinearObj.toProj (congrArg LinearObj.line (eq_of_pt_pt_lies_on_of_ne n h₁ h₁' h₂ h₂')))

def intersection_of_nonparallel_line (l₁ l₂ : Line P) (h : ¬ (l₁ ∥ (LinearObj.line l₂))) : P := 
  Classical.choose (exists_unique_intersection_of_nonparallel_lines h)
  -- by choose X _ using (exists_unique_intersection_of_nonparallel_lines h)
  -- use X

scoped notation "LineInt" => intersection_of_nonparallel_line

theorem intersection_of_nonparallel_line_lies_on_fst_line {l₁ l₂ : Line P} (h : ¬ (l₁ ∥ (LinearObj.line l₂))) : (LineInt l₁ l₂ h) LiesOn l₁ :=
  (Classical.choose_spec (exists_unique_intersection_of_nonparallel_lines h)).1.1

theorem intersection_of_nonparallel_line_lies_on_snd_line {l₁ l₂ : Line P} (h : ¬ (l₁ ∥ (LinearObj.line l₂))) : (LineInt l₁ l₂ h) LiesOn l₂ :=
  (Classical.choose_spec (exists_unique_intersection_of_nonparallel_lines h)).1.2

/-!
-- Now let's come to rays. 
-- If ray₁ and ray₂ are two rays that are not parallel, then the following function returns the unique point of the intersection of the associated two lines. This function is a bit tricky, will come back to this.
-- `Should we define this concept? Why don't we just use Intersection of Lines and use coersion (ray : Line)`
def Intersection_of_Lines_of_Rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : P := sorry

scoped notation "RayInx" => Intersection_of_Lines_of_Rays

theorem ray_intersection_lies_on_lines_of_rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : (RayInx h) LiesOn ray₁.toLine ∧ (RayInx h) LiesOn ray₂.toLine := by sorry

-- theorem ray_intersection_eq_line_intersection_of_rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : RayInt h = LineInt (Ne.trans (ray_parallel_to_line_assoc_ray ray₁) h) := sorry
-/

end property

end intersection_of_line

end EuclidGeom