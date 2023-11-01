import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex

noncomputable section
namespace EuclidGeom

open Line

variable {P : Type _} [EuclideanPlane P]

instance : LinearObj Vec_nd where
  toProj := fun l ↦ l.toProj

instance : LinearObj Dir where
  toProj := fun l ↦ l.toProj

instance : LinearObj (Ray P) where
  toProj := fun l ↦ l.toProj

instance : LinearObj (Seg_nd P) where
  toProj := fun l ↦ l.toProj

instance : LinearObj (Line P) where
  toProj := fun l ↦ l.toProj

-- Our definition of parallel for LinearObj is very general. Not only can it apply to different types of Objs, but also include degenerate cases, such as ⊆(inclusions), =(equal).

def parallel {α β : Type*} [LinearObj α] [LinearObj β] (l₁ : α) (l₂ : β) : Prop :=
  LinearObj.toProj l₁ = LinearObj.toProj l₂

instance (α : Type*) [LinearObj α] : IsEquiv α parallel where
  refl _ := rfl
  symm _ _ := Eq.symm
  trans _ _ _ := Eq.trans

scoped infix : 50 "ParallelTo" => parallel

scoped infix : 50 "∥" => parallel

/- lots of trivial parallel relation of vec of 2 pt lies on Line, coersions, ... -/

section parallel_theorem
---- `eq_toProj theorems should be relocate to this file, they are in Line_ex now`.
theorem Ray.toProj_eq_toLine_toProj (ray : Ray P): ray.toProj = ray.toLine.toProj := rfl

theorem Seg_nd.toProj_eq_toLine_toProj (seg_nd : Seg_nd P) : seg_nd.toProj = seg_nd.toLine.toProj := rfl

theorem Ray.para_toLine (ray : Ray P) : ray ∥ ray.toLine := rfl

theorem Seg_nd.para_toRay (seg_nd : Seg_nd P) : seg_nd ∥ seg_nd.toRay := rfl

theorem Seg_nd.para_toLine (seg_nd : Seg_nd P) : seg_nd ∥ seg_nd.toLine := rfl

-- many more...

theorem Ray.para_toLine_of_para (ray ray' : Ray P) (h : ray ∥ ray') : ray.toLine ∥ ray'.toLine := h

theorem Ray.not_para_of_not_para_toLine (ray ray' : Ray P) (h : ¬ ray.toLine ∥ ray'.toLine) : ¬ ray ∥ ray' := h

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

theorem ray_toLine_eq_of_same_extn_line {r₁ r₂ : Ray P} (h : same_extn_line r₁ r₂) : r₁.toLine = r₂.toLine := (Quotient.eq (r := same_extn_line.setoid)).mpr h

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

theorem heq_of_inx_of_extn_line (a₁ b₁ a₂ b₂ : Ray P) (h₁ : same_extn_line a₁ a₂) (h₂ : same_extn_line b₁ b₂) : HEq (fun h => inx_of_extn_line a₁ b₁ h) (fun h => inx_of_extn_line a₂ b₂ h) := by
  have e : (Ray.toProj b₁ ≠ Ray.toProj a₁) = (Ray.toProj b₂ ≠ Ray.toProj a₂) := by
    rw [h₁.1, h₂.1]
  exact @heq_funext (Ray.toProj b₁ ≠ Ray.toProj a₁) (Ray.toProj b₂ ≠ Ray.toProj a₂) P e (fun h => inx_of_extn_line a₁ b₁ h) (fun h => inx_of_extn_line a₂ b₂ h) (inx_eq_of_same_extn_line h₁ h₂)

/-- The construction of the intersection point of two lines. -/
def Line.inx (l₁ l₂ : Line P) (h : l₂.toProj ≠ l₁.toProj) : P := @Quotient.hrecOn₂ (Ray P) (Ray P) same_extn_line.setoid same_extn_line.setoid (fun l l' => (Line.toProj l' ≠ Line.toProj l) → P) l₁ l₂ inx_of_extn_line heq_of_inx_of_extn_line h

theorem Line.inx_lies_on_fst {l₁ l₂ : Line P} (h : l₂.toProj ≠ l₁.toProj) :
    Line.inx l₁ l₂ h ∈ l₁.carrier := by
  rcases Quotient.exists_rep l₁ with ⟨r1, hr1⟩
  rcases Quotient.exists_rep l₂ with ⟨r2, hr2⟩
  simp only [← hr1, ← hr2]
  exact inx_lies_on_fst_extn_line r1 r2 (by rw [← hr1, ← hr2] at h; exact h)

theorem Line.inx_lies_on_snd {l₁ l₂ : Line P} (h : l₂.toProj ≠ l₁.toProj) :
    Line.inx l₁ l₂ h ∈ l₂.carrier := by
  rcases Quotient.exists_rep l₁ with ⟨r1, hr1⟩
  rcases Quotient.exists_rep l₂ with ⟨r2, hr2⟩
  simp only [← hr1, ← hr2]
  exact inx_lies_on_snd_extn_line r1 r2 (by rw [← hr1, ← hr2] at h; exact h)

theorem Line.inx_is_inx {l₁ l₂ : Line P} (h : l₂.toProj ≠ l₁.toProj) : is_inx (Line.inx l₁ l₂ h) l₁ l₂ :=
  ⟨inx_lies_on_fst h, inx_lies_on_snd h⟩

end construction

section property

-- In this section, we discuss the property of intersection point using `is_inx` instead of `Line.inx`. As a corollory, we deduce the symmetry of Line.inx.

theorem unique_of_inx_of_line_of_not_para {A B : P} {l₁ l₂ : Line P} (h : l₂.toProj ≠ l₁.toProj) (a : is_inx A l₁ l₂) (b : is_inx B l₁ l₂) : B = A :=
  Classical.byContradiction fun d ↦ h (congrArg Line.toProj (eq_of_pt_pt_lies_on_of_ne d a.1 b.1 a.2 b.2).symm)

theorem inx_of_line_eq_inx {A : P} {l₁ l₂ : Line P} (h : l₂.toProj ≠ l₁.toProj) (ha : is_inx A l₁ l₂) :
  A = l₁.inx l₂ h := unique_of_inx_of_line_of_not_para h (Line.inx_is_inx h) ha

theorem Line.inx.symm {l₁ l₂ : Line P} (h : l₂.toProj ≠ l₁.toProj) : Line.inx l₂ l₁ h.symm = Line.inx l₁ l₂ h :=
  unique_of_inx_of_line_of_not_para h (Line.inx_is_inx h) (is_inx.symm (Line.inx_is_inx h.symm))

theorem eq_of_parallel_and_pt_lies_on {A : P} {l₁ l₂ : Line P} (h₁ : A LiesOn l₁) (h₂ : A LiesOn l₂)
  (h : l₁ ∥ l₂) : l₁ = l₂ := eq_of_same_toProj_and_pt_lies_on h₁ h₂ h

theorem exists_intersection_of_nonparallel_lines {l₁ l₂ : Line P} (h : ¬ l₁ ∥ l₂) : ∃ p : P, p LiesOn l₁ ∧ p LiesOn l₂ := by
  rcases l₁.nontriv with ⟨A, ⟨B, hab⟩⟩
  rcases l₂.nontriv with ⟨C, ⟨D, hcd⟩⟩
  have e' : Seg_nd.toProj ⟨SEG A B, hab.2.2⟩ ≠ Seg_nd.toProj ⟨SEG C D, hcd.2.2⟩ := by
    rw [toProj_eq_seg_nd_toProj_of_lies_on hab.1 hab.2.1 hab.2.2, toProj_eq_seg_nd_toProj_of_lies_on hcd.1 hcd.2.1 hcd.2.2]
    exact h
  let x := ((VEC A B).1 * (VEC C D).2 - (VEC A B).2 * (VEC C D).1)⁻¹ * ((VEC A C).1 * (VEC C D).2 - (VEC C D).1 * (VEC A C).2)
  let y := ((VEC A B).1 * (VEC C D).2 - (VEC A B).2 * (VEC C D).1)⁻¹ * ((VEC A B).1 * (VEC A C).2 - (VEC A C).1 * (VEC A B).2)
  have e : VEC A C = x • VEC A B + y • VEC C D := by
    apply linear_combination_of_not_colinear_vec_nd (VEC A C) e'
  have h : VEC C (x • VEC A B +ᵥ A) = - y • VEC C D := by
    rw [← vec_sub_vec A _ _, vec_of_pt_vadd_pt_eq_vec _ _, e]
    simp only [Complex.real_smul, sub_add_cancel', neg_smul]
  exact ⟨x • VEC A B +ᵥ A, (lies_on_iff_colinear_of_ne_lies_on_lies_on hab.2.2 hab.1 hab.2.1 _).2
    (colinear_of_vec_eq_smul_vec (vec_of_pt_vadd_pt_eq_vec A _)),
    (lies_on_iff_colinear_of_ne_lies_on_lies_on hcd.2.2 hcd.1 hcd.2.1 _).2 (colinear_of_vec_eq_smul_vec h)⟩

theorem exists_unique_intersection_of_nonparallel_lines {l₁ l₂ : Line P} (h : ¬ l₁ ∥ l₂) : ∃! p : P, p LiesOn l₁ ∧ p LiesOn l₂ := by
  rcases exists_intersection_of_nonparallel_lines h with ⟨X, ⟨h₁, h₂⟩⟩
  use X
  simp only [h₁, h₂, and_self, and_imp, true_and]
  exact fun _ h₁' h₂' ↦ Classical.byContradiction fun n ↦
    h (congrArg LinearObj.toProj (eq_of_pt_pt_lies_on_of_ne n h₁ h₁' h₂ h₂'))

def intersection_of_nonparallel_line (l₁ l₂ : Line P) (h : ¬ l₁ ∥ l₂) : P :=
  Classical.choose (exists_unique_intersection_of_nonparallel_lines h)
  -- by choose X _ using (exists_unique_intersection_of_nonparallel_lines h)
  -- use X

scoped notation "LineInt" => intersection_of_nonparallel_line

theorem intersection_of_nonparallel_line_lies_on_fst_line {l₁ l₂ : Line P} (h : ¬ l₁ ∥ l₂) : LineInt l₁ l₂ h LiesOn l₁ :=
  (Classical.choose_spec (exists_unique_intersection_of_nonparallel_lines h)).1.1

theorem intersection_of_nonparallel_line_lies_on_snd_line {l₁ l₂ : Line P} (h : ¬ l₁ ∥ l₂) : LineInt l₁ l₂ h LiesOn l₂ :=
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
