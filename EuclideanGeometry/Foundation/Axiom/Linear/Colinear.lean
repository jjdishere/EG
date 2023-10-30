import EuclideanGeometry.Foundation.Axiom.Linear.Ray
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex
/- This file discuss the relative positions of points and rays on a plane. -/
noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P] 

section colinear

-- Define a special normalize' that maps (0 : Vec) to (1 : Proj)
def colinear_of_nd {A B C : P} (h : ¬((C = B) ∨ (A = C) ∨ (B = A))): Prop := by
  push_neg at h
  exact Vec_nd.toProj ⟨VEC A B, (ne_iff_vec_ne_zero _ _).mp h.2.2⟩ = Vec_nd.toProj ⟨VEC A C, (ne_iff_vec_ne_zero _ _).mp h.2.1.symm⟩

def colinear (A B C : P) : Prop := by
  by_cases (C = B) ∨ (A = C) ∨ (B = A)
  · exact True
  · exact colinear_of_nd h

-- The definition of colinear now includes two cases: the degenerate case and the nondegenerate case. We use normalize' to avoid problems involving using conditions of an "if" in its "then" and "else". And we only use VEC to define colinear. 

theorem colinear_of_vec_eq_smul_vec {A B C : P} {t : ℝ} (e : VEC A C = t • VEC A B) : colinear A B C := by 
  have : colinear A B C = True := by
    unfold colinear
    apply dite_eq_left_iff.mpr
    simp only [eq_iff_iff, iff_true]
    intro h'
    push_neg at h'
    unfold colinear_of_nd
    exact (eq_toProj_of_smul ⟨_, (ne_iff_vec_ne_zero A B).1 h'.2.2⟩ ⟨_, ((ne_iff_vec_ne_zero A C).1 h'.2.1.symm)⟩ e)
  tauto

theorem colinear_of_vec_eq_smul_vec' {A B C : P} : (∃ t : ℝ, VEC A C = t • VEC A B) → colinear A B C := by
  intro ⟨_, e⟩
  exact colinear_of_vec_eq_smul_vec e

theorem  eq_mul_vec_iff_colinear_of_ne {A B C : P} (g : B ≠ A) : colinear A B C ↔ ∃ r : ℝ , VEC A C = r • VEC A B := by
  constructor
  · intro c
    rw [← iff_true (colinear A B C), ← eq_iff_iff] at c
    unfold colinear at c
    rw [dite_eq_left_iff] at c
    by_cases (C = B) ∨ (A = C) ∨ (B = A)
    · by_cases C = A
      · use 0
        rw [h]
        simp only [vec_same_eq_zero, zero_smul]
      · have h : B = C := by tauto
        use 1
        rw [h]
        simp only [one_smul]
    · specialize c h
      push_neg at h
      unfold colinear_of_nd at c
      simp only [ne_eq, eq_iff_iff, iff_true] at c
      exact smul_of_eq_toProj ⟨VEC A B, (ne_iff_vec_ne_zero A B).1 g⟩ ⟨VEC A C, (ne_iff_vec_ne_zero A C).1 h.2.1.symm⟩ c
  · intro ⟨_, e⟩
    exact colinear_of_vec_eq_smul_vec e

-- Please rewrite this part, use minimal theorems, but create a tactic called `colinearity`
theorem triv_colinear (A C : P) : (colinear A A C) := by
  rw [← iff_true (colinear A A C), ← eq_iff_iff]
  unfold colinear
  rw [dite_eq_left_iff]
  intro h
  push_neg at h
  exfalso
  exact h.2.2 rfl

theorem flip_colinear_snd_trd {A B C : P} (c : colinear A B C) : (colinear A C B) := by 
  by_cases (B ≠ A) ∧ (C ≠ A)
  · rcases (eq_mul_vec_iff_colinear_of_ne h.1).1 c with ⟨t, e⟩
    have ht : t ≠ 0 := by
      by_contra ht'
      rw [ht', zero_smul] at e
      have _ : C = A := ((eq_iff_vec_eq_zero A C).2 e)
      tauto
    exact colinear_of_vec_eq_smul_vec (Eq.symm ((inv_smul_eq_iff₀ ht).2 e))
  · rw [← iff_true (colinear _ _ _), ← eq_iff_iff]
    unfold colinear
    rw [dite_eq_left_iff]
    intro g
    exfalso
    push_neg at *
    exact g.2.2 $ h g.2.1.symm

theorem flip_colinear_fst_snd {A B C : P} (c : colinear A B C) : (colinear B A C) := by
  by_cases B = A
  · rw [h]
    exact triv_colinear _ _
  · rw [eq_mul_vec_iff_colinear_of_ne h] at c
    rcases c with ⟨r, e⟩
    have e' : VEC B C = (1 - r) • VEC B A := by
      rw [← vec_sub_vec A B C, e, ← neg_vec A B, smul_neg, sub_smul, neg_sub, one_smul]
    exact colinear_of_vec_eq_smul_vec e'

-- the proof of this theorem using def of line seems to be easier
theorem colinear_of_colinear_colinear_ne {A B C D: P} (h₁ : colinear A B C) (h₂ : colinear A B D) (h : B ≠ A) : (colinear A C D) := by
  have ac : ∃ r : ℝ , VEC A C = r • VEC A B := (eq_mul_vec_iff_colinear_of_ne h).mp h₁
  have ad : ∃ s : ℝ , VEC A D = s • VEC A B := (eq_mul_vec_iff_colinear_of_ne h).mp h₂
  rcases ac with ⟨r,eq⟩
  rcases ad with ⟨s,eq'⟩
  by_cases nd : r = 0
  . simp only [nd, zero_smul] at eq
    have : C = A := (eq_iff_vec_eq_zero A C).mpr eq
    rw [this] ; apply triv_colinear
  apply colinear_of_vec_eq_smul_vec'
  rw [eq,eq'] 
  use s/r
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_sub]
  rw [<-mul_assoc]
  simp only [ne_eq, mul_eq_mul_right_iff]
  left 
  rw [mul_comm,mul_div,mul_comm,<-mul_div]
  rw [<-ne_eq] at nd
  have  : r/r = 1 := by apply div_self ; exact nd
  rw [<-Complex.ofReal_inj] at this
  simp only [ne_eq, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one] at this 
  simp only [ne_eq, this, mul_one]

theorem ne_of_not_colinear {A B C : P} (h : ¬ colinear A B C) : (C ≠ B) ∧ (A ≠ C) ∧ (B ≠ A) := by
  rw [← iff_true (colinear A B C), ← eq_iff_iff] at h
  unfold colinear at h
  rw [dite_eq_left_iff] at h
  push_neg at h
  rcases h with ⟨g, _⟩
  tauto

end colinear

section compatibility

theorem Ray.colinear_of_lies_on {A B C : P} {ray : Ray P} (hA : A LiesOn ray) (hB : B LiesOn ray) (hC : C LiesOn ray) : colinear A B C := by
  rcases hA with ⟨a,_,Ap⟩
  rcases hB with ⟨b,_,Bp⟩
  rcases hC with ⟨c,_,Cp⟩
  have ab : VEC A B = (b - a) * (ray.toDir.toVec) := by
    rw [<-vec_sub_vec ray.source, Ap ,Bp]
    simp only [Complex.real_smul]
    rw [sub_mul]
  have ac : VEC A C = (c - a) * (ray.toDir.toVec) := by
    rw [<-vec_sub_vec ray.source, Ap ,Cp]
    simp only [Complex.real_smul]
    rw [sub_mul]
  by_cases nd : b - a = 0
  . have : b = a := by 
      rw [<-sub_self a] at nd
      apply add_right_cancel_iff.mp nd
    rw [this] at ab
    simp only [sub_self, zero_mul] at ab 
    have : B = A := by apply (eq_iff_vec_eq_zero A B).mpr ab
    rw [this] ; apply triv_colinear 
  apply colinear_of_vec_eq_smul_vec'
  use (c - a)/(b - a)
  rw [ac,ab]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_sub]
  rw [<-mul_assoc]
  simp only [ne_eq, mul_eq_mul_right_iff]
  left 
  rw [mul_comm,mul_div,mul_comm,<-mul_div]
  rw [<-ne_eq] at nd
  have  : (b - a) / (b - a) = 1 := by apply div_self ; exact nd
  rw [<-Complex.ofReal_inj] at this
  simp only [ne_eq, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one] at this 
  simp only [ne_eq, this, mul_one]

theorem Seg.colinear_of_lies_on {A B C : P} {seg : Seg P} (hA : A LiesOn seg) (hB : B LiesOn seg) (hC : C LiesOn seg) : colinear A B C := by
  by_cases nd : seg.source =seg.target 
  . rcases hA with ⟨_,_,_,a⟩
    simp only [nd, vec_same_eq_zero, smul_zero] at a 
    have a_d : A = seg.target := by apply (eq_iff_vec_eq_zero seg.target A).mpr a
    rcases hB with ⟨_,_,_,b⟩
    simp only [nd, vec_same_eq_zero, smul_zero] at b 
    have b_d : B = seg.target := by apply (eq_iff_vec_eq_zero seg.target B).mpr b
    rw [a_d,b_d] ; apply triv_colinear
  rw [<-ne_eq] at nd
  let seg_nd := Seg_nd.mk seg.source seg.target nd.symm
  have ha : A LiesOn seg_nd.1 := by apply hA
  have hb : B LiesOn seg_nd.1 := by apply hB
  have hc : C LiesOn seg_nd.1 := by apply hC
  exact Ray.colinear_of_lies_on (Seg_nd.lies_on_toRay_of_lies_on ha) (Seg_nd.lies_on_toRay_of_lies_on hb) (Seg_nd.lies_on_toRay_of_lies_on hc)

theorem lies_on_ray_or_rev_from_seg_iff_colinear {A B C : P} (h: B ≠ A) :  colinear A B C ↔ C LiesOn (Seg_nd.mk A B h).toRay ∨ C LiesOn (Seg_nd.mk A B h).toRay.reverse := by sorry
-- tip : theorem pt_lies_on_line_from_ray_iff_vec_parallel in Ray.ex may help.
theorem lies_on_ray_or_rev_iff_colinear {A B C : P} (h: B ≠ A) :  colinear A B C ↔ C LiesOn (Ray.mk_pt_pt A B h) ∨ C LiesOn (Ray.mk_pt_pt A B h).reverse := by sorry
/-
Note that we do not need all reverse, extension line,... here. instead we should show that
1. reverse, extension line coerce to same line with the original segment (in Line.lean)
2. If A B C falls on reverse then A B C falls on the coercing line. (This should be a corollory)
3. If A B C falls on the same line, then they are colinear (in Line.lean)
-/

end compatibility

theorem nontriv_of_plane {H : Type _} [h : EuclideanPlane H] : ∃ A B C : H, ¬(colinear A B C) := by
  rcases h.Nonempty with ⟨A⟩
  let B := (1 : Dir).toVec +ᵥ A
  let C := Dir.I.toVec +ᵥ A
  use A , B , C
  by_contra col
  rw [eq_mul_vec_iff_colinear_of_ne] at col
  simp only [Dir.one_eq_one_toComplex, vec_of_pt_vadd_pt_eq_vec, Dir.I_toComplex_eq_I, Complex.real_smul] at col 
  rcases col with ⟨r,eq⟩
  simp only [mul_one] at eq 
  have : (↑r : ℂ).im = 0 := by simp only [Complex.ofReal_im]
  rw [<-eq, Complex.I_im] at this
  linarith
  simp only [Dir.one_eq_one_toComplex, ne_eq, vadd_eq_self_iff_vec_eq_zero, one_ne_zero, not_false_eq_true]
  
  
end EuclidGeom