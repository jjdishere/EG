import EuclideanGeometry.Foundation.Axiom.Linear.Ray

/-
This file discuss the relative positions of points and rays on a plane.
-/
noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P]

section Collinear

/-- Given three points $A$, $B$, $C$, return whether they are collinear: if at least two of them are equal, then they are considered collinear; if the three points are distinct, we use the earlier definition of colinarity for distinct points. -/
def Collinear (A B C : P) : Prop := wedge A B C = 0

theorem collinear_iff_wedge_eq_zero (A B C : P) : (Collinear A B C) ↔ (wedge A B C = 0) := .rfl

theorem not_collinear_iff_wedge_ne_zero (A B C : P) : (¬ Collinear A B C) ↔ (wedge A B C ≠ 0) := .rfl

lemma collinear_iff_collinear {A B C D : P} [PtNe B A] (h : ∃ k : ℝ, VEC C D = k • VEC A B) : Collinear A B C ↔ Collinear A B D := by
  unfold Collinear
  rw [← wedge_eq_wedge_iff] at h
  rw [h]

/-- Given three points $A$, $B$, $C$ and a real number $t$, if the vector $\overrightarrow{AC}$ is $t$ times the vector $\overrightarrow{AB}$, then $A$, $B$, and $C$ are collinear. -/
theorem collinear_of_vec_eq_smul_vec {A B C : P} {t : ℝ} (e : VEC A C = t • VEC A B) : Collinear A B C := by
  unfold Collinear wedge
  rw [e]
  simp

/-- Given three points $A$, $B$, $C$, if the vector $\overrightarrow{AC}$ is a scalar multiple of the vector $\overrightarrow{AB}$, then $A$, $B$, $C$ are collinear. -/
theorem collinear_of_vec_eq_smul_vec' {A B C : P} : (∃ t : ℝ, VEC A C = t • VEC A B) → Collinear A B C := by
  intro ⟨_, e⟩
  exact collinear_of_vec_eq_smul_vec e

/-- Given three points $A$, $B$, $C$ such that $B \neq A$, we have $A$, $B$, $C$ are collinear if and only if the vector $\overrightarrow{AC}$ is a scalar multiple of the vector $\overrightarrow{AB}$. -/
theorem collinear_iff_eq_smul_vec_of_ne {A B C : P} [g : PtNe B A] : Collinear A B C ↔ ∃ r : ℝ, VEC A C = r • VEC A B := by
  constructor
  · intro c
    unfold Collinear wedge at c
    rwa [Vec.det_eq_zero_iff_eq_smul_left, or_iff_right] at c
    rw [← Ne, ← ne_iff_vec_ne_zero]
    exact g.elim
  · exact collinear_of_vec_eq_smul_vec'

-- Please rewrite this part, use minimal theorems, but create a tactic called `collinearity`
/-- For any two points $A$ and $C$, the points $A$, $A$, $C$ are collinear. -/
@[simp]
theorem triv_collinear₁₂ (A C : P) : (Collinear A A C) := by
  unfold Collinear
  simp

/-- For any two points $A$ and $C$, the points $A$, $C$, $C$ are collinear. -/
@[simp]
theorem triv_collinear₁₂₂₃ (A C : P) : (Collinear A C C) := by
  unfold Collinear
  simp

/-- For any two points $A$ and $C$, the points $A$, $C$, $A$ are collinear. -/
@[simp]
theorem triv_collinear₁₂₃₁ (A C : P) : (Collinear A C A) := by
  unfold Collinear
  simp

theorem collinear_of_trd_eq_snd (A : P) {B C : P} (h : C = B) : Collinear A B C := by
  simp [h]

theorem collinear_of_fst_eq_snd (B : P) {A C : P} (h : A = C) : Collinear A B C := by
  simp [h]

theorem collinear_of_snd_eq_fst {A B : P} (C : P) (h : B = A)  : Collinear A B C := by
  simp [h]

/-- Given three points $A$, $B$, and $C$, if $A$, $B$, $C$ are collinear (in that order), then $A$, $C$, $B$ are collinear (in that order); in other words, swapping the last two of the three points does not change the definition of colinarity. -/
theorem collinear132 {A B C : P} : Collinear A B C ↔ Collinear A C B := by
  unfold Collinear
  rw [wedge132, neg_eq_zero]

alias ⟨Collinear.perm₁₃₂, _⟩ := collinear132

/-- Given three points $A$, $B$, and $C$, if $A$, $B$, $C$ are collinear (in that order), then $B$, $A$, $C$ are collinear (in that order); in other words, in the definition of colinarity, swapping the first two of the three points does not change property of the three points being collinear. -/
theorem collinear213 {A B C : P} : Collinear A B C ↔ Collinear B A C := by
  unfold Collinear
  rw [wedge213, neg_eq_zero]

alias ⟨Collinear.perm₂₁₃, _⟩ := collinear213

theorem collinear231 {A B C : P} : Collinear A B C ↔ Collinear B C A := by
  unfold Collinear
  rw [wedge231]

alias ⟨Collinear.perm₂₃₁, _⟩ := collinear231

theorem collinear312 {A B C : P} : Collinear A B C ↔ Collinear C A B := by
  unfold Collinear
  rw [wedge312]

alias ⟨Collinear.perm₃₁₂, _⟩ := collinear312

theorem collinear321 {A B C : P} : Collinear A B C ↔ Collinear C B A := by
  unfold Collinear
  rw [wedge321, neg_eq_zero]

alias ⟨Collinear.perm₃₂₁, _⟩ := collinear321

-- the proof of this theorem using def of line seems to be easier
/-- Given four points $A$, $B$, $C$, $D$ with $B \neq A$, if $A$, $B$, $C$ are collinear, and if $A$, $B$, $D$ are collinear, then $A$, $C$, $D$ are collinear. -/
theorem collinear_of_collinear_collinear_ne {A B C D: P} (h₁ : Collinear A B C) (h₂ : Collinear A B D) [h : PtNe B A] : (Collinear A C D) := by
  have ac : ∃ r : ℝ , VEC A C = r • VEC A B := collinear_iff_eq_smul_vec_of_ne.mp h₁
  have ad : ∃ s : ℝ , VEC A D = s • VEC A B := collinear_iff_eq_smul_vec_of_ne.mp h₂
  rcases ac with ⟨r,eq⟩
  rcases ad with ⟨s,eq'⟩
  by_cases nd : r = 0
  . simp only [nd, zero_smul] at eq
    have : C = A := eq_iff_vec_eq_zero.mpr eq
    rw [this] ; apply triv_collinear₁₂
  apply collinear_of_vec_eq_smul_vec'
  rw [eq,eq']
  use s/r
  rw [smul_smul, div_mul_cancel _ nd]

set_option push_neg.use_distrib true in
/-- Given three points $A$, $B$, $C$, if they are not collinear, then they are pairwise distinct, i.e. $C \neq B$, $A \neq C$, and $B \neq A$. -/
theorem ne_of_not_collinear {A B C : P} (h : ¬ Collinear A B C) : (C ≠ B) ∧ (A ≠ C) ∧ (B ≠ A) := by
  push_neg
  contrapose! h
  obtain (rfl | rfl | rfl) := h <;> simp

theorem collinear_iff_toProj_eq_of_ptNe {A B C : P} [hba : PtNe B A] [hca : PtNe C A] : Collinear A B C ↔ (VEC_nd A C).toProj = (VEC_nd A B).toProj := by
  rw [collinear_iff_eq_smul_vec_of_ne, VecND.toProj_eq_toProj_iff]
  rfl

end Collinear

section compatibility

/-- If $A$, $B$, $C$ are three points which lie on a ray, then they are collinear. -/
theorem Ray.collinear_of_lies_on {A B C : P} {ray : Ray P} (hA : A LiesOn ray) (hB : B LiesOn ray) (hC : C LiesOn ray) : Collinear A B C := by
  rcases hA with ⟨a,_,Ap⟩
  rcases hB with ⟨b,_,Bp⟩
  rcases hC with ⟨c,_,Cp⟩
  have ab : VEC A B = (b - a) • ray.toDir.unitVec := by
    rw [<-vec_sub_vec ray.source, Ap, Bp, sub_smul]
  have ac : VEC A C = (c - a) • ray.toDir.unitVec := by
    rw [<-vec_sub_vec ray.source, Ap, Cp, sub_smul]
  by_cases nd : b - a = 0
  . have : b = a := by
      rw [<-sub_self a] at nd
      apply add_right_cancel_iff.mp nd
    rw [this] at ab
    rw [sub_self, zero_smul] at ab
    have : B = A := by apply eq_iff_vec_eq_zero.mpr ab
    rw [this] ; apply triv_collinear₁₂
  apply collinear_of_vec_eq_smul_vec'
  use (c - a)/(b - a)
  rw [ac, ab, smul_smul, div_mul_cancel _ nd]

/-- If $A$, $B$, $C$ are three points which lie on a segment, then they are collinear. -/
theorem Seg.collinear_of_lies_on {A B C : P} {seg : Seg P} (hA : A LiesOn seg) (hB : B LiesOn seg) (hC : C LiesOn seg) : Collinear A B C := by
  by_cases nd : seg.source =seg.target
  . rcases hA with ⟨_,_,_,a⟩
    simp only [nd, vec_same_eq_zero, smul_zero] at a
    have a_d : A = seg.target := by apply eq_iff_vec_eq_zero.mpr a
    rcases hB with ⟨_,_,_,b⟩
    simp only [nd, vec_same_eq_zero, smul_zero] at b
    have b_d : B = seg.target := by apply eq_iff_vec_eq_zero.mpr b
    rw [a_d,b_d] ; apply triv_collinear₁₂
  rw [<-ne_eq] at nd
  let seg_nd := SegND.mk seg.source seg.target nd.symm
  have ha : A LiesOn seg_nd.1 := by apply hA
  have hb : B LiesOn seg_nd.1 := by apply hB
  have hc : C LiesOn seg_nd.1 := by apply hC
  exact Ray.collinear_of_lies_on (SegND.lies_on_toRay_of_lies_on ha) (SegND.lies_on_toRay_of_lies_on hb) (SegND.lies_on_toRay_of_lies_on hc)

/-
Note that we do not need all reverse, extension line,... here. instead we should show that
1. reverse, extension line coerce to same line with the original segment (in Line.lean)
2. If A B C falls on reverse then A B C falls on the coercing line. (This should be a corollory)
3. If A B C falls on the same line, then they are collinear (in Line.lean)
-/

end compatibility

/-- There exists three points $A$, $B$, $C$ on the plane such that they are not collinear. -/
theorem nontriv_of_plane {H : Type _} [h : EuclideanPlane H] : ∃ A B C : H, ¬(Collinear A B C) := by
  rcases h.nonempty with ⟨A⟩
  let B := (⟨1, 0⟩ : Vec) +ᵥ A
  let C := (⟨0, 1⟩ : Vec) +ᵥ A
  use A, B, C
  have : PtNe B A := ⟨by simp; intro h; simpa using congr_arg Vec.fst h⟩
  simp [collinear_iff_eq_smul_vec_of_ne]

end EuclidGeom
