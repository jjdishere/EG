import EuclideanGeometry.Foundation.Axiom.Linear.Ray

/-
This file discuss the relative positions of points and rays on a plane.
-/
noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P]

section colinear

/-- Given three distinct (ordered) points $A$, $B$, $C$, this function returns whether they are colinear, i.e. whether the projective direction of the vector $\overrightarrow{AB}$ is the same as the projective direction of the vector $\overrightarrow{AC}$. -/
def colinear_of_nd {A B C : P} (hac : A ≠ C) (hba : B ≠ A) : Prop :=
  VecND.toProj (VEC_nd A B hba) = VecND.toProj (VEC_nd A C hac.symm)

/-- Given three points $A$, $B$, $C$, return whether they are colinear: if at least two of them are equal, then they are considered colinear; if the three points are distinct, we use the earlier definition of colinarity for distinct points. -/
def colinear (A B C : P) : Prop :=
  if h : (C = B) ∨ (A = C) ∨ (B = A) then True
  else by
    push_neg at h
    exact colinear_of_nd h.2.1 h.2.2

-- The definition of colinear now includes two cases: the degenerate case and the nondegenerate case. We use to_dir' to avoid problems involving using conditions of an "if" in its "then" and "else". And we only use VEC to define colinear.

theorem toProj_eq_of_colinear {A B C : P} (hba : B ≠ A) (hca : C ≠ A) (h : colinear A B C) : (SEG_nd A B hba).toProj = (SEG_nd A C hca).toProj :=
  if hbc : B = C then by congr
  else ((dite_prop_iff_and _).mp h).2 <| by
    push_neg
    exact ⟨Ne.symm hbc, hca.symm, hba⟩

/-- Given three points $A$, $B$, $C$ and a real number $t$, if the vector $\overrightarrow{AC}$ is $t$ times the vector $\overrightarrow{AB}$, then $A$, $B$, and $C$ are colinear. -/
theorem colinear_of_vec_eq_smul_vec {A B C : P} {t : ℝ} (e : VEC A C = t • VEC A B) : colinear A B C := by
  have : colinear A B C = True := by
    unfold colinear
    apply dite_eq_left_iff.mpr
    simp only [eq_iff_iff, iff_true]
    intro h'
    push_neg at h'
    unfold colinear_of_nd
    rw [eq_comm, VecND.toProj_eq_toProj_iff]
    exact ⟨t, e⟩
  tauto

/-- Given three points $A$, $B$, $C$, if the vector $\overrightarrow{AC}$ is a scalar multiple of the vector $\overrightarrow{AB}$, then $A$, $B$, $C$ are colinear. -/
theorem colinear_of_vec_eq_smul_vec' {A B C : P} : (∃ t : ℝ, VEC A C = t • VEC A B) → colinear A B C := by
  intro ⟨_, e⟩
  exact colinear_of_vec_eq_smul_vec e

/-- Given three points $A$, $B$, $C$ such that $B \neq A$, we have $A$, $B$, $C$ are colinear if and only if the vector $\overrightarrow{AC}$ is a scalar multiple of the vector $\overrightarrow{AB}$. -/
theorem colinear_iff_eq_smul_vec_of_ne {A B C : P} (g : B ≠ A) : colinear A B C ↔ ∃ r : ℝ , VEC A C = r • VEC A B := by
  constructor
  · intro c
    rw [← iff_true (colinear A B C), ← eq_iff_iff] at c
    unfold colinear at c
    rw [dite_eq_left_iff] at c
    by_cases h : (C = B) ∨ (A = C) ∨ (B = A)
    · by_cases h : C = A
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
      rwa [eq_comm, VecND.toProj_eq_toProj_iff] at c
  · intro ⟨_, e⟩
    exact colinear_of_vec_eq_smul_vec e


-- Please rewrite this part, use minimal theorems, but create a tactic called `colinearity`
/-- For any two points $A$ and $C$, the points $A$, $A$, $C$ are colinear. -/
theorem triv_colinear (A C : P) : (colinear A A C) := by
  rw [← iff_true (colinear A A C), ← eq_iff_iff]
  unfold colinear
  rw [dite_eq_left_iff]
  intro h
  push_neg at h
  exfalso
  exact h.2.2 rfl

theorem colinear_of_trd_eq_snd (A : P) {B C : P} (h : C = B) : colinear A B C :=
  (dite_prop_iff_or (C = B ∨ A = C ∨ B = A)).mpr (.inl ⟨.inl h, trivial⟩)

theorem colinear_of_fst_eq_snd (B : P) {A C : P} (h : A = C) : colinear A B C :=
  (dite_prop_iff_or (C = B ∨ A = C ∨ B = A)).mpr (.inl ⟨.inr (.inl h), trivial⟩)

theorem colinear_of_snd_eq_fst {A B : P} (C : P) (h : B = A)  : colinear A B C :=
  (dite_prop_iff_or (C = B ∨ A = C ∨ B = A)).mpr (.inl ⟨.inr (.inr h), trivial⟩)

/-- Given three points $A$, $B$, and $C$, if $A$, $B$, $C$ are colinear (in that order), then $A$, $C$, $B$ are colinear (in that order); in other words, swapping the last two of the three points does not change the definition of colinarity. -/
theorem flip_colinear_snd_trd {A B C : P} (c : colinear A B C) : colinear A C B := by
  by_cases h : (B ≠ A) ∧ (C ≠ A)
  · rcases (colinear_iff_eq_smul_vec_of_ne h.1).1 c with ⟨t, e⟩
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

/-- Given three points $A$, $B$, and $C$, if $A$, $B$, $C$ are colinear (in that order), then $B$, $A$, $C$ are colinear (in that order); in other words, in the definition of colinarity, swapping the first two of the three points does not change property of the three points being colinear. -/
theorem flip_colinear_fst_snd {A B C : P} (c : colinear A B C) : colinear B A C := by
  by_cases h : B = A
  · rw [h]
    exact triv_colinear _ _
  · rw [colinear_iff_eq_smul_vec_of_ne h] at c
    rcases c with ⟨r, e⟩
    have e' : VEC B C = (1 - r) • VEC B A := by
      rw [← vec_sub_vec A B C, e, ← neg_vec A B, smul_neg, sub_smul, neg_sub, one_smul]
    exact colinear_of_vec_eq_smul_vec e'

theorem perm_colinear_snd_trd_fst {A B C : P} (h : colinear A B C) : colinear B C A :=
  flip_colinear_snd_trd (flip_colinear_fst_snd h)

theorem perm_colinear_trd_fst_snd {A B C : P} (h : colinear A B C) : colinear C A B :=
  perm_colinear_snd_trd_fst (perm_colinear_snd_trd_fst h)

theorem flip_colinear_fst_trd {A B C : P} (h : colinear A B C) : colinear C B A :=
  perm_colinear_snd_trd_fst (flip_colinear_snd_trd h)

-- the proof of this theorem using def of line seems to be easier
/-- Given four points $A$, $B$, $C$, $D$ with $B \neq A$, if $A$, $B$, $C$ are colinear, and if $A$, $B$, $D$ are colinear, then $A$, $C$, $D$ are colinear. -/
theorem colinear_of_colinear_colinear_ne {A B C D: P} (h₁ : colinear A B C) (h₂ : colinear A B D) (h : B ≠ A) : (colinear A C D) := by
  have ac : ∃ r : ℝ , VEC A C = r • VEC A B := (colinear_iff_eq_smul_vec_of_ne h).mp h₁
  have ad : ∃ s : ℝ , VEC A D = s • VEC A B := (colinear_iff_eq_smul_vec_of_ne h).mp h₂
  rcases ac with ⟨r,eq⟩
  rcases ad with ⟨s,eq'⟩
  by_cases nd : r = 0
  . simp only [nd, zero_smul] at eq
    have : C = A := (eq_iff_vec_eq_zero A C).mpr eq
    rw [this] ; apply triv_colinear
  apply colinear_of_vec_eq_smul_vec'
  rw [eq,eq']
  use s/r
  rw [smul_smul, div_mul_cancel _ nd]

/-- Given three points $A$, $B$, $C$, if they are not colinear, then they are pairwise distinct, i.e. $C \neq B$, $A \neq C$, and $B \neq A$. -/
theorem ne_of_not_colinear {A B C : P} (h : ¬ colinear A B C) : (C ≠ B) ∧ (A ≠ C) ∧ (B ≠ A) := by
  rw [← iff_true (colinear A B C), ← eq_iff_iff] at h
  unfold colinear at h
  rw [dite_eq_left_iff] at h
  push_neg at h
  rcases h with ⟨g, _⟩
  tauto

end colinear

section compatibility

/-- If $A$, $B$, $C$ are three points which lie on a ray, then they are colinear. -/
theorem Ray.colinear_of_lies_on {A B C : P} {ray : Ray P} (hA : A LiesOn ray) (hB : B LiesOn ray) (hC : C LiesOn ray) : colinear A B C := by
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
    have : B = A := by apply (eq_iff_vec_eq_zero A B).mpr ab
    rw [this] ; apply triv_colinear
  apply colinear_of_vec_eq_smul_vec'
  use (c - a)/(b - a)
  rw [ac, ab, smul_smul, div_mul_cancel _ nd]

/-- If $A$, $B$, $C$ are three points which lie on a segment, then they are colinear. -/
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
  let seg_nd := SegND.mk seg.source seg.target nd.symm
  have ha : A LiesOn seg_nd.1 := by apply hA
  have hb : B LiesOn seg_nd.1 := by apply hB
  have hc : C LiesOn seg_nd.1 := by apply hC
  exact Ray.colinear_of_lies_on (SegND.lies_on_toRay_of_lies_on ha) (SegND.lies_on_toRay_of_lies_on hb) (SegND.lies_on_toRay_of_lies_on hc)

/-
Note that we do not need all reverse, extension line,... here. instead we should show that
1. reverse, extension line coerce to same line with the original segment (in Line.lean)
2. If A B C falls on reverse then A B C falls on the coercing line. (This should be a corollory)
3. If A B C falls on the same line, then they are colinear (in Line.lean)
-/

end compatibility

/-- There exists three points $A$, $B$, $C$ on the plane such that they are not colinear. -/
theorem nontriv_of_plane {H : Type _} [h : EuclideanPlane H] : ∃ A B C : H, ¬(colinear A B C) := by
  rcases h.nonempty with ⟨A⟩
  let B := (⟨1, 0⟩ : Vec) +ᵥ A
  let C := (⟨0, 1⟩ : Vec) +ᵥ A
  use A, B, C
  rw [colinear_iff_eq_smul_vec_of_ne]
  · simp
  · simp
    intro h
    simpa using congr_arg Vec.fst h

end EuclidGeom
