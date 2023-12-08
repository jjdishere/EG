import EuclideanGeometry.Foundation.Axiom.Linear.Colinear

noncomputable section
namespace EuclidGeom

@[ext]
class Line (P : Type _) [EuclideanPlane P] where 
  carrier : Set P
  linear : ∀ (A B C : P), (A ∈ carrier) → (B ∈ carrier) → (C ∈ carrier) → colinear A B C
  maximal : ∀ (A B : P), (A ∈ carrier) → (B ∈ carrier) → (B ≠ A) → (∀ (C : P), colinear A B C → (C ∈ carrier))
  nontriv : ∃ (A B : P), (A ∈ carrier) ∧ (B ∈ carrier) ∧ (B ≠ A)

namespace Line

variable  {P : Type _} [EuclideanPlane P] 

-- define a line from two points 

def mk_pt_pt (A B : P) (h : B ≠ A) : Line P where
  carrier := {C : P | ∃ t : ℝ, VEC A C = t • VEC A B}
  linear x y z:= by
    unfold Membership.mem Set.instMembershipSet Set.Mem setOf
    simp only [forall_exists_index]
    intro tx hx ty hy tz hz
    by_cases ty ≠ tx ∧ tz ≠ tx ∧ ty ≠ tz
    · rcases h with ⟨h₁, _, _⟩
      have w₂ : ∃ t : ℝ, VEC x z = t • VEC x y := by
        use (ty - tx)⁻¹ * (tz - tx)
        rw [mul_smul]
        symm
        apply ((inv_smul_eq_iff₀ (Iff.mpr sub_ne_zero h₁)).2)
        rw [← vec_sub_vec A x y, ← vec_sub_vec A x z, hx, hy, hz]
        rw [← sub_smul, ← sub_smul, ← mul_smul, ← mul_smul, mul_comm]
      apply colinear_of_vec_eq_smul_vec'
      exact w₂
    · have h' : (ty = tx) ∨ (tz = tx) ∨ (ty = tz) := by tauto
      by_cases ty = tx
      · rw [pt_eq_pt_of_eq_smul_smul h hy hx]
        exact triv_colinear _ _
      · by_cases tz = tx
        · rw [pt_eq_pt_of_eq_smul_smul h hz hx]
          exact flip_colinear_snd_trd $ triv_colinear _ _
        · have h : ty = tz := by tauto
          rw [pt_eq_pt_of_eq_smul_smul h hy hz]
          exact flip_colinear_fst_snd $ flip_colinear_snd_trd $ triv_colinear _ _
  maximal x y := by
    unfold Membership.mem Set.instMembershipSet Set.Mem setOf
    simp only [forall_exists_index]
    intro tx hx ty hy hne z c
    have e : VEC x y = (ty - tx) • VEC A B := by
      rw [← vec_sub_vec A x y, hx, hy, sub_smul]
    rcases (eq_mul_vec_iff_colinear_of_ne hne).1 c with ⟨t, ht⟩
    use tx + t * (ty - tx)
    rw [← vec_add_vec A x z, ht, e, hx, ← mul_smul, ← add_smul]
  nontriv := by
    use A
    use B
    unfold Membership.mem Set.instMembershipSet Set.Mem setOf
    simp only [forall_exists_index]
    constructor
    use 0
    simp only [vec_same_eq_zero, zero_smul]
    constructor
    use 1
    simp only [one_smul]
    exact h

end Line

scoped notation "LIN" => Line.mk_pt_pt 

namespace Line

variable {P : Type _} [EuclideanPlane P]

/- Def of point lies on a line, LiesInt is not defined -/
protected def IsOn (a : P) (l : Line P) : Prop :=
  a ∈ l.carrier

instance : Carrier P (Line P) where
  carrier := fun l => l.carrier

end Line

-- Now we introduce useful theorems to avoid using more unfolds in further proofs. 
variable {P : Type _} [EuclideanPlane P]

section Compaitiblity_of_coercions_of_mk_pt_pt

-- The first point and the second point in Line.mk_pt_pt LiesOn the line it make. 

theorem fst_pt_lies_on_line_of_pt_pt {A B : P} (h : B ≠ A) : A LiesOn LIN A B h := by
  unfold lies_on Carrier.carrier Line.instCarrierLine
  simp only [Set.setOf_mem_eq]
  unfold Line.carrier Line.mk_pt_pt
  simp only [Set.mem_setOf_eq, vec_same_eq_zero]
  use 0
  simp only [zero_smul]

theorem snd_pt_lies_on_line_of_pt_pt {A B : P} (h : B ≠ A) : B LiesOn LIN A B h := by
  unfold lies_on Carrier.carrier Line.instCarrierLine
  simp only [Set.setOf_mem_eq]
  unfold Line.carrier Line.mk_pt_pt
  simp only [Set.mem_setOf_eq, vec_same_eq_zero]
  use 1
  simp only [one_smul]

theorem pt_lies_on_line_of_pt_pt_of_ne {A B : P} (h: B ≠ A) : A LiesOn LIN A B h ∧ B LiesOn LIN A B h := by
  constructor
  exact fst_pt_lies_on_line_of_pt_pt h
  exact snd_pt_lies_on_line_of_pt_pt h

theorem lies_on_line_of_pt_pt_iff_colinear {A B : P} (h : B ≠ A) : ∀ X : P, (X LiesOn (LIN A B h)) ↔ colinear A B X := by
  intro X
  constructor
  intro hx
  apply (LIN A B h).linear
  exact fst_pt_lies_on_line_of_pt_pt h
  exact snd_pt_lies_on_line_of_pt_pt h
  exact hx
  intro c
  apply (LIN A B h).maximal A B
  exact fst_pt_lies_on_line_of_pt_pt h
  exact snd_pt_lies_on_line_of_pt_pt h
  exact h
  exact c

end Compaitiblity_of_coercions_of_mk_pt_pt

section Define_line_toProj

/- examine a line has uniquely defined toProj -/

theorem vec_eq_smul_vec_of_lies_on {l : Line P} {A B X Y : P} (ha : A LiesOn l) (hb : B LiesOn l) (hx : X LiesOn l) (hy : Y LiesOn l) (hab : B ≠ A) : ∃ t : ℝ, VEC X Y = t • VEC A B := by
  rcases (eq_mul_vec_iff_colinear_of_ne hab).1 (Line.linear A B X ha hb hx) with ⟨t₁, e₁⟩
  rcases (eq_mul_vec_iff_colinear_of_ne hab).1 (Line.linear A B Y ha hb hy) with ⟨t₂, e₂⟩
  use t₂ - t₁
  rw [← vec_sub_vec A, e₁, e₂, sub_smul]

theorem toProj_eq_toProj_of_SegND_lies_on {l : Line P} {A B X Y : P} (ha : A LiesOn l) (hb : B LiesOn l) (hx : X LiesOn l) (hy : Y LiesOn l) (hab : B ≠ A) (hxy : Y ≠ X) : SegND.toProj ⟨SEG A B, hab⟩ = SegND.toProj ⟨SEG X Y, hxy⟩ := by
  rcases (vec_eq_smul_vec_of_lies_on ha hb hx hy hab) with ⟨t, e⟩
  exact eq_toProj_of_smul _ _ e

/- define Line.toProj -/

theorem uniqueness_of_proj_of_line (l : Line P) : ∀ A B C D : P, (A LiesOn l) → (B LiesOn l) → (C LiesOn l) → (D LiesOn l) → (hab : B ≠ A) → (hcd : D ≠ C) → SegND.toProj ⟨SEG A B, hab⟩ = SegND.toProj ⟨SEG C D, hcd⟩ := by
  intro A B C D ha hb hc hd hab hcd
  exact toProj_eq_toProj_of_SegND_lies_on ha hb hc hd hab hcd

theorem exist_unique_proj_of_line (l : Line P) : ∃! pr : Proj, ∀ (A B : P) (ha : A LiesOn l) (hb : B LiesOn l) (h : B ≠ A), SegND.toProj ⟨SEG A B, h⟩ = pr := by
  rcases l.nontriv with ⟨x, ⟨y, c⟩⟩
  use SegND.toProj ⟨SEG x y, c.2.2⟩
  simp
  constructor
  intro A B ha hb hab
  exact toProj_eq_toProj_of_SegND_lies_on ha hb c.1 c.2.1 hab c.2.2
  intro pr w
  rw [← w]
  exact c.1
  exact c.2.1

def Line.toProj (l : Line P) : Proj :=
  Classical.choose (exist_unique_proj_of_line l)
  -- by choose pr _ using (exist_unique_proj_of_line l)
  -- exact pr

-- If you don't want to use Classical.choose, please use this theorem to simplify your Line.toProj. 

theorem line_toProj_eq_seg_nd_toProj_of_lies_on {A B : P} {l : Line P} (ha : A LiesOn l) (hb : B LiesOn l) (hab : B ≠ A) : SegND.toProj ⟨SEG A B, hab⟩ = l.toProj := (Classical.choose_spec (exist_unique_proj_of_line l)).1 A B ha hb hab

theorem line_of_pt_pt_toProj_eq_seg_nd_toProj {A B : P} (h : B ≠ A) : (LIN A B h).toProj = SegND.toProj ⟨SEG A B, h⟩ := by
  symm
  apply line_toProj_eq_seg_nd_toProj_of_lies_on
  exact fst_pt_lies_on_line_of_pt_pt h
  exact snd_pt_lies_on_line_of_pt_pt h

end Define_line_toProj

section Compatibility_of_LiesOn

-- This is also a typical proof that shows how to use the four conditions in the def of a line. Please write it shorter in future.

theorem lies_on_iff_colinear_of_ne_lies_on_lies_on {A B : P} {l : Line P} (h : B ≠ A) (ha : A LiesOn l) (hb : B LiesOn l) : ∀ C : P, (C LiesOn l) ↔ colinear A B C := by
  intro C
  constructor
  intro hc
  apply l.linear
  exact ha
  exact hb
  exact hc
  intro c
  apply l.maximal A B
  exact ha
  exact hb
  exact h
  exact c

/- Two lines are equal iff they have the same carrier -/

theorem lies_on_iff_lies_on_iff_line_eq_line (l₁ l₂ : Line P) : (∀ A : P, A LiesOn l₁ ↔ A LiesOn l₂) ↔ l₁ = l₂ := by
  constructor
  intro hiff
  exact Line.ext l₁ l₂ (Set.ext hiff)
  intro e
  rw [e]
  simp only [forall_const]

/- tautological theorems of Line.mk_pt_pt -/

theorem eq_line_of_pt_pt_of_ne {A B : P} {l : Line P} (h : B ≠ A) (ha : A LiesOn l) (hb : B LiesOn l) : LIN A B h = l := by
  apply (lies_on_iff_lies_on_iff_line_eq_line (LIN A B h) l).1
  intro X
  constructor
  intro hx
  apply (lies_on_iff_colinear_of_ne_lies_on_lies_on h ha hb X).2
  exact (lies_on_line_of_pt_pt_iff_colinear h X).1 hx
  intro hx
  exact (lies_on_line_of_pt_pt_iff_colinear h X).2 ((lies_on_iff_colinear_of_ne_lies_on_lies_on h ha hb X).1 hx)

theorem eq_of_pt_pt_lies_on_of_ne {A B : P} (h : B ≠ A) {l₁ l₂ : Line P}(hA₁ : A LiesOn l₁) (hB₁ : B LiesOn l₁) (hA₂ : A LiesOn l₂) (hB₂ : B LiesOn l₂) : l₁ = l₂ := sorry

theorem colinear_iff_exist_line_lies_on (A B C : P) : colinear A B C ↔ ∃ l : Line P, (A LiesOn l) ∧ (B LiesOn l) ∧ (C LiesOn l) := by
  sorry

end Compatibility_of_LiesOn
/- def coe from ray to line-/

def Ray.toLine (r : Ray P) := LIN r.source (r.toDir.toVec +ᵥ r.source) (by 
  simp only [ne_eq, vadd_eq_self_iff_vec_eq_zero]
  exact Dir.toVec_ne_zero r.toDir)

instance : Coe (Ray P) (Line P) where
  coe := Ray.toLine

theorem ray_toLine_toProj_eq_ray_toProj (r : Ray P) : r.toLine.toProj = r.toProj := by
  sorry

/- def coe from non trivial segment to line-/

def SegND.toLine (seg_nd : SegND P) := (LIN seg_nd.1.source seg_nd.1.target seg_nd.2)

def Line.mk_pt_vec_nd (A : P) (vec_nd : VecND) := (LIN A (vec_nd.1 +ᵥ A) (by
  sorry))

section Compaitiblity_of_coercions

-- If a point lies on a ray, then it lies on the line associated to the ray.
theorem Ray.lies_on_toLine_of_lie_on {A : P} {r : Ray P} (h : A LiesOn r) : A LiesOn (r.toLine) := sorry

theorem SegND.lies_on_toLine_of_lie_on {A : P} {s : SegND P} (h : A LiesOn s.1) : A LiesOn (s.toLine) := sorry

-- If A and B are two distinct points, they lie on the line AB
theorem Ray.source_lies_on_toLine (l : Ray P) : l.source LiesOn l.toLine := sorry

theorem SegND.source_lies_on_toLine (s : SegND P) : s.1.source LiesOn s.toLine := sorry

theorem SegND.target_lies_on_toLine (s : SegND P) : s.1.target LiesOn s.toLine := sorry

-- The line defined from a nontrivial segment is equal to the line defined from the ray associated this nontrivial segment

theorem SegND.toLine_eq_toray_toLine (seg_nd : SegND P) : seg_nd.toLine = (seg_nd.toRay).toLine := sorry

theorem line_of_pt_pt_eq_ray_toLine {A B : P} (h : B ≠ A) : LIN A B h = Ray.toLine (RAY A B h) := sorry

theorem line_of_pt_pt_eq_seg_nd_toLine {A B : P} (h : B ≠ A) : LIN A B h = SegND.toLine ⟨SEG A B, h⟩ := rfl

end Compaitiblity_of_coercions

section Archimedean_property

-- there are two distinct points on a line

theorem exists_ne_pt_pt_lies_on_of_line (A : P) (l : Line P) : ∃ B : P, B LiesOn l ∧ B ≠ A := by
  rcases l.nontriv with ⟨X, ⟨Y, _⟩⟩
  by_cases A = X
  · use Y
    rw [h]
    tauto
  · use X
    tauto

theorem lies_on_of_SegND_toProj_eq_toProj {A B : P} {l : Line P} (ha : A LiesOn l) (hab : B ≠ A) (hp : SegND.toProj ⟨SEG A B, hab⟩ = l.toProj) : B LiesOn l := by
  rcases exists_ne_pt_pt_lies_on_of_line A l with ⟨X, h⟩
  let g := line_toProj_eq_seg_nd_toProj_of_lies_on ha h.1 h.2
  rw [← hp] at g
  unfold SegND.toProj SegND.toVecND at g
  simp only [ne_eq] at g 
  have c : colinear A X B := by
    rw [← iff_true (colinear A X B), ← eq_iff_iff]
    unfold colinear colinear_of_nd
    simp [g]
    by_cases (B = X ∨ A = B ∨ X = A) 
    · simp only [h, dite_eq_ite]
    · simp only [h, dite_eq_ite]
  exact (lies_on_iff_colinear_of_ne_lies_on_lies_on h.2 ha h.1 B).2 c

theorem lies_on_iff_eq_toProj_of_lies_on {A B : P} {l : Line P} (ha : A LiesOn l) (hab : B ≠ A) : B LiesOn l ↔ (SegND.toProj ⟨SEG A B, hab⟩ = l.toProj) := by
  constructor
  exact fun a => line_toProj_eq_seg_nd_toProj_of_lies_on ha a hab
  exact fun a => lies_on_of_SegND_toProj_eq_toProj ha hab a

-- Given distinct A B on a line, there exist C s.t. C LiesOn AB (a cor of Archimedean_property in Seg) and there exist D s.t. B LiesOn AD
theorem Line.exist_pt_beyond_pt {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) (h : B ≠ A) : (∃ C D : P, (C LiesOn l) ∧ (D LiesOn l) ∧ (A LiesInt (SEG C B)) ∧ (B LiesInt (SEG A D))) := sorry

end Archimedean_property

section Line_passing_point_with_given_Proj

theorem exist_line_of_pt_proj (A : P) (pr : Proj) : ∃ l : Line P, A LiesOn l ∧ l.toProj = pr := by
  rcases Quot.exists_rep pr with ⟨dir, hd⟩ 
  let r : Ray P := ⟨A, dir⟩ 
  use r.toLine
  constructor
  exact Ray.lies_on_toLine_of_lie_on (Ray.source_lies_on r)
  rw [ray_toLine_toProj_eq_ray_toProj r]
  exact hd

theorem exist_unique_line_of_pt_proj (A : P) (pr : Proj) : ∃! l : Line P, A LiesOn l ∧ l.toProj = pr := by
  rcases (exist_line_of_pt_proj A pr) with ⟨l₁, hl₁⟩
  use l₁
  constructor
  exact hl₁
  intro l₂ hl₂
  rcases Quot.exists_rep pr with ⟨dir, _⟩
  have _ : dir.toVec +ᵥ A ≠ A := by
    simp only [ne_eq, vadd_eq_self_iff_vec_eq_zero, Dir.toVec_ne_zero dir, not_false_eq_true]
  apply (lies_on_iff_lies_on_iff_line_eq_line l₂ l₁).1
  intro X
  by_cases X = A 
  · rw [h]
    tauto
  · rw [lies_on_iff_eq_toProj_of_lies_on hl₁.1 h, hl₁.2, lies_on_iff_eq_toProj_of_lies_on hl₂.1 h, hl₂.2]

def Line.mk_pt_proj (A : P) (pr : Proj) : Line P := 
  Classical.choose (exist_unique_line_of_pt_proj A pr)

theorem pt_lies_on_and_proj_eq_of_line_mk_pt_proj (A : P) (pr : Proj) : A LiesOn (Line.mk_pt_proj A pr) ∧ (Line.mk_pt_proj A pr).toProj = pr := by
  exact (Classical.choose_spec (exist_unique_line_of_pt_proj A pr)).1

end Line_passing_point_with_given_Proj

end EuclidGeom