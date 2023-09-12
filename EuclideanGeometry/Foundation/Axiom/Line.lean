import EuclideanGeometry.Foundation.Axiom.Position

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

theorem pt_eq_pt_of_eq_smul_smul {O A B : P} {v : Vec} {tA tB : ℝ} (h : tA = tB) (ha : VEC O A = tA • v) (hb : VEC O B = tB • v) : A = B := by
  have hab : tB - tA = 0 := Iff.mpr sub_eq_zero (Eq.symm h)
  have hc : VEC A B = VEC O B - VEC O A := by
    unfold Vec.mk_pt_pt
    simp only [vsub_sub_vsub_cancel_right]
  rw [ha, hb, ← sub_smul, hab, zero_smul] at hc
  symm
  exact (eq_iff_vec_eq_zero A B).2 hc

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

variable {P : Type _} [EuclideanPlane P]

/- Def of point lies on a line -/
def IsOnLine (a : P) (l : Line P) : Prop :=
  a ∈ l.carrier

instance : HasLiesOn P (Line P) where
  lies_on := IsOnLine

-- Now we introduce useful theorems to avoid using more unfolds in further proofs. 

section Compaitiblity_of_coersions_of_mk_pt_pt

-- The first point and the second point in Line.mk_pt_pt LiesOn the line it make. 

theorem fst_pt_lies_on_line_of_pt_pt_of_ne {A B : P} (h : B ≠ A) : A LiesOn LIN A B h := by
  unfold HasLiesOn.lies_on instHasLiesOnLine IsOnLine Line.carrier Line.mk_pt_pt
  simp only [Set.mem_setOf_eq, vec_same_eq_zero]
  use 0
  simp only [zero_smul]

theorem snd_pt_lies_on_line_of_pt_pt_of_ne {A B : P} (h : B ≠ A) : B LiesOn LIN A B h := by
  unfold HasLiesOn.lies_on instHasLiesOnLine IsOnLine Line.carrier Line.mk_pt_pt
  simp only [Set.mem_setOf_eq, vec_same_eq_zero]
  use 1
  simp only [one_smul]

theorem pt_lies_on_line_of_pt_pt_of_ne {A B : P} (h: B ≠ A) : A LiesOn LIN A B h ∧ B LiesOn LIN A B h := by
  constructor
  exact fst_pt_lies_on_line_of_pt_pt_of_ne h
  exact snd_pt_lies_on_line_of_pt_pt_of_ne h

theorem lies_on_line_of_pt_pt_iff_colinear {A B : P} (h : B ≠ A) : ∀ X : P, (X LiesOn (LIN A B h)) ↔ colinear A B X := by
  intro X
  constructor
  intro hx
  apply (LIN A B h).linear
  exact fst_pt_lies_on_line_of_pt_pt_of_ne h
  exact snd_pt_lies_on_line_of_pt_pt_of_ne h
  exact hx
  intro c
  apply (LIN A B h).maximal A B
  exact fst_pt_lies_on_line_of_pt_pt_of_ne h
  exact snd_pt_lies_on_line_of_pt_pt_of_ne h
  exact h
  exact c

end Compaitiblity_of_coersions_of_mk_pt_pt

section Compatibility_of_LiesOn

-- This is also a typical proof that shows how to use the four conditions in the def of a line

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

theorem line_eq_line_of_pt_pt_of_ne {A B : P} {l : Line P} (h : B ≠ A) (ha : A LiesOn l) (hb : B LiesOn l) : LIN A B h = l := by
  apply (lies_on_iff_lies_on_iff_line_eq_line (LIN A B h) l).1
  intro X
  constructor
  intro hx
  apply (lies_on_iff_colinear_of_ne_lies_on_lies_on h ha hb X).2
  exact (lies_on_line_of_pt_pt_iff_colinear h X).1 hx
  intro hx
  exact (lies_on_line_of_pt_pt_iff_colinear h X).2 ((lies_on_iff_colinear_of_ne_lies_on_lies_on h ha hb X).1 hx)

end Compatibility_of_LiesOn

section Define_line_toProj

/- examine a line has uniquely defined toProj -/

theorem vec_eq_smul_vec_of_lies_on {l : Line P} {A B X Y : P} (ha : A LiesOn l) (hb : B LiesOn l) (hx : X LiesOn l) (hy : Y LiesOn l) (hab : B ≠ A) : ∃ t : ℝ, VEC X Y = t • VEC A B := by
  rcases (eq_mul_vec_iff_colinear_of_ne hab).1 (Line.linear A B X ha hb hx) with ⟨t₁, e₁⟩
  rcases (eq_mul_vec_iff_colinear_of_ne hab).1 (Line.linear A B Y ha hb hy) with ⟨t₂, e₂⟩
  use t₂ - t₁
  rw [← vec_sub_vec A, e₁, e₂, sub_smul]

theorem toProj_eq_toProj_of_Seg_nd_lies_on {l : Line P} {A B X Y : P} (ha : A LiesOn l) (hb : B LiesOn l) (hx : X LiesOn l) (hy : Y LiesOn l) (hab : B ≠ A) (hxy : Y ≠ X) : Seg_nd.toProj ⟨SEG A B, hab⟩ = Seg_nd.toProj ⟨SEG X Y, hxy⟩ := by
  rcases (vec_eq_smul_vec_of_lies_on ha hb hx hy hab) with ⟨t, e⟩
  exact eq_toProj_of_smul _ _ e

/- define Line.toProj -/

theorem uniqueness_of_proj_of_line (l : Line P) : ∀ A B C D : P, (A LiesOn l) → (B LiesOn l) → (C LiesOn l) → (D LiesOn l) → (hab : B ≠ A) → (hcd : D ≠ C) → Seg_nd.toProj ⟨SEG A B, hab⟩ = Seg_nd.toProj ⟨SEG C D, hcd⟩ := by
  intro A B C D ha hb hc hd hab hcd
  exact toProj_eq_toProj_of_Seg_nd_lies_on ha hb hc hd hab hcd

theorem exist_unique_proj_of_line (l : Line P) : ∃! pr : Proj, ∀ (A B : P) (ha : A LiesOn l) (hb : B LiesOn l) (h : B ≠ A), Seg_nd.toProj ⟨SEG A B, h⟩ = pr := by
  rcases l.nontriv with ⟨x, ⟨y, c⟩⟩
  use Seg_nd.toProj ⟨SEG x y, c.2.2⟩
  simp
  constructor
  intro A B ha hb hab
  exact toProj_eq_toProj_of_Seg_nd_lies_on ha hb c.1 c.2.1 hab c.2.2
  intro pr w
  rw [← w]
  exact c.1
  exact c.2.1

def Line.toProj (l : Line P) : Proj :=
  Classical.choose (exist_unique_proj_of_line l)
  -- by choose pr _ using (exist_unique_proj_of_line l)
  -- exact pr

-- If you don't want to use Classical.choose, please use this theorem to simplify your Line.toProj. 

theorem line_toProj_eq_seg_nd_toProj_of_lies_on {A B : P} {l : Line P} (ha : A LiesOn l) (hb : B LiesOn l) (hab : B ≠ A) : Seg_nd.toProj ⟨SEG A B, hab⟩ = l.toProj := (Classical.choose_spec (exist_unique_proj_of_line l)).1 A B ha hb hab

theorem line_of_pt_pt_toProj_eq_seg_nd_toProj {A B : P} (h : B ≠ A) : (LIN A B h).toProj = Seg_nd.toProj ⟨SEG A B, h⟩ := by
  symm
  apply line_toProj_eq_seg_nd_toProj_of_lies_on
  exact fst_pt_lies_on_line_of_pt_pt_of_ne h
  exact snd_pt_lies_on_line_of_pt_pt_of_ne h

end Define_line_toProj

/- def coe from ray to line-/

def Ray.toLine (r : Ray P) := LIN r.source (r.toDir.toVec +ᵥ r.source) (by 
  by_contra h
  exact (Dir.dir_toVec_ne_zero r.toDir) (vec_eq_zero_of_vadd_eq_self h))

instance : Coe (Ray P) (Line P) where
  coe := Ray.toLine

theorem ray_toLine_toProj_eq_ray_toProj (r : Ray P) : r.toLine.toProj = r.toProj := by
  sorry

/- def coe from non trivial segment to line-/

def Seg_nd.toLine (seg_nd : Seg_nd P) := (LIN seg_nd.1.source seg_nd.1.target seg_nd.2)

def Line.mk_pt_vec_nd (A : P) (vec_nd : Vec_nd) := (LIN A (vec_nd.1 +ᵥ A) (by
  sorry))

section Compaitiblity_of_coersions
-- If a point lies on a ray, then it lies on the line associated to the ray.
theorem lies_on_line_of_ray_of_lies_on_ray {A : P} {r : Ray P} (h : A LiesOn r) : A LiesOn (r.toLine) := sorry

-- If A and B are two distinct points, they lie on the line AB
theorem source_of_ray_lies_on_line_of_ray (l : Ray P) : l.source LiesOn l := sorry

-- The line defined from a nontrivial segment is equal to the line defined from the ray associated this nontriial segment

theorem line_of_nontriv_seg_eq_line_of_ray_of_nontriv_seg (seg_nd : Seg_nd P) : seg_nd.toLine = (seg_nd.toRay).toLine := sorry

theorem line_eq_line_of_seg_of_pt_pt_of_ne {A B : P} (h : B ≠ A) : LIN A B h = Seg_nd.toLine ⟨SEG A B, h⟩ := rfl

end Compaitiblity_of_coersions

section Archimedean_property

-- there are two distinct points on a line

theorem exists_ne_pt_pt_lies_on_of_line (l : Line P) : ∃ A B : P, A LiesOn l ∧ B LiesOn l ∧ B ≠ A := l.nontriv

-- Given distinct A B on a line, there exist C s.t. C LiesOn AB (a cor of Archimedean_property in Seg) and there exist D s.t. B LiesOn AD

end Archimedean_property

-- where should this theorem be placed?
/-
theorem vec_eq_mul_vec_of_pt_pt_on_line (l : Line P) (A B C D : P) (ha : A LiesOn l) (hb : B LiesOn l) (hC : C LiesOn l) (hD : D LiesOn l) (h : B ≠ A) : ∃ (t : ℝ), VEC C D = t • VEC A B := by
  sorry
-/
-- I think this theorem is just a corollary of our theorems. We should put it in some _ex. 

section Line_passing_point_with_given_Proj

theorem exist_line_of_pt_proj (A : P) (pr : Proj) : ∃ l : Line P, A LiesOn l ∧ l.toProj = pr := by
  rcases Quot.exists_rep pr with ⟨dir, hd⟩ 
  let r : Ray P := ⟨A, dir⟩ 
  use r.toLine
  constructor
  exact lies_on_line_of_ray_of_lies_on_ray (source_of_ray_lies_on_ray r)
  rw [ray_toLine_toProj_eq_ray_toProj r]
  exact hd

theorem exist_unique_line_mk_pt_proj (A : P) (pr : Proj) : ∃! l : Line P, A LiesOn l ∧ l.toProj = pr := by
  rcases (exist_line_of_pt_proj A pr) with ⟨l, hl⟩
  use l
  constructor
  exact hl
  intro l' hl'
  sorry

def Line.mk_pt_proj (A : P) (pr : Proj) : Line P := 
  Classical.choose (exist_unique_line_mk_pt_proj A pr)

theorem pt_lies_on_line_mk_pt_proj (A : P) (pr : Proj) : A LiesOn (Line.mk_pt_proj A pr) ∧ (Line.mk_pt_proj A pr).toProj = pr := by
  exact (Classical.choose_spec (exist_unique_line_mk_pt_proj A pr)).1

end Line_passing_point_with_given_Proj

end EuclidGeom