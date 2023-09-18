import EuclideanGeometry.Foundation.Axiom.Linear.Colinear
import EuclideanGeometry.Foundation.Axiom.Linear.Ray
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex

noncomputable section
namespace EuclidGeom

section setoid

variable {P : Type _} [EuclideanPlane P]

def same_extn_line : Ray P → Ray P → Prop := fun r₁ r₂ => r₁.toProj = r₂.toProj ∧ (r₂.source LiesOn r₁ ∨ r₂.source LiesOn r₁.reverse) 

namespace same_extn_line

theorem dir_eq_or_eq_neg {x y : Ray P} (h : same_extn_line x y) : (x.toDir = y.toDir ∨ x.toDir = - y.toDir) := (Dir.eq_toProj_iff _ _).mp h.1

protected theorem refl (x : Ray P) : same_extn_line x x := ⟨rfl, Or.inl (Ray.source_lies_on x)⟩  

protected theorem symm {x y : Ray P} (h : same_extn_line x y) : same_extn_line y x := by
  constructor
  · exact h.1.symm 
  · have g := dir_eq_or_eq_neg h
    cases g with 
    | inl h₁ => sorry
    | inr h₂ => sorry

protected theorem trans {x y z : Ray P} (h₁ : same_extn_line x y) (h₂ : same_extn_line y z) :  same_extn_line x z := sorry

protected def setoid : Setoid (Ray P) where
  r := same_extn_line
  iseqv := {
    refl := same_extn_line.refl
    symm := same_extn_line.symm
    trans := same_extn_line.trans
  }

instance : Setoid (Ray P) := same_extn_line.setoid

end same_extn_line

theorem same_extn_line_of_PM (A : P) (x y : Dir) (h : PM x y) : same_extn_line (Ray.mk A x) (Ray.mk A y) := sorry 

theorem same_extn_line.eq_carrier_union_rev_carrier (ray ray' : Ray P) (h : same_extn_line ray ray') : ray.carrier ∪ ray.reverse.carrier = ray'.carrier ∪ ray'.reverse.carrier := sorry

end setoid

def Line (P : Type _) [EuclideanPlane P] := Quotient (@same_extn_line.setoid P _)

variable  {P : Type _} [EuclideanPlane P] 

section make

namespace Line

-- define a line from two points 
def mk_pt_pt (A B : P) (h : B ≠ A) : Line P := ⟦RAY A B h⟧

-- define a line from a point and a proj
def mk_pt_proj (A : P) (proj : Proj) : Line P := Quotient.map (sa := PM.con.toSetoid) (fun x : Dir => Ray.mk A x) (same_extn_line_of_PM A) proj

-- define a line from a point and a direction
def mk_pt_dir (A : P) (dir : Dir) : Line P := mk_pt_proj A dir.toProj

-- define a line from a point and a nondegenerate vector
def mk_pt_vec_nd (A : P) (vec_nd : Vec_nd) : Line P := mk_pt_proj A vec_nd.toProj

end Line

scoped notation "LIN" => Line.mk_pt_pt 

end make

section coercion

def Ray.toLine (ray : Ray P) : Line P := ⟦ray⟧ 

def Seg_nd.toLine (seg_nd : Seg_nd P) : Line P := ⟦seg_nd.toRay⟧

section carrier

namespace Line

protected def carrier (l : Line P) : Set P := Quotient.lift (fun ray : Ray P => ray.carrier ∪ ray.reverse.carrier) (same_extn_line.eq_carrier_union_rev_carrier) l

/- Def of point lies on a line, LiesInt is not defined -/
protected def IsOn (a : P) (l : Line P) : Prop :=
  a ∈ l.carrier

instance : Carrier P (Line P) where
  carrier := fun l => l.carrier

theorem linear (l : Line P) (A B C : P) : (A ∈ l.carrier) → (B ∈ l.carrier) → (C ∈ l.carrier) → colinear A B C := sorry

theorem maximal : sorry := sorry

theorem nontriv : sorry := sorry

end Line

end carrier

end coercion

section compatibility

variable (A B : P) (h : B ≠ A) (ray : Ray P) (seg_nd : Seg_nd P)

section pt_pt

theorem line_of_pt_pt_eq_rev : LIN A B h = LIN B A h.symm := sorry

theorem fst_pt_lies_on_line_of_pt_pt {A B : P} (h : B ≠ A) : A LiesOn LIN A B h := Or.inl (Ray.source_lies_on (RAY A B h))

theorem snd_pt_lies_on_line_of_pt_pt {A B : P} (h : B ≠ A) : B LiesOn LIN A B h := sorry

end pt_pt

theorem Ray.toLine_eq_rev_toLine : ray.toLine = ray.reverse.toLine := sorry

theorem Seg_nd.toLine_eq_rev_toLine : seg_nd.toLine = seg_nd.reverse.toLine := sorry

theorem toLine_eq_extn_toLine : seg_nd.toLine = seg_nd.extension.toLine := sorry

end compatibility

namespace Line

variable {P : Type _} [EuclideanPlane P]

end Line

-- Now we introduce useful theorems to avoid using more unfolds in further proofs. 
variable {P : Type _} [EuclideanPlane P]

section Compaitiblity_of_coersions_of_mk_pt_pt

-- The first point and the second point in Line.mk_pt_pt LiesOn the line it make. 

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

end Compaitiblity_of_coersions_of_mk_pt_pt

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

def Seg_nd.toLine (seg_nd : Seg_nd P) := (LIN seg_nd.1.source seg_nd.1.target seg_nd.2)

def Line.mk_pt_vec_nd (A : P) (vec_nd : Vec_nd) := (LIN A (vec_nd.1 +ᵥ A) (by
  sorry))

section Compaitiblity_of_coersions

-- If a point lies on a ray, then it lies on the line associated to the ray.
theorem Ray.lies_on_toLine_of_lie_on {A : P} {r : Ray P} (h : A LiesOn r) : A LiesOn (r.toLine) := sorry

theorem Seg_nd.lies_on_toLine_of_lie_on {A : P} {s : Seg_nd P} (h : A LiesOn s.1) : A LiesOn (s.toLine) := sorry

-- If A and B are two distinct points, they lie on the line AB
theorem Ray.source_lies_on_toLine (l : Ray P) : l.source LiesOn l.toLine := sorry

theorem Seg_nd.source_lies_on_toLine (s : Seg_nd P) : s.1.source LiesOn s.toLine := sorry

theorem Seg_nd.target_lies_on_toLine (s : Seg_nd P) : s.1.target LiesOn s.toLine := sorry

-- The line defined from a nontrivial segment is equal to the line defined from the ray associated this nontrivial segment

theorem Seg_nd.toLine_eq_toRay_toLine (seg_nd : Seg_nd P) : seg_nd.toLine = (seg_nd.toRay).toLine := sorry

theorem line_of_pt_pt_eq_ray_toLine {A B : P} (h : B ≠ A) : LIN A B h = Ray.toLine (RAY A B h) := sorry

theorem line_of_pt_pt_eq_seg_nd_toLine {A B : P} (h : B ≠ A) : LIN A B h = Seg_nd.toLine ⟨SEG A B, h⟩ := rfl

end Compaitiblity_of_coersions

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

theorem lies_on_of_Seg_nd_toProj_eq_toProj {A B : P} {l : Line P} (ha : A LiesOn l) (hab : B ≠ A) (hp : Seg_nd.toProj ⟨SEG A B, hab⟩ = l.toProj) : B LiesOn l := by
  rcases exists_ne_pt_pt_lies_on_of_line A l with ⟨X, h⟩
  let g := line_toProj_eq_seg_nd_toProj_of_lies_on ha h.1 h.2
  rw [← hp] at g
  unfold Seg_nd.toProj Seg_nd.toVec_nd at g
  simp only [ne_eq] at g 
  have c : colinear A X B := by
    rw [← iff_true (colinear A X B), ← eq_iff_iff]
    unfold colinear colinear_of_nd
    simp [g]
    by_cases (B = X ∨ A = B ∨ X = A) 
    · simp only [h, dite_eq_ite]
    · simp only [h, dite_eq_ite]
  exact (lies_on_iff_colinear_of_ne_lies_on_lies_on h.2 ha h.1 B).2 c

theorem Seg_nd_toProj_eq_toProj_iff_lies_on {A B : P} {l : Line P} (ha : A LiesOn l) (hab : B ≠ A) : B LiesOn l ↔ (Seg_nd.toProj ⟨SEG A B, hab⟩ = l.toProj) := by
  constructor
  exact fun a => line_toProj_eq_seg_nd_toProj_of_lies_on ha a hab
  exact fun a => lies_on_of_Seg_nd_toProj_eq_toProj ha hab a

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
  · rw [Seg_nd_toProj_eq_toProj_iff_lies_on hl₁.1 h, hl₁.2, Seg_nd_toProj_eq_toProj_iff_lies_on hl₂.1 h, hl₂.2]

def Line.mk_pt_proj (A : P) (pr : Proj) : Line P := 
  Classical.choose (exist_unique_line_of_pt_proj A pr)

theorem pt_lies_on_and_proj_eq_of_line_mk_pt_proj (A : P) (pr : Proj) : A LiesOn (Line.mk_pt_proj A pr) ∧ (Line.mk_pt_proj A pr).toProj = pr := by
  exact (Classical.choose_spec (exist_unique_line_of_pt_proj A pr)).1

end Line_passing_point_with_given_Proj

end EuclidGeom