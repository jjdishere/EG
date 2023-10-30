import EuclideanGeometry.Foundation.Axiom.Linear.Colinear
import EuclideanGeometry.Foundation.Axiom.Linear.Ray
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex

noncomputable section
namespace EuclidGeom

section setoid

variable {P : Type _} [EuclideanPlane P]

def same_extn_line : Ray P → Ray P → Prop := fun r r' => r.toProj = r'.toProj ∧ (r'.source LiesOn r ∨ r'.source LiesOn r.reverse)

namespace same_extn_line

theorem dir_eq_or_eq_neg {r r' : Ray P} (h : same_extn_line r r') : (r.toDir = r'.toDir ∨ r.toDir = - r'.toDir) := (Dir.eq_toProj_iff _ _).mp h.1

theorem vec_parallel_of_same_extn_line {r r' : Ray P} (h : same_extn_line r r') : ∃t : ℝ, r'.toDir.toVec = t • r.toDir.toVec := by
  rcases (Dir.eq_toProj_iff _ _).mp h.1 with rr' | rr'
  · use 1
    rw [one_smul, rr']
  · use -1
    rw [rr', Dir.toVec_neg_eq_neg_toVec, smul_neg, neg_smul, one_smul, neg_neg]

theorem ray_rev_of_same_extn_line {r : Ray P} : same_extn_line r r.reverse := by 
  constructor
  · simp [Ray.toProj_of_rev_eq_toProj]
  · right
    exact Ray.source_lies_on

theorem pt_pt_ray_same_extn_line_of_pt_pt_lies_on_line {A B : P} {r : Ray P} (h : B ≠ A) (ha : A LiesOn r ∨ A LiesOn r.reverse) (hb : B LiesOn r ∨ B LiesOn r.reverse) : same_extn_line r (Ray.mk_pt_pt A B h) := by 
  constructor
  · exact ray_toProj_eq_mk_pt_pt_toProj h ha hb
  · by_cases  A LiesOn r
    · left
      exact h
    · right
      tauto

protected theorem refl (r : Ray P) : same_extn_line r r := ⟨rfl, Or.inl (Ray.source_lies_on)⟩

protected theorem symm {r r' : Ray P} (h : same_extn_line r r') : same_extn_line r' r := by
  constructor
  · exact h.1.symm
  · rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h.2 with ⟨a, dxy⟩
    apply pt_lies_on_line_from_ray_iff_vec_parallel.mpr
    have h₁ : VEC r'.source r.source = - VEC r.source r'.source := by simp [neg_vec]
    rw [dxy] at h₁
    rcases (Dir.eq_toProj_iff _ _).mp h.1 with xy | xy
    · have : r'.toDir.toVec = r.toDir.toVec := by rw [xy]
      use -a
      rw [h₁]
      rw [this]
      rw [neg_smul]
    · have : r'.toDir.toVec = -1 • r.toDir.toVec := by
        rw [xy]
        rw [Dir.toVec_neg_eq_neg_toVec]
        rw [smul_neg]
        rw [neg_smul]
        rw [one_smul]
        rw [neg_neg]
      use a
      rw [h₁]
      rw [this]
      rw [neg_smul]
      rw [one_smul]
      rw [smul_neg]

protected theorem trans {r r' r'' : Ray P} (h₁ : same_extn_line r r') (h₂ : same_extn_line r' r'') : same_extn_line r r'' where
  left := Eq.trans h₁.1 h₂.1
  right := by
    rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h₁.2 with ⟨a, dr'r⟩
    rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h₂.2 with ⟨b, dr''r'⟩
    apply pt_lies_on_line_from_ray_iff_vec_parallel.mpr
    let ⟨t, rparr'⟩ := vec_parallel_of_same_extn_line h₁
    use a + b * t
    rw [rparr'] at dr''r'
    rw [(vec_add_vec _ _ _).symm, dr'r, dr''r']
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_add]
    ring_nf

protected def setoid : Setoid (Ray P) where
  r := same_extn_line
  iseqv := {
    refl := same_extn_line.refl
    symm := same_extn_line.symm
    trans := same_extn_line.trans
  }

instance : Setoid (Ray P) := same_extn_line.setoid

end same_extn_line

theorem same_extn_line_of_PM (A : P) (x y : Dir) (h : PM x y) : same_extn_line (Ray.mk A x) (Ray.mk A y) := by
  constructor
  · simp only [Ray.toProj, Dir.eq_toProj_iff', h]
  · exact Or.inl Ray.source_lies_on

theorem same_extn_line.eq_carrier_union_rev_carrier (r r' : Ray P) (h : same_extn_line r r') : r.carrier ∪ r.reverse.carrier = r'.carrier ∪ r'.reverse.carrier := by 
  ext p
  simp only [Set.mem_union, Ray.in_carrier_iff_lies_on, pt_lies_on_line_from_ray_iff_vec_parallel]
  constructor
  · rintro ⟨c, hc⟩
    let ⟨a, ha⟩ := pt_lies_on_line_from_ray_iff_vec_parallel.mp h.symm.2
    let ⟨b, hb⟩ := dir_parallel_of_same_proj h.symm.1
    use a + c * b
    calc
      VEC r'.source p = VEC r'.source r.source + VEC r.source p := (vec_add_vec _ _ _).symm
      _ = a • r'.toDir.toVec + c • r.toDir.toVec := by rw [ha, hc]
      _ = a • r'.toDir.toVec + (c * b) • r'.toDir.toVec := by
        simp only [hb, Complex.real_smul, Complex.ofReal_mul, add_right_inj]
        ring_nf
      _ = (a + c * b) • r'.toDir.toVec := (add_smul _ _ _).symm
  · rintro ⟨c, hc⟩
    let ⟨a, ha⟩ := pt_lies_on_line_from_ray_iff_vec_parallel.mp h.2
    let ⟨b, hb⟩ := dir_parallel_of_same_proj h.1
    use a + c * b
    calc
      VEC r.source p = VEC r.source r'.source + VEC r'.source p := (vec_add_vec _ _ _).symm
      _ = a • r.toDir.toVec + c • r'.toDir.toVec := by rw [ha, hc]
      _ = a • r.toDir.toVec + (c * b) • r.toDir.toVec := by
        simp only [hb, Complex.real_smul, Complex.ofReal_mul, add_right_inj]
        ring_nf
      _ = (a + c * b) • r.toDir.toVec := (add_smul _ _ _).symm

end setoid

def Line (P : Type _) [EuclideanPlane P] := Quotient (@same_extn_line.setoid P _)

variable {P : Type _} [EuclideanPlane P]

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

def Line.toProj (l : Line P) : Proj := Quotient.lift (fun ray : Ray P => ray.toProj) (fun _ _ h => And.left h) l

def Ray.toLine (ray : Ray P) : Line P := ⟦ray⟧

def Seg_nd.toLine (seg_nd : Seg_nd P) : Line P := ⟦seg_nd.toRay⟧

instance : Coe (Ray P) (Line P) where
  coe := Ray.toLine



section carrier

namespace Line

protected def carrier (l : Line P) : Set P := Quotient.lift (fun ray : Ray P => ray.carrier ∪ ray.reverse.carrier) (same_extn_line.eq_carrier_union_rev_carrier) l

/- Def of point lies on a line, LiesInt is not defined -/
protected def IsOn (A : P) (l : Line P) : Prop :=
  A ∈ l.carrier

instance : Carrier P (Line P) where
  carrier := fun l => l.carrier

end Line

--**section carrier in here may overlap with "section coercion in Line_ex" and may need to be unified. (carrier vs lieson)
theorem Ray.toLine_carrier_eq_ray_carrier_union_rev_carrier (r : Ray P) : r.toLine.carrier = r.carrier ∪ r.reverse.carrier := rfl

theorem Ray.subset_toLine {r : Ray P} : r.carrier ⊆ r.toLine.carrier := by
  rw [toLine_carrier_eq_ray_carrier_union_rev_carrier]
  exact Set.subset_union_left _ _
-- A point lies on a line associated to a ray if and only if it lies on the ray or the reverse of the ray

theorem Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev {A : P} {r : Ray P}: (A LiesOn r.toLine) ↔ (A LiesOn r) ∨ (A LiesOn r.reverse) := by
  simp only [lies_on]
  rw [← Set.mem_union]
  revert A
  rw [← Set.ext_iff]
  exact Ray.toLine_carrier_eq_ray_carrier_union_rev_carrier r

theorem Ray.in_carrier_toLine_iff_in_or_in_rev {r : Ray P} {A : P} : (A ∈ r.toLine.carrier) ↔ ((A ∈ r.carrier) ∨ (A ∈ r.reverse.carrier)) := by rfl

theorem Line.in_carrier_iff_lies_on {l : Line P} {A : P} : A LiesOn l ↔ A ∈ l.carrier := by rfl
  
theorem Ray.lies_on_toLine_iff_lies_int_or_lies_int_rev_or_eq_source {A : P} {r : Ray P} : (A LiesOn r.toLine) ↔ (A LiesInt r) ∨ (A LiesInt r.reverse) ∨ (A = r.source) := by
  rw [Ray.lies_int_def, Ray.lies_int_def, Ray.source_of_rev_eq_source]
  have : A LiesOn r ∧ A ≠ r.source ∨ A LiesOn r.reverse ∧ A ≠ r.source ∨ A = r.source ↔ A LiesOn r ∨ A LiesOn r.reverse := by 
    constructor
    · exact fun
      | .inl h => Or.inl h.1
      | .inr h => by
        rcases h with h | h
        · exact Or.inr h.1
        · right
          rw [h]
          exact Ray.source_lies_on
    · exact fun
      | .inl h => by
        by_cases g : A = source
        · exact Or.inr (Or.inr g)
        · exact Or.inl ⟨h, g⟩
      | .inr h => by
        by_cases g : A = source
        · exact Or.inr (Or.inr g)
        · exact Or.inr (Or.inl ⟨h, g⟩)
  rw [this, Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev]

end carrier



namespace Line



-- **section pt_pt--
-- **This part appears in both Line and Line.ex and needs to be unified.
theorem line_of_pt_pt_eq_rev {A B : P} (h : B ≠ A): LIN A B h = LIN B A h.symm := Quotient.eq.mpr ⟨Ray.toProj_eq_toProj_of_mk_pt_pt h, Or.inl (Ray.snd_pt_lies_on_mk_pt_pt h)⟩

theorem Line.fst_pt_lies_on_mk_pt_pt {A B : P} (h : B ≠ A) : A LiesOn LIN A B h := Or.inl (Ray.source_lies_on)
    
theorem Line.snd_pt_lies_on_mk_pt_pt {A B : P} (h : B ≠ A) : B LiesOn LIN A B h := by
  rw [line_of_pt_pt_eq_rev]
  exact fst_pt_lies_on_mk_pt_pt h.symm
-- **end pt_pt--



--**We can put "section pt_proj of Line_ex" here.



--**section coercion--
--**This part overlaps a lot with "section coercion of Line_ex" and needs to be unified.
theorem ray_rev_toLine_eq_ray_toLine {r : Ray P} : r.toLine = r.reverse.toLine := Quotient.eq.mpr same_extn_line.ray_rev_of_same_extn_line

theorem seg_toLine_eq_seg_toRay_toLine {s : Seg_nd P} : s.toRay.toLine = s.toLine := rfl

theorem ray_subset_line {r : Ray P} {l : Line P} (h : r.toLine = l) : r.carrier ⊆ l.carrier := by
  rw [← h]
  exact r.subset_toLine

theorem seg_lies_on_Line {s : Seg_nd P}{A : P}(h : A LiesOn s.1) : A LiesOn s.toLine := by 
  have g : A ∈ s.toRay.carrier := Seg_nd.lies_on_toRay_of_lies_on h
  have h : s.toRay.toLine = s.toLine := rfl
  exact Set.mem_of_subset_of_mem (ray_subset_line h) g

theorem seg_subset_line {s : Seg_nd P} {l : Line P} (h : s.toLine = l) : s.1.carrier ⊆ l.carrier := by
  intro A Ain
  rw [← h]
  apply seg_lies_on_Line Ain

theorem pt_pt_seg_toLine_eq_seg_toRay_toLine {A B : P} (h : B ≠ A) : (Ray.mk_pt_pt A B h).toLine = LIN A B h := by 
  rw [← pt_pt_seg_toRay_eq_pt_pt_ray]
  exact seg_toLine_eq_seg_toRay_toLine

theorem pt_pt_lies_on_iff_ray_toLine {A B : P} {l : Line P} (h : B ≠ A) : A LiesOn l ∧ B LiesOn l  ↔ (Ray.mk_pt_pt A B h).toLine = l := by 
  constructor
  · intro lAB
    let ⟨r, hr⟩ := l.exists_rep
    have rl : r.toLine = l := by apply hr
    have : ∀ (X : P), X LiesOn l ↔ X LiesOn r ∨ X LiesOn r.reverse  := by 
      intro X
      rw [← rl]
      apply Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev
    have : same_extn_line r (Ray.mk_pt_pt A B h) := by
      apply same_extn_line.pt_pt_ray_same_extn_line_of_pt_pt_lies_on_line h
      · exact (this A).mp lAB.1
      · exact (this B).mp lAB.2
    rw [← rl]
    apply Quotient.eq.mpr 
    exact same_extn_line.symm this
  · intro hl
    rw [← hl]
    constructor
    · exact Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mpr (Or.inl Ray.source_lies_on)
    · apply Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mpr
      left
      apply Ray.snd_pt_lies_on_mk_pt_pt

--**This theorem may be moved to section pt_pt with modifying this proof, perhaps merged with theorem eq_line_of_pt_pt_of_ne in Line.ex.
theorem eq_pt_pt_line_iff_lies_on {A B : P} {l : Line P} (h : B ≠ A) : A LiesOn l ∧ B LiesOn l  ↔ LIN A B h = l := by 
  constructor
  · have : LIN A B h = (Ray.mk_pt_pt A B h).toLine := by apply pt_pt_seg_toLine_eq_seg_toRay_toLine
    rw [this]
    exact (pt_pt_lies_on_iff_ray_toLine h).mp
  · intro lAB
    rw [← lAB]
    constructor
    · exact Line.fst_pt_lies_on_mk_pt_pt h
    · exact Line.snd_pt_lies_on_mk_pt_pt h

theorem pt_pt_lies_on_iff_seg_toLine {A B : P} {l : Line P} (h : B ≠ A) : A LiesOn l ∧ B LiesOn l  ↔ (Seg_nd.mk A B h).toLine = l := by 
  constructor
  · intro lAB
    rw [← seg_toLine_eq_seg_toRay_toLine]
    rw [pt_pt_seg_toRay_eq_pt_pt_ray h]
    exact (pt_pt_lies_on_iff_ray_toLine h).mp lAB
  · intro hl
    rw [← hl]
    constructor
    · exact seg_lies_on_Line Seg.source_lies_on 
    · exact seg_lies_on_Line Seg.target_lies_on
--**end coercion--



--**section colinear--
theorem linear {l : Line P} {A B C : P} (h₁ : A LiesOn l) (h₂ : B LiesOn l) (h₃ : C LiesOn l) : colinear A B C := by
  unfold Line at l
  revert l
  rw [Quotient.forall (p := fun k : Line P => A LiesOn k → B LiesOn k → C LiesOn k → colinear A B C)]
  unfold lies_on instCarrierLine Carrier.carrier Line.carrier at *
  simp only
  intro ray a b c
  rw [@Quotient.lift_mk _ _ same_extn_line.setoid _ _ _] at *
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      cases c with
      | inl c =>
        exact Ray.colinear_of_lies_on a b c
      | inr c =>
        let ray' := Ray.mk C ray.toDir
        have a' : A ∈ ray'.carrier := lies_on_pt_toDir_of_pt_lies_on_rev a c
        have b' : B ∈ ray'.carrier := lies_on_pt_toDir_of_pt_lies_on_rev b c
        exact Ray.colinear_of_lies_on a' b' (Ray.source_lies_on)
    | inr b =>
      cases c with
      | inl c => 
        let ray' := Ray.mk B ray.toDir
        have a' : A ∈ ray'.carrier := lies_on_pt_toDir_of_pt_lies_on_rev a b
        have c' : C ∈ ray'.carrier := lies_on_pt_toDir_of_pt_lies_on_rev c b
        exact Ray.colinear_of_lies_on a' (Ray.source_lies_on) c'
      | inr c => 
        let ray' := Ray.mk A ray.reverse.toDir
        have a' : A LiesOn ray.reverse.reverse := by
          rw [Ray.rev_rev_eq_self]
          exact a
        have b' : B ∈ ray'.carrier := lies_on_pt_toDir_of_pt_lies_on_rev b a'
        have c' : C ∈ ray'.carrier := lies_on_pt_toDir_of_pt_lies_on_rev c a'
        exact Ray.colinear_of_lies_on (Ray.source_lies_on) b' c'
  | inr a =>
    cases b with
    | inl b =>
      cases c with
      | inl c => 
        let ray' := Ray.mk A ray.toDir
        have b' : B ∈ ray'.carrier := lies_on_pt_toDir_of_pt_lies_on_rev b a
        have c' : C ∈ ray'.carrier := lies_on_pt_toDir_of_pt_lies_on_rev c a
        exact Ray.colinear_of_lies_on (Ray.source_lies_on) b' c'
      | inr c => 
        let ray' := Ray.mk B ray.reverse.toDir
        have b' : B LiesOn ray.reverse.reverse := by
          rw [Ray.rev_rev_eq_self]
          exact b
        have a' : A ∈ ray'.carrier := lies_on_pt_toDir_of_pt_lies_on_rev a b'
        have c' : C ∈ ray'.carrier := lies_on_pt_toDir_of_pt_lies_on_rev c b'
        exact Ray.colinear_of_lies_on a' (Ray.source_lies_on) c'
    | inr b =>
      cases c with
      | inl c => 
        let ray' := Ray.mk C ray.reverse.toDir
        have c' : C LiesOn ray.reverse.reverse := by
          rw [Ray.rev_rev_eq_self]
          exact c
        have a' : A ∈ ray'.carrier := lies_on_pt_toDir_of_pt_lies_on_rev a c'
        have b' : B ∈ ray'.carrier := lies_on_pt_toDir_of_pt_lies_on_rev b c'
        exact Ray.colinear_of_lies_on  a' b' (Ray.source_lies_on)
      | inr c => 
        exact Ray.colinear_of_lies_on a b c

theorem maximal' {l : Line P} {A B C : P} (h₁ : A LiesOn l) (h₂ : B LiesOn l) (h : B ≠ A) (Co : colinear A B C) : C LiesOn l := by 
  have : C LiesOn (Ray.mk_pt_pt A B h) ∨ C LiesOn (Ray.mk_pt_pt A B h).reverse := (lies_on_ray_or_rev_iff_colinear h).mp Co
  by_cases Cry : C LiesOn (Ray.mk_pt_pt A B h)
  · rw [← (pt_pt_lies_on_iff_ray_toLine h).mp ⟨h₁, h₂⟩] 
    apply Ray.subset_toLine
    exact Cry
  · rw [← (pt_pt_lies_on_iff_ray_toLine h).mp ⟨h₁, h₂⟩] 
    rw [ray_rev_toLine_eq_ray_toLine]
    apply Ray.subset_toLine
    tauto

theorem maximal {l : Line P} {A B C : P} (h₁ : A ∈ l.carrier) (h₂ : B ∈ l.carrier) (h : B ≠ A) (Co : colinear A B C) : C ∈ l.carrier := by 
  have hl : C LiesOn l := by
    apply maximal' _ _ h Co
    · exact Line.in_carrier_iff_lies_on.mpr h₁
    · exact Line.in_carrier_iff_lies_on.mpr h₂
  exact Line.in_carrier_iff_lies_on.mp hl

--**Things in section colinear in Line_ex should be put here since they may use theorems above.
 
--**end colinear--



--**section Archimedean_property--
theorem nontriv {l : Line P} : ∃ (A B : P), (A ∈ l.carrier) ∧ (B ∈ l.carrier) ∧ (B ≠ A) := by
  let ⟨r, h⟩ := l.exists_rep
  rcases r.nontriv with ⟨A, B, g⟩
  have : r.carrier ⊆ l.carrier := ray_subset_line h
  exact ⟨A, B, ⟨this g.1, this g.2.1, g.2.2⟩⟩
--**end Archimedean_property--

end Line

end coercion

end EuclidGeom