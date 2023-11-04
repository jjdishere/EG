import EuclideanGeometry.Foundation.Axiom.Linear.Colinear
import EuclideanGeometry.Foundation.Axiom.Linear.Ray
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex

noncomputable section
namespace EuclidGeom

section setoid

variable {P : Type _} [EuclideanPlane P]

def same_dir_line : Ray P → Ray P → Prop := fun r r' => r.toDir = r'.toDir ∧ (r'.source LiesOn r ∨ r'.source LiesOn r.reverse)

namespace same_dir_line

protected theorem refl (r : Ray P) : same_dir_line r r := ⟨rfl, .inl r.source_lies_on⟩

protected theorem symm {r r' : Ray P} : same_dir_line r r' → same_dir_line r' r := fun h => ⟨h.1.symm, sorry⟩

protected theorem trans {r r' r'' : Ray P} (h₁ : same_dir_line r r') (h₂ : same_dir_line r' r'') : same_dir_line r r'' := sorry

protected def setoid : Setoid (Ray P) where
  r := same_dir_line
  iseqv := {
    refl := same_dir_line.refl
    symm := same_dir_line.symm
    trans := same_dir_line.trans
  }

end same_dir_line

def same_extn_line : Ray P → Ray P → Prop := fun r r' => r.toProj = r'.toProj ∧ (r'.source LiesOn r ∨ r'.source LiesOn r.reverse)

namespace same_extn_line

theorem dir_eq_or_eq_neg {r r' : Ray P} (h : same_extn_line r r') : (r.toDir = r'.toDir ∨ r.toDir = - r'.toDir) :=
  (Dir.eq_toProj_iff r.toDir r'.toDir).mp h.1

theorem vec_parallel_of_same_extn_line {r r' : Ray P} (h : same_extn_line r r') : ∃ t : ℝ, r'.toDir.toVec = t • r.toDir.toVec :=
  Or.casesOn (dir_eq_or_eq_neg h) (fun rr' ↦ ⟨1, by rw [one_smul, rr']⟩)
    fun rr' ↦ ⟨- 1, by rw [rr', Dir.toVec_neg_eq_neg_toVec, smul_neg, neg_smul, one_smul, neg_neg]⟩

theorem ray_rev_of_same_extn_line {r : Ray P} : same_extn_line r r.reverse :=
  ⟨Ray.toProj_of_rev_eq_toProj.symm, .inr Ray.source_lies_on⟩

theorem pt_pt_ray_same_extn_line_of_pt_pt_lies_on_line {A B : P} {r : Ray P} (h : B ≠ A) (ha : A LiesOn r ∨ A LiesOn r.reverse) (hb : B LiesOn r ∨ B LiesOn r.reverse) : same_extn_line r (Ray.mk_pt_pt A B h) :=
  ⟨ray_toProj_eq_mk_pt_pt_toProj h ha hb, ha⟩

protected theorem refl (r : Ray P) : same_extn_line r r := ⟨rfl, .inl Ray.source_lies_on⟩

protected theorem symm {r r' : Ray P} (h : same_extn_line r r') : same_extn_line r' r := by
  refine' ⟨h.1.symm, pt_lies_on_line_from_ray_iff_vec_parallel.mpr _⟩
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h.2 with ⟨a, dxy⟩
  rcases dir_eq_or_eq_neg h with xy | xy
  · use -a
    rw [← neg_vec, dxy, ← neg_smul, xy]
  · use a
    rw [← neg_vec, dxy, xy, Dir.toVec_neg_eq_neg_toVec, smul_neg, Complex.real_smul, neg_neg]

protected theorem trans {r r' r'' : Ray P} (h₁ : same_extn_line r r') (h₂ : same_extn_line r' r'') : same_extn_line r r'' := by
  refine' ⟨h₁.1.trans h₂.1, pt_lies_on_line_from_ray_iff_vec_parallel.mpr _⟩
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h₁.2 with ⟨a, dr⟩
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h₂.2 with ⟨b, dr'⟩
  let ⟨t, rparr'⟩ := vec_parallel_of_same_extn_line h₁
  use a + b * t
  rw [← vec_add_vec, dr, dr', rparr']
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_add]
  ring

protected def setoid : Setoid (Ray P) where
  r := same_extn_line
  iseqv := {
    refl := same_extn_line.refl
    symm := same_extn_line.symm
    trans := same_extn_line.trans
  }

-- instance : Setoid (Ray P) := same_extn_line.setoid

end same_extn_line

theorem same_extn_line_of_PM (A : P) (x y : Dir) (h : PM x y) : same_extn_line (Ray.mk A x) (Ray.mk A y) :=
  ⟨by simp only [Ray.toProj, Dir.eq_toProj_iff', h], .inl Ray.source_lies_on⟩

theorem same_extn_line.subset_carrier_union_rev_carrier {r r' : Ray P} (h : same_extn_line r r') : r'.carrier ∪ r'.reverse.carrier ⊆ r.carrier ∪ r.reverse.carrier := by
  intro p hp
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h.2 with ⟨a, ha⟩
  rcases dir_parallel_of_same_proj h.1 with ⟨b, hb⟩
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp hp with ⟨c, hc⟩
  refine' pt_lies_on_line_from_ray_iff_vec_parallel.mpr ⟨a + c * b, _⟩
  rw [← vec_add_vec, ha, hc, hb, Complex.real_smul, Complex.real_smul, Complex.real_smul,
    ← mul_assoc, ← Complex.ofReal_mul]
  exact (add_smul a (c * b) r.toDir.toVec).symm

theorem same_extn_line.eq_carrier_union_rev_carrier (r r' : Ray P) (h : same_extn_line r r') : r.carrier ∪ r.reverse.carrier = r'.carrier ∪ r'.reverse.carrier :=
  Set.Subset.antisymm_iff.mpr ⟨h.symm.subset_carrier_union_rev_carrier, h.subset_carrier_union_rev_carrier⟩

-- relation between two setoids, same_dir_line implies same_extn_line
theorem same_dir_line_le_same_extn_line : same_dir_line.setoid (P := P) ≤ same_extn_line.setoid := fun _ _ h => ⟨congrArg (⟦·⟧) h.1 , h.2⟩

end setoid

def DirLine (P : Type _) [EuclideanPlane P] := Quotient (@same_dir_line.setoid P _)

def Line (P : Type _) [EuclideanPlane P] := Quotient (@same_extn_line.setoid P _)

variable {P : Type _} [EuclideanPlane P]

section make

namespace DirLine

-- define a directed line from 2 distinct points
def mk_pt_pt (A B : P) (h : B ≠ A) : DirLine P := Quotient.mk same_dir_line.setoid (RAY A B h)

-- define a directed line from a point and a direction
def mk_pt_dir (A : P) (dir : Dir) : DirLine P := Quotient.mk same_dir_line.setoid (Ray.mk A dir)

def mk_pt_vec_nd (A : P) (vec_nd : Vec_nd) : DirLine P := mk_pt_dir A vec_nd.toDir

end DirLine

namespace Line

-- define a line from two points
def mk_pt_pt (A B : P) (h : B ≠ A) : Line P := Quotient.mk same_extn_line.setoid (RAY A B h)

-- define a line from a point and a proj
def mk_pt_proj (A : P) (proj : Proj) : Line P := Quotient.map (sa := PM.con.toSetoid) (sb := same_extn_line.setoid) (fun x : Dir => Ray.mk A x) (same_extn_line_of_PM A) proj

-- define a line from a point and a direction
def mk_pt_dir (A : P) (dir : Dir) : Line P := mk_pt_proj A dir.toProj

-- define a line from a point and a nondegenerate vector
def mk_pt_vec_nd (A : P) (vec_nd : Vec_nd) : Line P := mk_pt_proj A vec_nd.toProj

end Line

scoped notation "LIN" => Line.mk_pt_pt

scoped notation "DLIN" => DirLine.mk_pt_pt

end make

section coercion

def Line.toProj (l : Line P) : Proj := Quotient.lift (s := same_extn_line.setoid) (fun ray : Ray P => ray.toProj) (fun _ _ h => And.left h) l

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

/-- A point lies on a line associated to a ray if and only if it lies on the ray or the reverse of the ray. -/
theorem Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev {A : P} {r : Ray P}: (A LiesOn r.toLine) ↔ (A LiesOn r) ∨ (A LiesOn r.reverse) := Iff.rfl

theorem Ray.in_carrier_toLine_iff_in_or_in_rev {r : Ray P} {A : P} : (A ∈ r.toLine.carrier) ↔ ((A ∈ r.carrier) ∨ (A ∈ r.reverse.carrier)) := Iff.rfl

theorem Line.in_carrier_iff_lies_on {l : Line P} {A : P} : A LiesOn l ↔ A ∈ l.carrier := Iff.rfl

end carrier



namespace Line

variable (A B : P) (h : B ≠ A) (ray : Ray P) (seg_nd : Seg_nd P)

section pt_pt

theorem line_of_pt_pt_eq_rev : LIN A B h = LIN B A h.symm :=
  (Quotient.eq (r := same_extn_line.setoid)).mpr ⟨Ray.toProj_eq_toProj_of_mk_pt_pt h, .inl (Ray.snd_pt_lies_on_mk_pt_pt h)⟩

theorem fst_pt_lies_on_mk_pt_pt {A B : P} (h : B ≠ A) : A LiesOn LIN A B h := .inl (Ray.source_lies_on)

theorem snd_pt_lies_on_mk_pt_pt {A B : P} (h : B ≠ A) : B LiesOn LIN A B h := by
  rw [line_of_pt_pt_eq_rev]
  exact fst_pt_lies_on_mk_pt_pt h.symm

-- The first point and the second point in Line.mk_pt_pt LiesOn the line it make.
theorem pt_lies_on_line_of_pt_pt_of_ne {A B : P} (h: B ≠ A) : A LiesOn LIN A B h ∧ B LiesOn LIN A B h :=
  ⟨fst_pt_lies_on_mk_pt_pt h, snd_pt_lies_on_mk_pt_pt h⟩

-- two point determines a line
theorem eq_line_of_pt_pt_of_ne {A B : P} {l : Line P} (h : B ≠ A) (ha : A LiesOn l) (hb : B LiesOn l) : LIN A B h = l := by
  revert l
  rintro ⟨r⟩ ha hb
  exact (Quotient.eq (r := same_extn_line.setoid)).mpr (same_extn_line.symm ⟨ray_toProj_eq_mk_pt_pt_toProj h ha hb, ha⟩)

-- If two lines have two distinct intersection points, then these two lines are identical.
theorem eq_of_pt_pt_lies_on_of_ne {A B : P} (h : B ≠ A) {l₁ l₂ : Line P} (hA₁ : A LiesOn l₁) (hB₁ : B LiesOn l₁) (hA₂ : A LiesOn l₂) (hB₂ : B LiesOn l₂) : l₁ = l₂ := by
  rw [← eq_line_of_pt_pt_of_ne h hA₁ hB₁]
  exact eq_line_of_pt_pt_of_ne h hA₂ hB₂

--**This theorem may be moved to section pt_pt with modifying this proof, perhaps merged with theorem eq_line_of_pt_pt_of_ne in Line.ex.
theorem eq_pt_pt_line_iff_lies_on {A B : P} {l : Line P} (h : B ≠ A) : A LiesOn l ∧ B LiesOn l ↔ LIN A B h = l := by
  refine' ⟨fun ⟨ha, hb⟩ ↦ eq_line_of_pt_pt_of_ne h ha hb, fun lAB ↦ _⟩
  rw [← lAB]
  exact pt_lies_on_line_of_pt_pt_of_ne h

theorem pt_pt_lies_on_iff_ray_toLine {A B : P} {l : Line P} (h : B ≠ A) : A LiesOn l ∧ B LiesOn l  ↔ (RAY A B h).toLine = l := eq_pt_pt_line_iff_lies_on h

theorem pt_pt_lies_on_iff_seg_toLine {A B : P} {l : Line P} (h : B ≠ A) : A LiesOn l ∧ B LiesOn l  ↔ (SEG_nd A B h).toLine = l := eq_pt_pt_line_iff_lies_on h

theorem toProj_eq_seg_nd_toProj_of_lies_on {A B : P} {l : Line P} (ha : A LiesOn l) (hb : B LiesOn l) (hab : B ≠ A) : Seg_nd.toProj ⟨SEG A B, hab⟩ = l.toProj := by
  rw [← eq_line_of_pt_pt_of_ne hab ha hb]
  rfl

end pt_pt


--**We can put "section pt_proj of Line_ex" here.
section pt_proj

theorem pt_lies_on_of_mk_pt_proj (proj : Proj) : A LiesOn Line.mk_pt_proj A proj := by
  rw [← @Quotient.out_eq _ PM.con.toSetoid proj]
  exact Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mpr (.inl Ray.source_lies_on)

theorem pt_lies_on_of_mk_pt_dir (dir : Dir) : A LiesOn Line.mk_pt_dir A dir :=
  pt_lies_on_of_mk_pt_proj A dir.toProj

theorem pt_lies_on_of_mk_pt_vec_nd (vec_nd : Vec_nd) : A LiesOn Line.mk_pt_vec_nd A vec_nd :=
  pt_lies_on_of_mk_pt_proj A vec_nd.toProj

theorem proj_eq_of_mk_pt_proj (proj : Proj) : (Line.mk_pt_proj A proj).toProj = proj := by
  rw [← @Quotient.out_eq _ PM.con.toSetoid proj]
  rfl

theorem mk_pt_proj_eq {A : P} {l : Line P} (h : A LiesOn l) : Line.mk_pt_proj A l.toProj = l := by
  revert l
  rintro ⟨r⟩ h
  exact (@Quotient.map_mk _ _ PM.con.toSetoid same_extn_line.setoid (fun x : _ ↦ Ray.mk A x)
    (same_extn_line_of_PM A) r.2).trans <|
      (@Quotient.eq (r := same_extn_line.setoid)).mpr (same_extn_line.symm ⟨rfl, h⟩)

theorem mk_pt_proj_eq_of_eq_toProj {A : P} {l : Line P} (h : A LiesOn l) {x : Proj}
    (hx : x = l.toProj) : Line.mk_pt_proj A x = l := by
  rw [hx]
  exact mk_pt_proj_eq h

theorem eq_of_same_toProj_and_pt_lies_on {A : P} {l₁ l₂: Line P} (h₁ : A LiesOn l₁) (h₂ : A LiesOn l₂) (h : l₁.toProj = l₂.toProj) : l₁ = l₂ := by
  rw [← mk_pt_proj_eq h₁, mk_pt_proj_eq_of_eq_toProj h₂ h]

theorem exsit_line_pt_lies_on : ∃ l : Line P, A LiesOn l :=
  ⟨Line.mk_pt_vec_nd A ⟨1, one_ne_zero⟩, pt_lies_on_of_mk_pt_vec_nd A ⟨1, one_ne_zero⟩⟩

end pt_proj

end Line



open Line Classical

--**section coercion--
section coercion

variable (r : Ray P) (s : Seg_nd P)

theorem Ray.toLine_eq_rev_toLine : r.toLine = r.reverse.toLine :=
  (Quotient.eq (r := same_extn_line.setoid)).mpr same_extn_line.ray_rev_of_same_extn_line

theorem Seg_nd.toLine_eq_toRay_toLine : s.toRay.toLine = s.toLine := rfl

theorem Seg_nd.toLine_eq_rev_toLine : s.toLine = s.reverse.toLine :=
  line_of_pt_pt_eq_rev s.1.source s.1.target s.2

theorem Seg_nd.toLine_eq_extn_toLine : s.toLine = s.extension.toLine :=
  (Quotient.eq (r := same_extn_line.setoid)).mpr ⟨by
  show s.toProj = s.reverse.toRay.reverse.toProj
  rw [Ray.toProj_of_rev_eq_toProj, Seg_nd.toRay_toProj_eq_toProj, Seg_nd.toProj_of_rev_eq_toProj],
  .inl (Seg_nd.lies_on_toRay_of_lies_on Seg.target_lies_on)⟩

theorem ray_of_pt_pt_toLine_eq_line_of_pt_pt {A B : P} (h : B ≠ A) : (RAY A B h).toLine = LIN A B h := rfl

theorem seg_nd_of_pt_pt_toLine_eq_line_of_pt_pt {A B : P} (h : B ≠ A) : Seg_nd.toLine ⟨SEG A B, h⟩ = LIN A B h := rfl

end coercion

section lieson

variable (r : Ray P) (s : Seg_nd P)

theorem Ray.subset_toLine : r.carrier ⊆ r.toLine.carrier := by
  rw [toLine_carrier_eq_ray_carrier_union_rev_carrier]
  exact Set.subset_union_left r.carrier r.reverse.carrier

theorem ray_subset_line {r : Ray P} {l : Line P} (h : r.toLine = l) : r.carrier ⊆ l.carrier := by
  rw [← h]
  exact r.subset_toLine

theorem seg_lies_on_line {s : Seg_nd P} {A : P} (h : A LiesOn s.1) : A LiesOn s.toLine :=
  Set.mem_of_subset_of_mem (ray_subset_line rfl) (Seg_nd.lies_on_toRay_of_lies_on h)

theorem Seg_nd.subset_toLine : s.1.carrier ⊆ s.toLine.carrier := fun _ h ↦ seg_lies_on_line h

theorem seg_subset_line {s : Seg_nd P} {l : Line P} (h : s.toLine = l) : s.1.carrier ⊆ l.carrier := by
  rw [← h]
  exact s.subset_toLine

theorem Line.nontriv (l : Line P) : ∃ (A B : P), A LiesOn l ∧ B LiesOn l ∧ (B ≠ A) := by
  let ⟨r, h⟩ := l.exists_rep
  rcases r.nontriv with ⟨A, B, g⟩
  exact ⟨A, B, ⟨ray_subset_line h g.1, ray_subset_line h g.2.1, g.2.2⟩⟩

-- If a point lies on a ray, then it lies on the line associated to the ray.
theorem Ray.lies_on_toLine_of_lie_on {A : P} {r : Ray P} (h : A LiesOn r) : A LiesOn r.toLine := .inl h

theorem Seg_nd.lies_on_toLine_of_lie_on {A : P} {s : Seg_nd P} (h : A LiesOn s.1) : A LiesOn s.toLine :=
  .inl (lies_on_toRay_of_lies_on h)

theorem Ray.source_lies_on_toLine : r.source LiesOn r.toLine :=
  r.lies_on_toLine_of_lie_on r.source_lies_on

theorem Seg_nd.source_lies_on_toLine : s.1.source LiesOn s.toLine :=
  s.toRay.source_lies_on_toLine

theorem Seg_nd.target_lies_on_toLine : s.1.target LiesOn s.toLine :=
  s.lies_on_toLine_of_lie_on s.1.target_lies_on

theorem Ray.lies_on_ray_or_lies_on_ray_rev_iff {A : P} {r : Ray P} : A LiesOn r ∧ A ≠ r.source ∨ A LiesOn r.reverse ∧ A ≠ r.source ∨ A = r.source ↔ A LiesOn r ∨ A LiesOn r.reverse := ⟨
  fun | .inl h => .inl h.1
      | .inr h => .casesOn h (fun h => .inr h.1) (fun h => .inr (by rw[h]; exact source_lies_on)),
  fun | .inl h => if g : A = source then .inr (.inr g) else .inl ⟨h, g⟩
      | .inr h => if g : A = source then .inr (.inr g) else .inr (.inl ⟨h, g⟩)⟩

theorem Ray.lies_on_toLine_iff_lies_int_or_lies_int_rev_or_eq_source {A : P} {r : Ray P} : (A LiesOn r.toLine) ↔ (A LiesInt r) ∨ (A LiesInt r.reverse) ∨ (A = r.source) := by
  rw [lies_int_def, lies_int_def, source_of_rev_eq_source, lies_on_ray_or_lies_on_ray_rev_iff, lies_on_toLine_iff_lies_on_or_lies_on_rev]

theorem Seg_nd.lies_on_extn_or_rev_extn_iff_lies_on_toLine_of_not_lies_on {A : P} {seg_nd : Seg_nd P} (h : ¬ A LiesInt seg_nd.1) : A LiesOn seg_nd.toLine ↔ (A LiesOn seg_nd.extension) ∨ (A LiesOn seg_nd.reverse.extension) := by
  constructor
  · intro hh
    rcases Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mp hh with h₁ | h₂
    · by_cases ax : A = seg_nd.1.source
      · rw [ax]
        exact .inr Ray.source_lies_on
      by_cases ay : A = seg_nd.1.target
      · rw [ay]
        exact .inl Ray.source_lies_on
      exact .casesOn (lies_on_seg_nd_or_extension_of_lies_on_toRay h₁)
        (fun h₁ ↦ (h ⟨h₁, ax, ay⟩).elim) (fun h₁ ↦ .inl h₁)
    exact .inr h₂
  · exact fun hh ↦ .casesOn hh
      (fun h₁ ↦ Eq.mpr (seg_nd.toLine_eq_extn_toLine ▸ Eq.refl (A LiesOn seg_nd.toLine))
        ((seg_nd.extension.lies_on_toLine_iff_lies_on_or_lies_on_rev).mpr (.inl h₁)))
      (fun h₂ ↦ (seg_nd.toRay.lies_on_toLine_iff_lies_on_or_lies_on_rev).mpr (.inr h₂))

theorem Seg_nd.lies_on_toline_of_lies_on_extn {X : P} {seg_nd : Seg_nd P} (lieson : X LiesOn seg_nd.extension) : X LiesOn seg_nd.toLine := by
  rw [Seg_nd.toLine_eq_rev_toLine]
  exact Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mpr (.inr lieson)

-- Two lines are equal iff they have the same carrier.
theorem lies_on_iff_lies_on_iff_line_eq_line (l₁ l₂ : Line P) : (∀ A : P, A LiesOn l₁ ↔ A LiesOn l₂) ↔ l₁ = l₂ := by
  constructor
  · revert l₁ l₂
    rintro ⟨r₁⟩ ⟨r₂⟩ h
    rcases r₁.toLine.nontriv with ⟨X, Y, Xrl₁, Yrl₁, neq⟩
    exact eq_of_pt_pt_lies_on_of_ne neq Xrl₁ Yrl₁ ((h X).mp Xrl₁) ((h Y).mp Yrl₁)
  · exact fun h A ↦ Iff.of_eq (congrArg (lies_on A) h)

theorem Line.lies_on_iff_eq_toProj_of_lies_on {A B : P} {l : Line P} (h : B ≠ A) (hA : A LiesOn l) : B LiesOn l ↔ (SEG_nd A B h).toProj = l.toProj := by
  refine' ⟨fun hB ↦ toProj_eq_seg_nd_toProj_of_lies_on hA hB h, fun eq ↦ _⟩
  rw [← eq_of_same_toProj_and_pt_lies_on (Seg_nd.lies_on_toLine_of_lie_on (@Seg.source_lies_on _ _ (SEG_nd A B h).1)) hA eq]
  exact Seg_nd.lies_on_toLine_of_lie_on Seg.target_lies_on

end lieson
--**end coercion--



namespace Line

--**section colinear--
section colinear

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
    rw [Ray.toLine_eq_rev_toLine]
    apply Ray.subset_toLine
    tauto

theorem maximal {l : Line P} {A B C : P} (h₁ : A ∈ l.carrier) (h₂ : B ∈ l.carrier) (h : B ≠ A) (Co : colinear A B C) : C ∈ l.carrier := by
  have hl : C LiesOn l := by
    apply maximal' _ _ h Co
    · exact Line.in_carrier_iff_lies_on.mpr h₁
    · exact Line.in_carrier_iff_lies_on.mpr h₂
  exact Line.in_carrier_iff_lies_on.mp hl

theorem lies_on_line_of_pt_pt_iff_colinear {A B : P} (h : B ≠ A) (X : P) : (X LiesOn (LIN A B h)) ↔ colinear A B X :=
  ⟨fun hx ↦ (LIN A B h).linear (fst_pt_lies_on_mk_pt_pt h) (snd_pt_lies_on_mk_pt_pt h) hx,
  fun c ↦ (LIN A B h).maximal (fst_pt_lies_on_mk_pt_pt h) (snd_pt_lies_on_mk_pt_pt h) h c⟩

-- This is also a typical proof that shows how to use linear, maximal, nontriv of a line. Please write it shorter in future.

theorem lies_on_iff_colinear_of_ne_lies_on_lies_on {A B : P} {l : Line P} (h : B ≠ A) (ha : A LiesOn l) (hb : B LiesOn l) (C : P) : (C LiesOn l) ↔ colinear A B C :=
  ⟨fun hc ↦ l.linear ha hb hc, fun c ↦ l.maximal ha hb h c⟩

theorem colinear_iff_exist_line_lies_on (A B C : P) : colinear A B C ↔ ∃ l : Line P, (A LiesOn l) ∧ (B LiesOn l) ∧ (C LiesOn l) := by
  constructor
  · intro c
    by_cases h : B ≠ A
    · exact ⟨(LIN A B h), fst_pt_lies_on_mk_pt_pt h, snd_pt_lies_on_mk_pt_pt h,
        (lies_on_line_of_pt_pt_iff_colinear h C).mpr c⟩
    rw [ne_eq, not_not] at h
    by_cases hh : C ≠ B
    · use LIN B C hh
      rw [← h, and_self_left]
      exact ⟨fst_pt_lies_on_mk_pt_pt hh, snd_pt_lies_on_mk_pt_pt hh⟩
    rw [ne_eq, not_not] at hh
    simp only [hh, h, and_self, exsit_line_pt_lies_on A]
  · intro ⟨l, ha, hb, hc⟩
    if h : B = A then simp only [h, colinear, or_true, dite_true]
    else exact (lies_on_iff_colinear_of_ne_lies_on_lies_on h ha hb C).mp hc

end colinear
--**end colinear--



--**section Archimedean_property--
section Archimedean_property

-- there are two distinct points on a line
theorem exists_ne_pt_pt_lies_on_of_line (A : P) (l : Line P) : ∃ B : P, B LiesOn l ∧ B ≠ A := by
  rcases l.nontriv with ⟨X, Y, hx, hy, ne⟩
  exact if h : A = X then ⟨Y, hy, ne.trans_eq h.symm⟩ else ⟨X, hx, ne_comm.mp h⟩

theorem lies_on_of_Seg_nd_toProj_eq_toProj {A B : P} {l : Line P} (ha : A LiesOn l) (hab : B ≠ A) (hp : Seg_nd.toProj ⟨SEG A B, hab⟩ = l.toProj) : B LiesOn l :=
  (lies_on_iff_eq_toProj_of_lies_on hab ha).mpr hp

theorem vec_vadd_pt_lies_on_line {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) (h : B ≠ A) : (VEC A B) +ᵥ B LiesOn l := by
  rw [← eq_line_of_pt_pt_of_ne h hA hB]
  refine' Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mpr
    (.inl ⟨2 * ‖VEC A B‖, mul_nonneg zero_le_two (norm_nonneg (VEC A B)), _⟩)
  have eq : VEC A (VEC A B +ᵥ B) = 2 * (VEC A B) := (vadd_vsub_assoc _ B A).trans (two_mul _).symm
  simp only [Ray.mk_pt_pt, eq, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat,
    mul_assoc, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
  exact (Vec_nd.norm_smul_to_dir_eq_self ⟨VEC A B, (ne_iff_vec_ne_zero A B).1 h⟩).symm

theorem Line.exist_pt_beyond_pt_right {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) (h : B ≠ A) : ∃ C : P, C LiesOn l ∧ B LiesInt (SEG A C) :=
  ⟨VEC A B +ᵥ B, vec_vadd_pt_lies_on_line hA hB h, (SEG_nd A B h).target_lies_int_seg_source_vec_vadd_target⟩

theorem Line.exist_pt_beyond_pt_left {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) (h : B ≠ A) : ∃ C : P, C LiesOn l ∧ A LiesInt (SEG C B) := by
  rcases exist_pt_beyond_pt_right hB hA h.symm with ⟨C, cl, acb⟩
  exact ⟨C, cl, Seg.lies_int_iff_lies_int_rev.mp acb⟩

end Archimedean_property
--**end Archimedean_property--

end Line

end coercion

end EuclidGeom
