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

protected theorem symm {r r' : Ray P} (h : same_dir_line r r') : same_dir_line r' r := by
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h.2 with ⟨a, dxy⟩
  refine' ⟨h.1.symm, pt_lies_on_line_from_ray_iff_vec_parallel.mpr ⟨- a, _⟩⟩
  rw [← neg_vec, dxy, neg_smul, neg_inj, Complex.real_smul]
  exact mul_eq_mul_left_iff.mpr (.inl (congrArg @Dir.toVec h.1))

protected theorem trans {r r' r'' : Ray P} (h₁ : same_dir_line r r') (h₂ : same_dir_line r' r'') : same_dir_line r r'' := by
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h₁.2 with ⟨a, dr⟩
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h₂.2 with ⟨b, dr'⟩
  refine' ⟨h₁.1.trans h₂.1, pt_lies_on_line_from_ray_iff_vec_parallel.mpr ⟨a + b, _⟩⟩
  rw [← vec_add_vec, dr, dr', ← h₁.1]
  exact (add_smul a b _).symm

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
  (Dir.eq_toproj_iff r.toDir r'.toDir).mp h.1

theorem vec_parallel_of_same_extn_line {r r' : Ray P} (h : same_extn_line r r') : ∃ t : ℝ, r'.toDir.toVec = t • r.toDir.toVec :=
  Or.casesOn (dir_eq_or_eq_neg h) (fun rr' ↦ ⟨1, by rw [one_smul, rr']⟩)
    fun rr' ↦ ⟨- 1, by rw [rr', Dir.tovec_neg_eq_neg_tovec, smul_neg, neg_smul, one_smul, neg_neg]⟩

theorem ray_rev_of_same_extn_line {r : Ray P} : same_extn_line r r.reverse :=
  ⟨Ray.toproj_of_rev_eq_toproj.symm, .inr Ray.source_lies_on⟩

theorem pt_pt_ray_same_extn_line_of_pt_pt_lies_on_line {A B : P} {r : Ray P} (h : B ≠ A) (ha : A LiesOn r ∨ A LiesOn r.reverse) (hb : B LiesOn r ∨ B LiesOn r.reverse) : same_extn_line r (Ray.mk_pt_pt A B h) :=
  ⟨ray_toproj_eq_mk_pt_pt_toproj h ha hb, ha⟩

protected theorem refl (r : Ray P) : same_extn_line r r := ⟨rfl, .inl Ray.source_lies_on⟩

protected theorem symm {r r' : Ray P} (h : same_extn_line r r') : same_extn_line r' r := by
  refine' ⟨h.1.symm, pt_lies_on_line_from_ray_iff_vec_parallel.mpr _⟩
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h.2 with ⟨a, dxy⟩
  rcases dir_eq_or_eq_neg h with xy | xy
  · use -a
    rw [← neg_vec, dxy, ← neg_smul, xy]
  · use a
    rw [← neg_vec, dxy, xy, Dir.tovec_neg_eq_neg_tovec, smul_neg, Complex.real_smul, neg_neg]

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
  ⟨by simp only [Ray.toProj, Dir.eq_toproj_iff', h], .inl Ray.source_lies_on⟩

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

def DirLine.toDir (l : DirLine P) : Dir := Quotient.lift (s := same_dir_line.setoid) (fun ray => ray.toDir) (fun _ _ h => h.left) l

def DirLine.toProj (l : DirLine P) : Proj := l.toDir.toProj

def DirLine.toLine (l : DirLine P) : Line P := Quotient.lift (⟦·⟧) (fun _ _ h => Quotient.sound $ same_dir_line_le_same_extn_line h) l

def Ray.toDirLine (ray : Ray P) : DirLine P := ⟦ray⟧

def Seg_nd.toDirLine (seg_nd : Seg_nd P) : DirLine P := seg_nd.toRay.toDirLine

def Line.toProj (l : Line P) : Proj := Quotient.lift (s := same_extn_line.setoid) (fun ray : Ray P => ray.toProj) (fun _ _ h => h.left) l

def Ray.toLine (ray : Ray P) : Line P := ⟦ray⟧

def Seg_nd.toLine (seg_nd : Seg_nd P) : Line P := ⟦seg_nd.toRay⟧

end coercion

section coercion_compatibility

theorem DirLine.toline_toproj_eq_toproj (l : DirLine P) : l.toLine.toProj = l.toProj := Quotient.ind (motive := fun l => Line.toProj (toLine l) = toProj l) (fun _ => rfl) l

theorem Ray.toline_eq_todirline_toline (ray : Ray P) : ray.toLine = ray.toDirLine.toLine := rfl

instance : Coe (Ray P) (DirLine P) where
  coe := Ray.toDirLine

instance : Coe (DirLine P) (Line P) where
  coe := DirLine.toLine

instance : Coe (Ray P) (Line P) where
  coe := Ray.toLine

end coercion_compatibility

/-
section ClassDirFig

variable (P : Type _) [EuclideanPlane P]

class DirFig (α : Type*) where
  toDirLine : α → DirLine P

instance DirLine.instDirFig : DirFig P (DirLine P) where
  toDirLine l := l

instance Ray.instDirFig : DirFig P (Ray P) where
  toDirLine := Quotient.mk (@same_dir_line.setoid P _)

instance Seg_nd.instDirFig : DirFig P (Seg_nd P) where
  toDirLine s := Quotient.mk (@same_dir_line.setoid P _) s.toRay

section DirFig

variable {P : Type _} [EuclideanPlane P] {α : Type _} [DirFig P α] (l : α)

def toDir : Dir := (@DirFig.toDirLine P _ _ _ l).toDir

def toProj : Proj := (@DirFig.toDirLine P _ _ _ l).toDir.toProj

def toLine : Line P := (@DirFig.toDirLine P _ _ _ l).toLine

-- And other definitions, such as IsLeft, IsRight, OnLine, odist, sign, and so on.

end DirFig

end ClassDirFig
-/

open Classical

section carrier

namespace Line

protected def carrier (l : Line P) : Set P := Quotient.lift (fun ray : Ray P => ray.carrier ∪ ray.reverse.carrier) (same_extn_line.eq_carrier_union_rev_carrier) l

/- Def of point lies on a line, LiesInt is not defined -/
protected def IsOn (A : P) (l : Line P) : Prop :=
  A ∈ l.carrier

instance : Fig Line where
  carrier := Line.carrier

end Line

namespace DirLine

protected def carrier (l : DirLine P) : Set P := l.toLine.carrier

instance : Fig DirLine where
  carrier := DirLine.carrier

end DirLine

theorem Ray.toline_carrier_eq_ray_carrier_union_rev_carrier (r : Ray P) : r.toLine.carrier = r.carrier ∪ r.reverse.carrier := rfl

variable {A : P} {r : Ray P} {s : Seg_nd P}

/-- A point lies on a line associated to a ray if and only if it lies on the ray or the reverse of the ray. -/
theorem Ray.lies_on_toline_iff_lies_on_or_lies_on_rev : (A LiesOn r.toLine) ↔ (A LiesOn r) ∨ (A LiesOn r.reverse) := Iff.rfl

theorem Ray.lies_on_todirline_iff_lies_on_or_lies_on_rev : (A LiesOn r.toDirLine) ↔ (A LiesOn r) ∨ (A LiesOn r.reverse) := Iff.rfl

theorem DirLine.lies_on_iff_lies_on_toline {l : DirLine P} : (A LiesOn l.toLine) ↔ (A LiesOn l) := Iff.rfl

-- add lies on ray implies lies on ray.toLine, ray.toDirLine. Similar for seg_nd

-- If a point lies on a ray, then it lies on the line associated to the ray.
theorem Ray.lies_on_toline_of_lie_on (h : A LiesOn r) : A LiesOn r.toLine := .inl h

theorem Seg_nd.lies_on_toline_of_lie_on (h : A LiesOn s.1) : A LiesOn s.toLine :=
  .inl (lies_on_toray_of_lies_on h)

theorem Ray.source_lies_on_toline : r.source LiesOn r.toLine :=
  r.lies_on_toline_of_lie_on r.source_lies_on

theorem Seg_nd.source_lies_on_toline : s.1.source LiesOn s.toLine :=
  s.toRay.source_lies_on_toline

theorem Seg_nd.target_lies_on_toline : s.1.target LiesOn s.toLine :=
  s.lies_on_toline_of_lie_on s.1.target_lies_on

-- If a point lies on a ray, then it lies on the directed line associated to the ray.
theorem Ray.lies_on_todirLine_of_lie_on (h : A LiesOn r) : A LiesOn r.toDirLine := .inl h

theorem Seg_nd.lies_on_todirLine_of_lie_on (h : A LiesOn s.1) : A LiesOn s.toDirLine :=
  .inl (lies_on_toray_of_lies_on h)

theorem Ray.source_lies_on_todirLine : r.source LiesOn r.toDirLine :=
  r.lies_on_toline_of_lie_on r.source_lies_on

theorem Seg_nd.source_lies_on_todirLine : s.1.source LiesOn s.toDirLine :=
  s.toRay.source_lies_on_toline

theorem Seg_nd.target_lies_on_todirLine : s.1.target LiesOn s.toDirLine :=
  s.lies_on_toline_of_lie_on s.1.target_lies_on

end carrier

section dirline_toray

-- the assumption h is for properties, not for construction
-- this def have to appear after carrier is defined
def Ray.mk_pt_dirline (A : P) (l : DirLine P) (h : A LiesOn l) : Ray P := Ray.mk A l.toDir

theorem ray_of_pt_dirline_todirline_eq_dirline (A : P) (l : DirLine P) (h : A LiesOn l) : (Ray.mk_pt_dirline A l h).toDirLine = l := by
  revert l
  apply Quotient.ind
  intro r h
  exact Quotient.sound' $ same_dir_line.symm ⟨rfl, h⟩

theorem ray_of_pt_dirline_todirline_todir_eq_dirline_todir (A : P) (l : DirLine P) (h : A LiesOn l) : (Ray.mk_pt_dirline A l h).toDir = l.toDir := rfl

end dirline_toray

section reverse

def DirLine.reverse (l : DirLine P) : DirLine P := by
  refine' Quotient.lift (⟦·.reverse⟧) (fun a b h ↦ _) l
  exact (@Quotient.eq _ same_dir_line.setoid _ _).mpr ⟨neg_inj.mpr h.left, Ray.lies_on_or_lies_on_rev_iff.mp h.2⟩

theorem DirLine.rev_todir_eq_neg_todir (l : DirLine P) : l.reverse.toDir = - l.toDir := by
  revert l
  rintro ⟨r⟩
  rfl

theorem DirLine.rev_rev_eq_self (l : DirLine P) : l.reverse.reverse = l := by
  revert l
  rintro ⟨r⟩
  exact congrArg (@Quotient.mk _ same_dir_line.setoid) r.rev_rev_eq_self

theorem DirLine.lies_on_rev_iff_lies_on {A : P} {l : DirLine P} : A LiesOn l.reverse ↔ A LiesOn l := by
  revert l
  rintro ⟨r⟩
  exact Ray.lies_on_or_lies_on_rev_iff.symm

end reverse

section line_dirline_compatibility

namespace DirLine

variable (l : DirLine P) {l₁ l₂ : DirLine P}

theorem rev_toline_eq_toline : l.reverse.toLine = l.toLine := by
  revert l
  rintro ⟨r⟩
  exact (@Quotient.eq _ same_extn_line.setoid _ _).mpr same_extn_line.ray_rev_of_same_extn_line.symm

theorem eq_of_todir_eq_of_toline_eq (h : l₁.toLine = l₂.toLine) (hd : l₁.toDir = l₂.toDir) : l₁ = l₂ := by
  revert l₁ l₂
  rintro ⟨r₁⟩ ⟨r₂⟩ h hd
  exact (@Quotient.eq _ same_dir_line.setoid _ _).mpr ⟨hd, ((@Quotient.eq _ same_extn_line.setoid _ _).mp h).2⟩

theorem eq_rev_of_todir_eq_neg_of_toline_eq (h : l₁.toLine = l₂.toLine) (hd : l₁.toDir = - l₂.toDir) : l₁ = l₂.reverse := by
  revert l₁ l₂
  rintro ⟨r₁⟩ ⟨r₂⟩ h hd
  exact (@Quotient.eq _ same_dir_line.setoid _ _).mpr ⟨hd, ((@Quotient.eq _ same_extn_line.setoid _ _).mp h).2⟩

theorem eq_rev_of_todir_ne_of_toline_eq (h : l₁.toLine = l₂.toLine) (hd : l₁.toDir ≠ l₂.toDir) : l₁ = l₂.reverse :=
  have hp : l₁.toProj = l₂.toProj := by rw [← l₁.toline_toproj_eq_toproj, h, l₂.toline_toproj_eq_toproj]
  eq_rev_of_todir_eq_neg_of_toline_eq h (((Dir.eq_toproj_iff _ _).mp hp).resolve_left hd)

theorem eq_or_eq_rev_of_toline_eq (h : l₁.toLine = l₂.toLine) : l₁ = l₂ ∨ l₁ = l₂.reverse :=
  if hd : l₁.toDir = l₂.toDir then .inl (eq_of_todir_eq_of_toline_eq h hd)
  else .inr (eq_rev_of_todir_ne_of_toline_eq h hd)

end DirLine

end line_dirline_compatibility

namespace Line

variable (A B : P) (h : B ≠ A) (ray : Ray P) (seg_nd : Seg_nd P)

section pt_pt

theorem line_of_pt_pt_eq_rev : LIN A B h = LIN B A h.symm :=
  (Quotient.eq (r := same_extn_line.setoid)).mpr ⟨Ray.toproj_eq_toproj_of_mk_pt_pt h, .inl (Ray.snd_pt_lies_on_mk_pt_pt h)⟩

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
  exact (Quotient.eq (r := same_extn_line.setoid)).mpr (same_extn_line.symm ⟨ray_toproj_eq_mk_pt_pt_toproj h ha hb, ha⟩)

-- If two lines have two distinct intersection points, then these two lines are identical.
theorem eq_of_pt_pt_lies_on_of_ne {A B : P} (h : B ≠ A) {l₁ l₂ : Line P} (hA₁ : A LiesOn l₁) (hB₁ : B LiesOn l₁) (hA₂ : A LiesOn l₂) (hB₂ : B LiesOn l₂) : l₁ = l₂ := by
  rw [← eq_line_of_pt_pt_of_ne h hA₁ hB₁]
  exact eq_line_of_pt_pt_of_ne h hA₂ hB₂

theorem eq_pt_pt_line_iff_lies_on {A B : P} {l : Line P} (h : B ≠ A) : A LiesOn l ∧ B LiesOn l ↔ LIN A B h = l := by
  refine' ⟨fun ⟨ha, hb⟩ ↦ eq_line_of_pt_pt_of_ne h ha hb, fun lAB ↦ _⟩
  rw [← lAB]
  exact pt_lies_on_line_of_pt_pt_of_ne h

theorem pt_pt_lies_on_iff_ray_toline {A B : P} {l : Line P} (h : B ≠ A) : A LiesOn l ∧ B LiesOn l ↔ (RAY A B h).toLine = l :=
  eq_pt_pt_line_iff_lies_on h

theorem pt_pt_lies_on_iff_seg_toline {A B : P} {l : Line P} (h : B ≠ A) : A LiesOn l ∧ B LiesOn l ↔ (SEG_nd A B h).toLine = l :=
  eq_pt_pt_line_iff_lies_on h

theorem toproj_eq_seg_nd_toproj_of_lies_on {A B : P} {l : Line P} (ha : A LiesOn l) (hb : B LiesOn l) (hab : B ≠ A) : (SEG_nd A B hab).toProj = l.toProj := by
  rw [← eq_line_of_pt_pt_of_ne hab ha hb]
  rfl

end pt_pt

section pt_proj

theorem pt_lies_on_of_mk_pt_proj (proj : Proj) : A LiesOn Line.mk_pt_proj A proj := by
  rw [← @Quotient.out_eq _ PM.con.toSetoid proj]
  exact Ray.lies_on_toline_iff_lies_on_or_lies_on_rev.mpr (.inl Ray.source_lies_on)

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

theorem mk_pt_proj_eq_of_eq_toproj {A : P} {l : Line P} (h : A LiesOn l) {x : Proj} (hx : x = l.toProj) : Line.mk_pt_proj A x = l := by
  rw [hx]
  exact mk_pt_proj_eq h

theorem eq_of_same_toproj_and_pt_lies_on {A : P} {l₁ l₂ : Line P} (h₁ : A LiesOn l₁) (h₂ : A LiesOn l₂) (h : l₁.toProj = l₂.toProj) : l₁ = l₂ := by
  rw [← mk_pt_proj_eq h₁, mk_pt_proj_eq_of_eq_toproj h₂ h]

theorem exsit_line_pt_lies_on : ∃ l : Line P, A LiesOn l :=
  ⟨Line.mk_pt_vec_nd A ⟨1, one_ne_zero⟩, pt_lies_on_of_mk_pt_vec_nd A ⟨1, one_ne_zero⟩⟩

end pt_proj

end Line

section pt_dir

namespace DirLine

variable (A B : P) (h : B ≠ A) (ray : Ray P) (seg_nd : Seg_nd P)

theorem pt_pt_rev_eq_rev : DLIN B A h.symm = (DLIN A B h).reverse := sorry

theorem fst_pt_lies_on_mk_pt_pt {A B : P} (h : B ≠ A) : A LiesOn DLIN A B h := .inl (Ray.source_lies_on)

theorem snd_pt_lies_on_mk_pt_pt {A B : P} (h : B ≠ A) : B LiesOn DLIN A B h := Line.snd_pt_lies_on_mk_pt_pt h

-- The first point and the second point in DirLine.mk_pt_pt LiesOn the directed line it make.
theorem pt_lies_on_of_pt_pt_of_ne {A B : P} (h: B ≠ A) : A LiesOn DLIN A B h ∧ B LiesOn DLIN A B h :=
  ⟨fst_pt_lies_on_mk_pt_pt h, snd_pt_lies_on_mk_pt_pt h⟩

theorem pt_lies_on_of_mk_pt_dir (dir : Dir) : A LiesOn mk_pt_dir A dir :=
  Line.pt_lies_on_of_mk_pt_dir A dir

theorem pt_lies_on_of_mk_pt_vec_nd (vec_nd : Vec_nd) : A LiesOn mk_pt_vec_nd A vec_nd :=
  Line.pt_lies_on_of_mk_pt_vec_nd A vec_nd

theorem dir_eq_of_mk_pt_dir (dir : Dir) : (mk_pt_dir A dir).toDir = dir := rfl

theorem mk_pt_dir_eq {A : P} {l : DirLine P} (h : A LiesOn l) : mk_pt_dir A l.toDir = l := sorry

theorem mk_pt_dir_eq_of_eq_todir {A : P} {l : DirLine P} (h : A LiesOn l) {x : Dir} (hx : x = l.toDir) : mk_pt_dir A x = l := by
  rw [hx]
  exact mk_pt_dir_eq h

theorem eq_of_same_todir_and_pt_lies_on {A : P} {l₁ l₂ : DirLine P} (h₁ : A LiesOn l₁) (h₂ : A LiesOn l₂) (h : l₁.toDir = l₂.toDir) : l₁ = l₂ := by
  rw [← mk_pt_dir_eq h₁, mk_pt_dir_eq_of_eq_todir h₂ h]

theorem eq_dirline_of_todir_eq_of_pt_of_ne {A B : P} {l : DirLine P} (h : B ≠ A) (ha : A LiesOn l) (hd : (SEG_nd A B h).toDir = l.toDir) : DLIN A B h = l := sorry

theorem eq_dirline_of_todir_eq_of_pt_of_ne' {A B : P} {l : DirLine P} (h : B ≠ A) (hb : B LiesOn l) (hd : (SEG_nd A B h).toDir = l.toDir) : DLIN A B h = l := sorry

theorem eq_dirline_rev_of_todir_ne_of_pt_pt_of_ne {A B : P} {l : DirLine P} (h : B ≠ A) (ha : A LiesOn l) (hb : B LiesOn l) (hd : (SEG_nd A B h).toDir ≠ l.toDir) : DLIN B A h.symm = l := sorry

theorem eq_dirline_or_rev_of_pt_pt_of_ne {A B : P} {l : DirLine P} (h : B ≠ A) (ha : A LiesOn l) (hb : B LiesOn l) : DLIN A B h = l ∨ DLIN B A h.symm = l :=
  if hd : (SEG_nd A B h).toDir = l.toDir then (.inl (eq_dirline_of_todir_eq_of_pt_of_ne h ha hd))
  else (.inr (eq_dirline_rev_of_todir_ne_of_pt_pt_of_ne h ha hb hd))

-- If two directed lines have a intersection point and the same direction, then these two directed lines are identical.
theorem eq_of_todir_eq_of_pt_pt_lies_on_of_ne {A B : P} (h : B ≠ A) {l₁ l₂ : DirLine P} (h₁ : A LiesOn l₁) (h₂ : A LiesOn l₂) (hd : l₁.toDir = l₂.toDir) : l₁ = l₂ := sorry

theorem eq_of_todir_eq_of_pt_pt_lies_on_of_ne' {A B : P} (h : B ≠ A) {l₁ l₂ : DirLine P} (h₁ : B LiesOn l₁) (h₂ : B LiesOn l₂) (hd : l₁.toDir = l₂.toDir) : l₁ = l₂ := sorry

theorem eq_dirline_or_rev_of_pt_pt_lies_on_of_ne {A B : P} (h : B ≠ A) {l₁ l₂ : DirLine P} (hA₁ : A LiesOn l₁) (hB₁ : B LiesOn l₁) (hA₂ : A LiesOn l₂) (hB₂ : B LiesOn l₂) : l₁ = l₂ ∨ l₁ = l₂.reverse :=
  eq_or_eq_rev_of_toline_eq (Line.eq_of_pt_pt_lies_on_of_ne h hA₁ hB₁ hA₂ hB₂)

theorem toproj_eq_seg_nd_toproj_of_lies_on {A B : P} {l : DirLine P} (ha : A LiesOn l) (hb : B LiesOn l) (hab : B ≠ A) : (SEG_nd A B hab).toProj = l.toProj :=
  (Line.toproj_eq_seg_nd_toproj_of_lies_on ha hb hab).trans l.toline_toproj_eq_toproj

theorem exsit_dirline_pt_lies_on : ∃ l : DirLine P, A LiesOn l := by
  rcases Line.exsit_line_pt_lies_on A with ⟨⟨r⟩, h⟩
  exact ⟨r.toDirLine, h⟩

end DirLine

end pt_dir



open Line DirLine

section coercion

variable (r : Ray P) (s : Seg_nd P)

theorem Ray.toline_eq_rev_toline : r.toLine = r.reverse.toLine :=
  (Quotient.eq (r := same_extn_line.setoid)).mpr same_extn_line.ray_rev_of_same_extn_line

theorem Seg_nd.toline_eq_toray_toline : s.toRay.toLine = s.toLine := rfl

theorem Seg_nd.toline_eq_rev_toline : s.toLine = s.reverse.toLine :=
  line_of_pt_pt_eq_rev s.1.source s.1.target s.2

theorem Seg_nd.toline_eq_extn_toline : s.toLine = s.extension.toLine :=
  (Quotient.eq (r := same_extn_line.setoid)).mpr ⟨by
  show s.toProj = s.reverse.toRay.reverse.toProj
  rw [Ray.toproj_of_rev_eq_toproj, Seg_nd.toray_toproj_eq_toproj, Seg_nd.toproj_of_rev_eq_toproj],
  .inl (Seg_nd.lies_on_toray_of_lies_on Seg.target_lies_on)⟩

theorem ray_of_pt_pt_toline_eq_line_of_pt_pt {A B : P} (h : B ≠ A) : (RAY A B h).toLine = LIN A B h := rfl

theorem seg_nd_of_pt_pt_toline_eq_line_of_pt_pt {A B : P} (h : B ≠ A) : (SEG_nd A B h).toLine = LIN A B h := rfl

theorem Ray.todirline_rev_eq_rev_toline : r.toDirLine.reverse = r.reverse.toDirLine :=
  (Quotient.eq (r := same_dir_line.setoid)).mpr ⟨rfl, .inl r.source_lies_on_rev⟩

theorem Seg_nd.todirline_eq_toray_toline : s.toRay.toDirLine = s.toDirLine := rfl

theorem Seg_nd.todirline_rev_eq_rev_toline : s.toDirLine.reverse = s.reverse.toDirLine := sorry

theorem Seg_nd.todirline_eq_extn_todirLine : s.toDirLine = s.extension.toDirLine :=
  (Quotient.eq (r := same_dir_line.setoid)).mpr
    ⟨s.extension_todir.symm , .inl (s.lies_on_toray_of_lies_on s.1.target_lies_on)⟩

theorem ray_of_pt_pt_todirLine_eq_dirline_of_pt_pt {A B : P} (h : B ≠ A) : (RAY A B h).toDirLine = DLIN A B h := rfl

theorem seg_nd_of_pt_pt_todirLine_eq_dirline_of_pt_pt {A B : P} (h : B ≠ A) : (SEG_nd A B h).toDirLine = DLIN A B h := rfl

end coercion

section lieson

variable (r : Ray P) (s : Seg_nd P)

theorem Ray.subset_toline : r.carrier ⊆ r.toLine.carrier := by
  rw [toline_carrier_eq_ray_carrier_union_rev_carrier]
  exact Set.subset_union_left r.carrier r.reverse.carrier

theorem ray_subset_line {r : Ray P} {l : Line P} (h : r.toLine = l) : r.carrier ⊆ l.carrier := by
  rw [← h]
  exact r.subset_toline

theorem seg_lies_on_line {s : Seg_nd P} {A : P} (h : A LiesOn s.1) : A LiesOn s.toLine :=
  Set.mem_of_subset_of_mem (ray_subset_line rfl) (Seg_nd.lies_on_toray_of_lies_on h)

theorem Seg_nd.subset_toline : s.1.carrier ⊆ s.toLine.carrier := fun _ h ↦ seg_lies_on_line h

theorem seg_subset_line {s : Seg_nd P} {l : Line P} (h : s.toLine = l) : s.1.carrier ⊆ l.carrier := by
  rw [← h]
  exact s.subset_toline

theorem Line.nontriv (l : Line P) : ∃ (A B : P), A LiesOn l ∧ B LiesOn l ∧ (B ≠ A) := by
  let ⟨r, h⟩ := l.exists_rep
  rcases r.nontriv with ⟨A, B, g⟩
  exact ⟨A, B, ⟨ray_subset_line h g.1, ray_subset_line h g.2.1, g.2.2⟩⟩

theorem Ray.lies_on_ray_or_lies_on_ray_rev_iff : A LiesOn r ∧ A ≠ r.source ∨ A LiesOn r.reverse ∧ A ≠ r.source ∨ A = r.source ↔ A LiesOn r ∨ A LiesOn r.reverse := ⟨
  fun | .inl h => .inl h.1
      | .inr h => .casesOn h (fun h => .inr h.1) (fun h => .inr (by rw[h]; exact source_lies_on)),
  fun | .inl h => if g : A = source then .inr (.inr g) else .inl ⟨h, g⟩
      | .inr h => if g : A = source then .inr (.inr g) else .inr (.inl ⟨h, g⟩)⟩

theorem Ray.lies_on_toline_iff_lies_int_or_lies_int_rev_or_eq_source {r : Ray P} : (A LiesOn r.toLine) ↔ (A LiesInt r) ∨ (A LiesInt r.reverse) ∨ (A = r.source) := by
  rw [lies_int_def, lies_int_def, source_of_rev_eq_source, lies_on_ray_or_lies_on_ray_rev_iff, lies_on_toline_iff_lies_on_or_lies_on_rev]

theorem Seg_nd.lies_on_extn_or_rev_extn_iff_lies_on_toline_of_not_lies_on {A : P} {seg_nd : Seg_nd P} (h : ¬ A LiesInt seg_nd.1) : A LiesOn seg_nd.toLine ↔ (A LiesOn seg_nd.extension) ∨ (A LiesOn seg_nd.reverse.extension) := by
  constructor
  · intro hh
    rcases Ray.lies_on_toline_iff_lies_on_or_lies_on_rev.mp hh with h₁ | h₂
    · by_cases ax : A = seg_nd.1.source
      · rw [ax]
        exact .inr Ray.source_lies_on
      by_cases ay : A = seg_nd.1.target
      · rw [ay]
        exact .inl Ray.source_lies_on
      exact .casesOn (lies_on_seg_nd_or_extension_of_lies_on_toray h₁)
        (fun h₁ ↦ (h ⟨h₁, ax, ay⟩).elim) (fun h₁ ↦ .inl h₁)
    exact .inr h₂
  · exact fun hh ↦ .casesOn hh
      (fun h₁ ↦ Eq.mpr (seg_nd.toline_eq_extn_toline ▸ Eq.refl (A LiesOn seg_nd.toLine))
        ((seg_nd.extension.lies_on_toline_iff_lies_on_or_lies_on_rev).mpr (.inl h₁)))
      (fun h₂ ↦ (seg_nd.toRay.lies_on_toline_iff_lies_on_or_lies_on_rev).mpr (.inr h₂))

theorem Seg_nd.lies_on_toline_of_lies_on_extn {X : P} {seg_nd : Seg_nd P} (lieson : X LiesOn seg_nd.extension) : X LiesOn seg_nd.toLine := by
  rw [Seg_nd.toline_eq_rev_toline]
  exact Ray.lies_on_toline_iff_lies_on_or_lies_on_rev.mpr (.inr lieson)

-- Two lines are equal iff they have the same carrier.
theorem lies_on_iff_lies_on_iff_line_eq_line (l₁ l₂ : Line P) : (∀ A : P, A LiesOn l₁ ↔ A LiesOn l₂) ↔ l₁ = l₂ := by
  constructor
  · revert l₁ l₂
    rintro ⟨r₁⟩ ⟨r₂⟩ h
    rcases r₁.toLine.nontriv with ⟨X, Y, Xrl₁, Yrl₁, neq⟩
    exact eq_of_pt_pt_lies_on_of_ne neq Xrl₁ Yrl₁ ((h X).mp Xrl₁) ((h Y).mp Yrl₁)
  · exact fun h A ↦ Iff.of_eq (congrArg (lies_on A) h)

theorem Line.lies_on_iff_eq_toproj_of_lies_on {A B : P} {l : Line P} (h : B ≠ A) (hA : A LiesOn l) : B LiesOn l ↔ (SEG_nd A B h).toProj = l.toProj := by
  refine' ⟨fun hB ↦ toproj_eq_seg_nd_toproj_of_lies_on hA hB h, fun eq ↦ _⟩
  rw [← eq_of_same_toproj_and_pt_lies_on (Seg_nd.lies_on_toline_of_lie_on (@Seg.source_lies_on _ _ (SEG_nd A B h).1)) hA eq]
  exact Seg_nd.lies_on_toline_of_lie_on Seg.target_lies_on

theorem Line.exist_real_vec_eq_smul_of_lies_on {A B : P} {dir : Dir} (h : B LiesOn (mk_pt_dir A dir)) : ∃ t : ℝ, VEC A B = t • dir.1 :=
  @exist_real_vec_eq_smul_of_lies_on_or_rev P _ B ⟨A, dir⟩ h

theorem Line.exist_real_vec_eq_smul_vec_of_lies_on {A B : P} {v : Vec_nd} (h : B LiesOn (mk_pt_vec_nd A v)) : ∃ t : ℝ, VEC A B = t • v.1 := sorry

theorem Line.exist_real_of_lies_on_of_pt_pt {A B C : P} (h : B ≠ A) (hc : C LiesOn (LIN A B h)) : ∃ t : ℝ, VEC A C = t • VEC A B :=
  @exist_real_vec_eq_smul_vec_of_lies_on P _ A C (SEG_nd A B h).toVec_nd hc

theorem Line.lies_on_of_exist_real_vec_eq_smul {A B : P} {dir : Dir} (h : ∃ t : ℝ, VEC A B = t • dir.1) : B LiesOn (mk_pt_dir A dir) :=
  (@pt_lies_on_line_from_ray_iff_vec_parallel P _ B ⟨A, dir⟩).mpr h

theorem Line.lies_on_of_exist_real_vec_eq_smul_vec {A B : P} {v : Vec_nd} (h : ∃ t : ℝ, VEC A B = t • v.1) : B LiesOn (mk_pt_vec_nd A v):= sorry

theorem Line.lies_on_of_exist_real_of_pt_pt {A B C : P} (h : B ≠ A) (ht : ∃ t : ℝ, VEC A C = t • VEC A B) : C LiesOn (LIN A B h) :=
  @lies_on_of_exist_real_vec_eq_smul_vec P _ A C (SEG_nd A B h).toVec_nd ht

theorem Ray.subset_todirLine : r.carrier ⊆ r.toDirLine.carrier := r.subset_toline

theorem ray_subset_dirline {r : Ray P} {l : DirLine P} (h : r.toDirLine = l) : r.carrier ⊆ l.carrier :=
  ray_subset_line (congrArg DirLine.toLine h)

theorem seg_lies_on_dirline {s : Seg_nd P} {A : P} (h : A LiesOn s.1) : A LiesOn s.toDirLine :=
  seg_lies_on_line h

theorem Seg_nd.subset_todirLine : s.1.carrier ⊆ s.toDirLine.carrier := s.subset_toline

theorem seg_subset_dirline {s : Seg_nd P} {l : DirLine P} (h : s.toDirLine = l) : s.1.carrier ⊆ l.carrier :=
  seg_subset_line (congrArg DirLine.toLine h)

theorem DirLine.nontriv (l : DirLine P) : ∃ (A B : P), A LiesOn l ∧ B LiesOn l ∧ (B ≠ A) :=
  l.toLine.nontriv

theorem Ray.lies_on_todirLine_iff_lies_int_or_lies_int_rev_or_eq_source {r : Ray P} : (A LiesOn r.toDirLine) ↔ (A LiesInt r) ∨ (A LiesInt r.reverse) ∨ (A = r.source) :=
  r.lies_on_toline_iff_lies_int_or_lies_int_rev_or_eq_source

theorem Seg_nd.lies_on_extn_or_rev_extn_iff_lies_on_todirLine_of_not_lies_on {A : P} {seg_nd : Seg_nd P} (h : ¬ A LiesInt seg_nd.1) : A LiesOn seg_nd.toDirLine ↔ (A LiesOn seg_nd.extension) ∨ (A LiesOn seg_nd.reverse.extension) :=
  Seg_nd.lies_on_extn_or_rev_extn_iff_lies_on_toline_of_not_lies_on h

theorem Seg_nd.lies_on_todirLine_of_lies_on_extn {X : P} {seg_nd : Seg_nd P} (h : X LiesOn seg_nd.extension) : X LiesOn seg_nd.toDirLine :=
  Seg_nd.lies_on_toline_of_lies_on_extn h

theorem DirLine.lies_on_iff_lies_on_iff_toline_eq_toline (l₁ l₂ : DirLine P) : (∀ A : P, A LiesOn l₁ ↔ A LiesOn l₂) ↔ l₁.toLine = l₂.toLine :=
  lies_on_iff_lies_on_iff_line_eq_line l₁.toLine l₂.toLine

theorem DirLine.lies_on_iff_eq_toproj_of_lies_on {A B : P} {l : DirLine P} (h : B ≠ A) (hA : A LiesOn l) : B LiesOn l ↔ (SEG_nd A B h).toProj = l.toProj :=
  (Line.lies_on_iff_eq_toproj_of_lies_on h hA).trans (Eq.congr rfl l.toline_toproj_eq_toproj)

theorem DirLine.exist_real_vec_eq_smul_of_lies_on {A B : P} {dir : Dir} (h : B LiesOn (mk_pt_dir A dir)) : ∃ t : ℝ, VEC A B = t • dir.1 :=
  @exist_real_vec_eq_smul_of_lies_on_or_rev P _ B ⟨A, dir⟩ h

theorem DirLine.exist_real_vec_eq_smul_vec_of_lies_on {A B : P} {v : Vec_nd} (h : B LiesOn (mk_pt_vec_nd A v)) : ∃ t : ℝ, VEC A B = t • v.1 :=
  Line.exist_real_vec_eq_smul_vec_of_lies_on h

theorem DirLine.exist_real_of_lies_on_of_pt_pt {A B C : P} (h : B ≠ A) (hc : C LiesOn (DLIN A B h)) : ∃ t : ℝ, VEC A C = t • VEC A B :=
  Line.exist_real_of_lies_on_of_pt_pt h hc

theorem DirLine.exist_real_vec_eq_smul_toDir_of_lies_on {A B : P} {l : DirLine P} (ha : A LiesOn l) (hb : B LiesOn l) : ∃ t : ℝ, VEC A B = t • l.toDir.1 := by
  rw [← mk_pt_dir_eq ha]
  rw [← mk_pt_dir_eq ha] at hb
  exact exist_real_vec_eq_smul_of_lies_on hb

theorem DirLine.lies_on_of_exist_real_vec_eq_smul {A B : P} {dir : Dir} (h : ∃ t : ℝ, VEC A B = t • dir.1) : B LiesOn (mk_pt_dir A dir) :=
  Line.lies_on_of_exist_real_vec_eq_smul h

theorem DirLine.lies_on_of_exist_real_vec_eq_smul_vec {A B : P} {v : Vec_nd} (h : ∃ t : ℝ, VEC A B = t • v.1) : B LiesOn (mk_pt_vec_nd A v):=
  Line.lies_on_of_exist_real_vec_eq_smul_vec h

theorem DirLine.lies_on_of_exist_real_of_pt_pt {A B C : P} (h : B ≠ A) (ht : ∃ t : ℝ, VEC A C = t • VEC A B) : C LiesOn (DLIN A B h) :=
  Line.lies_on_of_exist_real_of_pt_pt h ht

theorem DirLine.lies_on_of_exist_real_vec_eq_smul_toDir {A B : P} {l : DirLine P} (ha : A LiesOn l) (ht : ∃ t : ℝ, VEC A B = t • l.toDir.1) : B LiesOn l := by
  rw [← mk_pt_dir_eq ha]
  exact lies_on_of_exist_real_vec_eq_smul ht

end lieson



section colinear

namespace Line

theorem linear {l : Line P} {A B C : P} (h₁ : A LiesOn l) (h₂ : B LiesOn l) (h₃ : C LiesOn l) : colinear A B C := by
  revert l
  rintro ⟨ray⟩ a b c
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      cases c with
      | inl c =>
        exact Ray.colinear_of_lies_on a b c
      | inr c =>
        let ray' := Ray.mk C ray.toDir
        have a' : A ∈ ray'.carrier := lies_on_pt_todir_of_pt_lies_on_rev a c
        have b' : B ∈ ray'.carrier := lies_on_pt_todir_of_pt_lies_on_rev b c
        exact Ray.colinear_of_lies_on a' b' (Ray.source_lies_on)
    | inr b =>
      cases c with
      | inl c =>
        let ray' := Ray.mk B ray.toDir
        have a' : A ∈ ray'.carrier := lies_on_pt_todir_of_pt_lies_on_rev a b
        have c' : C ∈ ray'.carrier := lies_on_pt_todir_of_pt_lies_on_rev c b
        exact Ray.colinear_of_lies_on a' (Ray.source_lies_on) c'
      | inr c =>
        let ray' := Ray.mk A ray.reverse.toDir
        have a' : A LiesOn ray.reverse.reverse := by
          rw [Ray.rev_rev_eq_self]
          exact a
        have b' : B ∈ ray'.carrier := lies_on_pt_todir_of_pt_lies_on_rev b a'
        have c' : C ∈ ray'.carrier := lies_on_pt_todir_of_pt_lies_on_rev c a'
        exact Ray.colinear_of_lies_on (Ray.source_lies_on) b' c'
  | inr a =>
    cases b with
    | inl b =>
      cases c with
      | inl c =>
        let ray' := Ray.mk A ray.toDir
        have b' : B ∈ ray'.carrier := lies_on_pt_todir_of_pt_lies_on_rev b a
        have c' : C ∈ ray'.carrier := lies_on_pt_todir_of_pt_lies_on_rev c a
        exact Ray.colinear_of_lies_on (Ray.source_lies_on) b' c'
      | inr c =>
        let ray' := Ray.mk B ray.reverse.toDir
        have b' : B LiesOn ray.reverse.reverse := by
          rw [Ray.rev_rev_eq_self]
          exact b
        have a' : A ∈ ray'.carrier := lies_on_pt_todir_of_pt_lies_on_rev a b'
        have c' : C ∈ ray'.carrier := lies_on_pt_todir_of_pt_lies_on_rev c b'
        exact Ray.colinear_of_lies_on a' (Ray.source_lies_on) c'
    | inr b =>
      cases c with
      | inl c =>
        let ray' := Ray.mk C ray.reverse.toDir
        have c' : C LiesOn ray.reverse.reverse := by
          rw [Ray.rev_rev_eq_self]
          exact c
        have a' : A ∈ ray'.carrier := lies_on_pt_todir_of_pt_lies_on_rev a c'
        have b' : B ∈ ray'.carrier := lies_on_pt_todir_of_pt_lies_on_rev b c'
        exact Ray.colinear_of_lies_on  a' b' (Ray.source_lies_on)
      | inr c =>
        exact Ray.colinear_of_lies_on a b c

theorem pt_pt_maximal {A B C : P} (h : B ≠ A) (Co : colinear A B C) : C LiesOn (LIN A B h) := sorry

theorem maximal {l : Line P} {A B C : P} (h₁ : A LiesOn l) (h₂ : B LiesOn l) (h : B ≠ A) (Co : colinear A B C) : C LiesOn l := by
  rw [← eq_line_of_pt_pt_of_ne h h₁ h₂]
  exact pt_pt_maximal h Co

theorem lies_on_line_of_pt_pt_iff_colinear {A B : P} (h : B ≠ A) (X : P) : (X LiesOn (LIN A B h)) ↔ colinear A B X := ⟨
  fun hx ↦ (LIN A B h).linear (fst_pt_lies_on_mk_pt_pt h) (snd_pt_lies_on_mk_pt_pt h) hx,
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

end Line

namespace DirLine

theorem linear {l : DirLine P} {A B C : P} (h₁ : A LiesOn l) (h₂ : B LiesOn l) (h₃ : C LiesOn l) : colinear A B C :=
  Line.linear h₁ h₂ h₃

theorem pt_pt_maximal {A B C : P} (h : B ≠ A) (Co : colinear A B C) : C LiesOn (DLIN A B h) :=
  Line.pt_pt_maximal h Co

theorem maximal {l : DirLine P} {A B C : P} (h₁ : A LiesOn l) (h₂ : B LiesOn l) (h : B ≠ A) (Co : colinear A B C) : C LiesOn l :=
  Line.maximal  h₁ h₂ h Co

theorem lies_on_dirline_of_pt_pt_iff_colinear {A B : P} (h : B ≠ A) (X : P) : (X LiesOn (DLIN A B h)) ↔ colinear A B X :=
  Line.lies_on_line_of_pt_pt_iff_colinear h X

theorem lies_on_iff_colinear_of_ne_lies_on_lies_on {A B : P} {l : DirLine P} (h : B ≠ A) (ha : A LiesOn l) (hb : B LiesOn l) (C : P) : (C LiesOn l) ↔ colinear A B C :=
  Line.lies_on_iff_colinear_of_ne_lies_on_lies_on h ha hb C

theorem colinear_iff_exist_dirline_lies_on (A B C : P) : colinear A B C ↔ ∃ l : Line P, (A LiesOn l) ∧ (B LiesOn l) ∧ (C LiesOn l) :=
  Line.colinear_iff_exist_line_lies_on A B C

end DirLine

end colinear



section Archimedean_property

namespace Line

-- there are two distinct points on a line
theorem exists_ne_pt_pt_lies_on_of_line (A : P) (l : Line P) : ∃ B : P, B LiesOn l ∧ B ≠ A := by
  rcases l.nontriv with ⟨X, Y, hx, hy, ne⟩
  exact if h : A = X then ⟨Y, hy, ne.trans_eq h.symm⟩ else ⟨X, hx, ne_comm.mp h⟩

theorem lies_on_of_Seg_nd_toproj_eq_toproj {A B : P} {l : Line P} (ha : A LiesOn l) (hab : B ≠ A) (hp : (SEG_nd A B hab).toProj = l.toProj) : B LiesOn l :=
  (lies_on_iff_eq_toproj_of_lies_on hab ha).mpr hp

theorem vec_vadd_pt_lies_on_line {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) (h : B ≠ A) : (VEC A B) +ᵥ B LiesOn l := by
  rw [← eq_line_of_pt_pt_of_ne h hA hB]
  refine' Ray.lies_on_toline_iff_lies_on_or_lies_on_rev.mpr
    (.inl ⟨2 * ‖VEC A B‖, mul_nonneg zero_le_two (norm_nonneg (VEC A B)), _⟩)
  have eq : VEC A (VEC A B +ᵥ B) = 2 * (VEC A B) := (vadd_vsub_assoc _ B A).trans (two_mul _).symm
  simp only [Ray.mk_pt_pt, eq, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat,
    mul_assoc, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
  exact (Vec_nd.norm_smul_todir_eq_self ⟨VEC A B, (ne_iff_vec_ne_zero A B).1 h⟩).symm

theorem exist_pt_beyond_pt_right {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) (h : B ≠ A) : ∃ C : P, C LiesOn l ∧ B LiesInt (SEG A C) :=
  ⟨VEC A B +ᵥ B, vec_vadd_pt_lies_on_line hA hB h, (SEG_nd A B h).target_lies_int_seg_source_vec_vadd_target⟩

theorem exist_pt_beyond_pt_left {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) (h : B ≠ A) : ∃ C : P, C LiesOn l ∧ A LiesInt (SEG C B) := by
  rcases exist_pt_beyond_pt_right hB hA h.symm with ⟨C, cl, acb⟩
  exact ⟨C, cl, Seg.lies_int_iff_lies_int_rev.mp acb⟩

end Line

namespace DirLine

-- there are two distinct points on a directed line
theorem exists_ne_pt_pt_lies_on_of_dirline (A : P) (l : DirLine P) : ∃ B : P, B LiesOn l ∧ B ≠ A :=
  Line.exists_ne_pt_pt_lies_on_of_line A l

theorem lies_on_of_Seg_nd_toproj_eq_toproj {A B : P} {l : DirLine P} (ha : A LiesOn l) (hab : B ≠ A) (hp : (SEG_nd A B hab).toDir = l.toDir) : B LiesOn l :=
  Line.lies_on_of_Seg_nd_toproj_eq_toproj ha hab ((congrArg Dir.toProj hp).trans l.toline_toproj_eq_toproj.symm)

theorem exist_pt_beyond_pt_right {A B : P} {l : DirLine P} (hA : A LiesOn l) (hB : B LiesOn l) (h : B ≠ A) : ∃ C : P, C LiesOn l ∧ B LiesInt (SEG A C) :=
  Line.exist_pt_beyond_pt_right hA hB h

theorem exist_pt_beyond_pt_left {A B : P} {l : DirLine P} (hA : A LiesOn l) (hB : B LiesOn l) (h : B ≠ A) : ∃ C : P, C LiesOn l ∧ A LiesInt (SEG C B) :=
  Line.exist_pt_beyond_pt_left hA hB h

end DirLine

end Archimedean_property

end EuclidGeom
