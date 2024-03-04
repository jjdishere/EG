import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Basic.Angle

/-!
# Baisc definitions of angle as a figure

-/

noncomputable section

namespace EuclidGeom

open Classical Dir

/-- The angle value between two directed figures. -/
def DirObj.AngDiff {α β} [DirObj α] [DirObj β] (F : α) (G : β) : AngValue := toDir G -ᵥ toDir F

/-- The `AngDValue` between two figures with projective directions. -/
def ProjObj.DAngDiff {α β} [ProjObj α] [ProjObj β] (F : α) (G : β) : AngDValue := toProj G -ᵥ toProj F

export ProjObj (DAngDiff)

export DirObj (AngDiff)

/- Define values of oriented angles, in (-π, π], modulo 2 π. -/
/- Define oriented angles, ONLY taking in two rays starting at one point! And define ways to construct oriented angles, by given three points on the plane, and etc.  -/

/-- An `Angle` is a structure of a point $P$ and two directions, which is the angle consists of
two rays start at $P$ along with the two specified directions. -/
@[ext]
structure Angle (P : Type*) [EuclideanPlane P] where
  source : P
  dir₁ : Dir
  dir₂ : Dir

attribute [pp_dot] Angle.source Angle.dir₁ Angle.dir₂

variable {P : Type*} [EuclideanPlane P]

namespace Angle

alias mk_pt_dir_dir := Angle.mk

/-- Given two rays with the same source, this function returns the angle consists of these two rays. -/
def mk_two_ray_of_eq_source (r : Ray P) (r' : Ray P) (_h : r.source = r'.source) : Angle P where
  source := r.source
  dir₁ := r.toDir
  dir₂ := r'.toDir

/-- Given vertex $O$ and two distinct points $A$ and $B$, this function returns the angle
formed by rays $OA$ and $OB$. We use $\verb|ANG|$ to abbreviate $\verb|Angle.mk_pt_pt_pt|$. -/
def mk_pt_pt_pt (A O B : P) (h₁ : A ≠ O) (h₂ : B ≠ O) : Angle P where
  source := O
  dir₁ := (VEC_nd O A h₁).toDir
  dir₂ := (VEC_nd O B h₂).toDir

def mk_ray_pt (r : Ray P) (A : P) (h : A ≠ r.source) : Angle P where
  source := r.source
  dir₁ := r.toDir
  dir₂ := (VEC_nd r.source A h).toDir

def mk_pt_ray (A : P) (r : Ray P) (h : A ≠ r.source) : Angle P where
  source := r.source
  dir₁ := (VEC_nd r.source A h).toDir
  dir₂ := r.toDir

def mk_dirline_dirline (l₁ l₂ : DirLine P) (h : ¬ l₁ ∥ l₂) : Angle P where
  source := Line.inx l₁.toLine l₂.toLine (DirLine.not_para_toLine_of_not_para h)
  dir₁ := l₁.toDir
  dir₂ := l₂.toDir

variable (ang : Angle P)

@[pp_dot]
def value : AngValue := ang.dir₂ -ᵥ ang.dir₁

@[pp_dot]
abbrev dvalue : AngDValue := (ang.value : AngDValue)

@[pp_dot]
abbrev proj₁ : Proj := ang.dir₁.toProj

@[pp_dot]
abbrev proj₂ : Proj := ang.dir₂.toProj

@[pp_dot]
abbrev IsPos : Prop := ang.value.IsPos

@[pp_dot]
abbrev IsNeg : Prop := ang.value.IsNeg

@[pp_dot]
abbrev IsND : Prop := ang.value.IsND

@[pp_dot]
abbrev IsAcu : Prop := ang.value.IsAcu

@[pp_dot]
abbrev IsObt : Prop := ang.value.IsObt

@[pp_dot]
abbrev IsRt : Prop := ang.value.IsRt

end Angle

/-- The value of $\verb|Angle.mk_pt_pt_pt| A O B$. We use `∠` to abbreviate
$\verb|Angle.value_of_angle_of_three_point_nd|$. -/
abbrev value_of_angle_of_three_point_nd (A O B : P) (h₁ : A ≠ O) (h₂ : B ≠ O) : AngValue :=
  (Angle.mk_pt_pt_pt A O B h₁ h₂).value

abbrev value_of_angle_of_two_ray_of_eq_source (start_ray end_ray : Ray P) (h : start_ray.source = end_ray.source) : AngValue :=
  (Angle.mk_two_ray_of_eq_source start_ray end_ray h).value

theorem value_of_angle_of_two_ray_of_eq_source_eq_angDiff (start_ray end_ray : Ray P) (h : start_ray.source = end_ray.source) : value_of_angle_of_two_ray_of_eq_source start_ray end_ray h = DirObj.AngDiff start_ray end_ray :=
  rfl

abbrev value_of_angle_of_pt_dir_dir (O : P) (r r' : Dir) : AngValue :=
  (Angle.mk O r r').value

theorem value_of_angle_of_pt_dir_dir_eq_angDiff (O : P) (r r' : Dir) : value_of_angle_of_pt_dir_dir O r r' = DirObj.AngDiff r r' :=
  rfl

@[inherit_doc Angle.mk_pt_pt_pt]
scoped syntax "ANG" ws term:max ws term:max ws term:max (ws term:max ws term:max)? : term

macro_rules
  | `(ANG $A $B $C) => `(Angle.mk_pt_pt_pt $A $B $C (@Fact.out _ inferInstance) (@Fact.out _ inferInstance))
  | `(ANG $A $B $C $h₁ $h₂) => `(Angle.mk_pt_pt_pt $A $B $C $h₁ $h₂)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `Angle.mk_pt_pt_pt` -/
@[delab app.EuclidGeom.Angle.mk_pt_pt_pt]
def delabAngleMkPtPtPt : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``Angle.mk_pt_pt_pt 7
  let A ← withNaryArg 2 delab
  let B ← withNaryArg 3 delab
  let C ← withNaryArg 4 delab
  let ⟨b₁, h₁⟩ ← withNaryArg 5 do
    return ((← getExpr).isAppOfArity' ``Fact.out 2, ← delab)
  let ⟨b₂, h₂⟩ ← withNaryArg 6 do
    return ((← getExpr).isAppOfArity' ``Fact.out 2, ← delab)
  if b₁ && b₂ then
    `(ANG $A $B $C)
  else
    `(ANG $A $B $C $h₁ $h₂)

@[inherit_doc value_of_angle_of_three_point_nd]
scoped syntax "∠" ws term:max ws term:max ws term:max (ws term:max ws term:max)? : term

macro_rules
  | `(∠ $A $B $C) => `(value_of_angle_of_three_point_nd $A $B $C (@Fact.out _ inferInstance) (@Fact.out _ inferInstance))
  | `(∠ $A $B $C $h₁ $h₂) => `(value_of_angle_of_three_point_nd $A $B $C $h₁ $h₂)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `value_of_angle_of_three_point_nd` -/
@[delab app.EuclidGeom.value_of_angle_of_three_point_nd]
def delabValueOfAngleOfThreePointND : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``value_of_angle_of_three_point_nd 7
  let A ← withNaryArg 2 delab
  let B ← withNaryArg 3 delab
  let C ← withNaryArg 4 delab
  let ⟨b₁, h₁⟩ ← withNaryArg 5 do
    return ((← getExpr).isAppOfArity' ``Fact.out 2, ← delab)
  let ⟨b₂, h₂⟩ ← withNaryArg 6 do
    return ((← getExpr).isAppOfArity' ``Fact.out 2, ← delab)
  if b₁ && b₂ then
    `(∠ $A $B $C)
  else
    `(∠ $A $B $C $h₁ $h₂)

/-- The dvalue of $\verb|Angle.mk_pt_pt_pt| A O B$. We use `∡` to abbreviate
$\verb|Angle.dvalue_of_angle_of_three_point_nd|$. -/
abbrev dvalue_of_angle_of_three_point_nd (A O B : P) (h₁ : A ≠ O) (h₂ : B ≠ O) : AngDValue :=
  (Angle.mk_pt_pt_pt A O B h₁ h₂).dvalue

@[inherit_doc dvalue_of_angle_of_three_point_nd]
scoped syntax "∡" ws term:max ws term:max ws term:max (ws term:max ws term:max)? : term

macro_rules
  | `(∡ $A $B $C) => `(dvalue_of_angle_of_three_point_nd $A $B $C (@Fact.out _ inferInstance) (@Fact.out _ inferInstance))
  | `(∡ $A $B $C $h₁ $h₂) => `(dvalue_of_angle_of_three_point_nd $A $B $C $h₁ $h₂)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `value_of_angle_of_three_point_nd` -/
@[delab app.EuclidGeom.dvalue_of_angle_of_three_point_nd]
def delabDValueOfAngleOfThreePointND : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``dvalue_of_angle_of_three_point_nd 7
  let A ← withNaryArg 2 delab
  let B ← withNaryArg 3 delab
  let C ← withNaryArg 4 delab
  let ⟨b₁, h₁⟩ ← withNaryArg 5 do
    return ((← getExpr).isAppOfArity' ``Fact.out 2, ← delab)
  let ⟨b₂, h₂⟩ ← withNaryArg 6 do
    return ((← getExpr).isAppOfArity' ``Fact.out 2, ← delab)
  if b₁ && b₂ then
    `(∡ $A $B $C)
  else
    `(∡ $A $B $C $h₁ $h₂)

namespace Angle

section start_end_ray

variable {ang : Angle P}

@[pp_dot]
def start_ray (ang : Angle P) : Ray P := ⟨ang.source, ang.dir₁⟩

@[pp_dot]
def end_ray (ang : Angle P) : Ray P := ⟨ang.source, ang.dir₂⟩

@[pp_dot]
theorem start_ray_source_eq_end_ray_source : ang.start_ray.source = ang.end_ray.source := rfl

@[simp]
theorem start_ray_toDir : ang.start_ray.toDir = ang.dir₁ := rfl

@[simp]
theorem end_ray_toDir : ang.end_ray.toDir = ang.dir₂ := rfl

@[simp]
theorem source_eq_start_ray_source : ang.start_ray.source = ang.source := rfl

@[simp]
theorem source_eq_end_ray_source : ang.end_ray.source = ang.source := rfl

theorem source_lies_on_start_ray : ang.source LiesOn ang.start_ray :=
  ang.start_ray.source_lies_on

theorem source_lies_on_end_ray : ang.source LiesOn ang.end_ray :=
  ang.end_ray.source_lies_on

theorem start_ray_not_para_end_ray_of_isND (h : ang.IsND) : ¬ ang.start_ray ∥ ang.end_ray :=
  Dir.toProj_ne_toProj_iff_neg_vsub_isND.mpr h

theorem start_ray_eq_end_ray_of_value_eq_zero (h : ang.value = 0) : ang.start_ray = ang.end_ray :=
  Ray.ext ang.start_ray ang.end_ray rfl (eq_of_vsub_eq_zero h).symm

theorem start_ray_eq_end_ray_reverse_of_value_eq_pi (h : ang.value = π) : ang.start_ray = ang.end_ray.reverse :=
  Ray.ext ang.start_ray ang.end_ray.reverse rfl
    (neg_eq_iff_eq_neg.mp ((eq_neg_of_vsub_eq_pi ang.dir₂ ang.dir₁).mpr h).symm)

@[pp_dot]
def start_dirLine (ang : Angle P) : DirLine P := DirLine.mk_pt_dir ang.source ang.dir₁

@[pp_dot]
def end_dirLine (ang : Angle P) : DirLine P := DirLine.mk_pt_dir ang.source ang.dir₂

@[simp]
theorem start_dirLine_toDir : ang.start_dirLine.toDir = ang.dir₁ := rfl

@[simp]
theorem end_dirLine_toDir : ang.end_dirLine.toDir = ang.dir₂ := rfl

@[simp]
theorem start_ray_toDirLine_eq_start_dirLine : ang.start_ray.toDirLine = ang.start_dirLine := rfl

@[simp]
theorem end_ray_toDirLine_eq_end_dirLine : ang.end_ray.toDirLine = ang.end_dirLine := rfl

theorem source_lies_on_start_dirLine: ang.source LiesOn ang.start_dirLine :=
  DirLine.pt_lies_on_of_mk_pt_dir ang.source ang.dir₁

theorem source_lies_on_end_dirLine : ang.source LiesOn ang.end_dirLine :=
  DirLine.pt_lies_on_of_mk_pt_dir ang.source ang.dir₂

theorem start_dirLine_not_para_end_dirLine_of_value_ne_zero (h : ang.value.IsND) : ¬ ang.start_dirLine ∥ ang.end_dirLine :=
  start_ray_not_para_end_ray_of_isND h

theorem start_dirLine_eq_end_dirLine_of_value_eq_zero (h : ang.value = 0) : ang.start_dirLine = ang.end_dirLine :=
  congrArg Ray.toDirLine (start_ray_eq_end_ray_of_value_eq_zero h)

theorem start_dirLine_eq_end_dirLine_reverse_of_value_eq_pi (h : ang.value = π) : ang.start_dirLine = ang.end_dirLine.reverse :=
  congrArg Ray.toDirLine (start_ray_eq_end_ray_reverse_of_value_eq_pi h)

end start_end_ray

section carrier
/-
def dir_min (ang : Angle P) : Dir := if ang.IsNeg then ang.dir₂ else ang.dir₁

def dir_max (ang : Angle P) : Dir := if ang.IsNeg then ang.dir₁ else ang.dir₂

def abs (ang : Angle P) : Angle P where
  source := ang.source
  dir₁ := ang.dir_min
  dir₂ := ang.dir_max

variable {ang : Angle P}

theorem abs_value_eq_value_abs : ang.abs.value = ang.value.abs := sorry

theorem abs_not_isNeg : ¬ ang.abs.IsNeg := sorry

protected structure IsInt (p : P) (ang : Angle P) : Prop where
  ne_source : p ≠ ang.source
  isInt : sbtw ang.dir_min (VEC_nd ang.source p ne_source).toDir ang.dir_max
-/

/-
-- `should discuss this later, is there a better definition?` ite, dite is bitter to deal with
/- `What does it mean to be LiesIn a angle? when the angle < 0`, for now it is defined as the smaller side. and when angle = π, it is defined as the left side -/

-- Do we need an abbreviation for `sbtw ang.dir₁ dir ang.dir₂`?

protected def IsOn (p : P) (ang : Angle P) : Prop :=
  if h : p = ang.source then True
  else btw ang.dir₁ (VEC_nd ang.source p h).toDir ang.dir₂
  /- There may be problems when `ang.value = 0`. See the example below.
  Maybe change it to `ang.IsInt p ∨ p LiesOn ang.strat_ray ∨ p LiesOn ang.end_ray`. -/

protected structure IsInt (p : P) (ang : Angle P) : Prop where
  ne_source : p ≠ ang.source
  isInt : sbtw ang.dir₁ (VEC_nd ang.source p ne_source).toDir ang.dir₂

variable {p : P} {ang : Angle P} {d : Dir} {r : Ray P}

protected theorem ison_of_isint (h : ang.IsInt p) : ang.IsOn p := by
  simp only [Angle.IsOn, h.1, dite_false]
  exact btw_of_sbtw h.2

protected def carrier (ang : Angle P) : Set P := { p : P | Angle.IsOn p ang}

instance : Fig (Angle P) P where
  carrier := Angle.carrier

protected def interior (ang : Angle P) : Set P := { p : P | Angle.IsInt p ang }

instance : Interior (Angle P) P where
  interior := Angle.interior

instance : IntFig (Angle P) P where
  carrier := Angle.carrier
  interior_subset_carrier _ _ := Angle.ison_of_isint

theorem source_lies_on (ang : Angle P) : ang.source LiesOn ang := by
  show if h : ang.1 = ang.1 then True else btw ang.dir₁ (VEC_nd ang.1 ang.1 h).toDir ang.dir₂
  simp only [dite_true]

theorem lies_on_of_eq (h : p = ang.source) : p LiesOn ang := by
  simp only [h, source_lies_on]

theorem lies_on_iff_btw_of_ptNe [_h : PtNe p ang.source] : p LiesOn ang ↔ btw ang.dir₁ (VEC_nd ang.source p).toDir ang.dir₂ :=
  (dite_prop_iff_and _).trans ((and_iff_right (fun _ ↦ trivial)).trans (forall_prop_of_true _h.1))

example (p : P) {ang : Angle P} [PtNe p ang.source] (h : ang.dir₁ = ang.dir₂) : p LiesOn ang := by
  apply lies_on_iff_btw_of_ptNe.mpr
  rw [h]
  exact btw_rfl_left_right

theorem lies_on_of_lies_on_ray_mk (hd : btw ang.dir₁ d ang.dir₂) (h : p LiesOn Ray.mk ang.source d) : p LiesOn ang := sorry

theorem lies_on_of_lies_on_ray (hs : ang.source = r.source) (hd : btw ang.dir₁ r.toDir ang.dir₂) (h : p LiesOn r) : p LiesOn ang :=
  lies_on_of_lies_on_ray_mk hd ((congrArg (lies_on p) (congrFun (congrArg Ray.mk hs) r.toDir)).mpr h)

theorem lies_on_iff_lies_on_ray : p LiesOn ang ↔ ∃ r : Ray P, (ang.source = r.source ∧ btw ang.dir₁ r.toDir ang.dir₂) ∧ p LiesOn r := sorry

theorem lies_int_of_lies_int_ray_mk (hd : btw ang.dir₁ d ang.dir₂) (h : p LiesInt Ray.mk ang.source d) : p LiesInt ang := sorry

theorem lies_int_of_lies_int_ray (hs : ang.source = r.source) (hd : btw ang.dir₁ r.toDir ang.dir₂) (h : p LiesInt r) : p LiesInt ang :=
  lies_int_of_lies_int_ray_mk hd ((congrArg (lies_int p) (congrFun (congrArg Ray.mk hs) r.toDir)).mpr h)

theorem lies_int_iff_lies_int_ray : p LiesInt ang ↔ ∃ r : Ray P, (ang.source = r.source ∧ btw ang.dir₁ r.toDir ang.dir₂) ∧ p LiesInt r := sorry
 -/
end carrier

section mk_two_ray

variable (r r' : Ray P) (h : r.source = r'.source)

theorem source_eq_fst_source_of_mk_two_ray_of_eq_source: (mk_two_ray_of_eq_source r r' h).source = r.source := rfl

theorem source_eq_snd_source_of_mk_two_ray_of_eq_source : (mk_two_ray_of_eq_source r r' h).source = r'.source := h

@[simp]
theorem mk_two_ray_of_eq_source_dir₁ : (mk_two_ray_of_eq_source r r' h).dir₁ = r.toDir := rfl

@[simp]
theorem mk_two_ray_of_eq_source_dir₂ : (mk_two_ray_of_eq_source r r' h).dir₂ = r'.toDir := rfl

@[simp]
theorem mk_two_ray_of_eq_source_start_ray : (mk_two_ray_of_eq_source r r' h).start_ray = r := rfl

@[simp]
theorem mk_two_ray_of_eq_source_end_ray : (mk_two_ray_of_eq_source r r' h).end_ray = r' :=
  Ray.ext (mk_two_ray_of_eq_source r r' h).end_ray r' h rfl

theorem mk_two_ray_of_eq_source_value : (mk_two_ray_of_eq_source r r' h).value = r'.toDir -ᵥ r.toDir := rfl

@[simp]
theorem same_ray_value_eq_zero (r : Ray P) : (mk_two_ray_of_eq_source r r rfl).value = 0 :=
  vsub_self r.2

end mk_two_ray

section pt_pt_pt

variable {A O B : P} (ha : A ≠ O) (hb : B ≠ O)

@[simp]
theorem mk_pt_pt_pt_source : (ANG A O B ha hb).source = O := rfl

@[simp]
theorem mk_pt_pt_pt_dir₁ : (ANG A O B ha hb).dir₁ = (VEC_nd O A ha).toDir := rfl

@[simp]
theorem mk_pt_pt_pt_dir₂ : (ANG A O B ha hb).dir₂ = (VEC_nd O B hb).toDir := rfl

@[simp]
theorem mk_pt_pt_pt_start_ray : (ANG A O B ha hb).start_ray = RAY O A ha := rfl

@[simp]
theorem mk_pt_pt_pt_end_ray : (ANG A O B ha hb).end_ray = RAY O B hb := rfl

@[simp]
theorem neg_value_eq_rev_ang : - ∠ A O B ha hb = ∠ B O A hb ha :=
  neg_vsub_eq_vsub_rev (VEC_nd O B hb).toDir (VEC_nd O A ha).toDir

theorem neg_value_of_rev_ang {A O B : P} [h₁ : PtNe A O] [h₂ : PtNe B O] : ∠ A O B = -∠ B O A :=
  (neg_value_eq_rev_ang h₂.1 h₁.1).symm

end pt_pt_pt

section mk_ray_pt

variable (r : Ray P) (A : P) (h : A ≠ r.source)

@[simp]
theorem mk_ray_pt_source : (mk_ray_pt r A h).source = r.source := rfl

@[simp]
theorem mk_ray_pt_dir₁ : (mk_ray_pt r A h).dir₁ = r.toDir := rfl

@[simp]
theorem mk_ray_pt_dir₂ : (mk_ray_pt r A h).dir₂ = (VEC_nd r.source A h).toDir := rfl

@[simp]
theorem mk_ray_pt_start_ray : (mk_ray_pt r A h).start_ray = r := rfl

@[simp]
theorem mk_ray_pt_end_ray : (mk_ray_pt r A h).end_ray = RAY r.source A h := rfl

end mk_ray_pt

section mk_pt_ray

variable (A : P) (r : Ray P) (h : A ≠ r.source)

@[simp]
theorem mk_pt_ray_source : (mk_pt_ray A r h).source = r.source := rfl

@[simp]
theorem mk_pt_ray_dir₁ : (mk_pt_ray A r h).dir₁ = (VEC_nd r.source A h).toDir := rfl

@[simp]
theorem mk_pt_ray_dir₂ : (mk_pt_ray A r h).dir₂ = r.toDir := rfl

@[simp]
theorem mk_pt_ray_start_ray : (mk_pt_ray A r h).start_ray = RAY r.source A h := rfl

@[simp]
theorem mk_pt_ray_end_ray : (mk_pt_ray A r h).end_ray = r := rfl

end mk_pt_ray

section change_dir

def mk_dir₁ (ang : Angle P) (d : Dir) : Angle P where
  source := ang.source
  dir₁ := ang.dir₁
  dir₂ := d

def mk_dir₂ (ang : Angle P) (d : Dir) : Angle P where
  source := ang.source
  dir₁ := d
  dir₂ := ang.dir₂

@[simp]
theorem mk_dir₁_source {ang : Angle P} (d : Dir) : (mk_dir₁ ang d).source = ang.source := rfl

@[simp]
theorem mk_dir₂_source {ang : Angle P} (d : Dir) : (mk_dir₂ ang d).source = ang.source := rfl

theorem mk_dir₁_value {ang : Angle P} (d : Dir) : (mk_dir₁ ang d).value = d -ᵥ ang.dir₁ := rfl

theorem mk_dir₂_value {ang : Angle P} (d : Dir) : (mk_dir₂ ang d).value = ang.dir₂ -ᵥ d := rfl

theorem mk_dir₁_dir₂_eq_self {ang : Angle P} : mk_dir₁ ang ang.dir₂ = ang := rfl

theorem mk_dir₂_dir₁_eq_self {ang : Angle P} : mk_dir₂ ang ang.dir₁ = ang := rfl

/-
variable {p : P} {ang : Angle P} {d : Dir}

theorem lies_on_of_lies_on_mk_dir₁ (hd : btw ang.dir₁ d ang.dir₂) (h : p LiesOn mk_dir₁ ang d) : p LiesOn ang := sorry

theorem lies_on_mk_dir₁_of_lies_on (hd : btw ang.dir₁ ang.dir₂ d) (h : p LiesOn ang) : p LiesOn mk_dir₁ ang d := sorry

theorem lies_int_of_lies_int_mk_dir₁ (hd : btw ang.dir₁ d ang.dir₂) (h : p LiesInt mk_dir₁ ang d) : p LiesInt ang := sorry

theorem lies_int_mk_dir₁_of_lies_int (hd : btw ang.dir₁ ang.dir₂ d) (h : p LiesInt ang) : p LiesInt mk_dir₁ ang d := sorry

theorem lies_on_of_lies_on_mk_dir₂ (hd : btw ang.dir₁ d ang.dir₂) (h : p LiesOn mk_dir₂ ang d) : p LiesOn ang := sorry

theorem lies_on_mk_dir₂_of_lies_on (hd : btw ang.dir₂ ang.dir₁ d) (h : p LiesOn ang) : p LiesOn mk_dir₁ ang d := sorry

theorem lies_int_of_lies_int_mk_dir₂ (hd : btw ang.dir₁ d ang.dir₂) (h : p LiesInt mk_dir₂ ang d) : p LiesInt ang := sorry

theorem lies_int_mk_dir₂_of_lies_int (hd : btw ang.dir₁ ang.dir₂ d) (h : p LiesInt ang) : p LiesInt mk_dir₂ ang d := sorry

theorem lies_on_of_lies_on_of_btw_of_btw {ang₁ : Angle P} {ang₂ : Angle P} (h₁ : btw ang₁.dir₁ ang₂.dir₁ ang₁.dir₂) (h₂ : btw ang₁.dir₁ ang₂.dir₂ ang₁.dir₂) (h : p LiesOn ang₂) : p LiesOn ang₁ := sorry

theorem lies_int_of_lies_int_of_btw_of_btw {ang₁ : Angle P} {ang₂ : Angle P} (h₁ : btw ang₁.dir₁ ang₂.dir₁ ang₁.dir₂) (h₂ : btw ang₁.dir₁ ang₂.dir₂ ang₁.dir₂) (h : p LiesInt ang₂) : p LiesInt ang₁ := sorry
 -/
end change_dir

-- this section should talks about when different making methods make the same angle
section mk_compatibility

variable {ang : Angle P}

@[simp]
theorem mk_start_ray_end_ray_eq_self : mk_two_ray_of_eq_source ang.start_ray ang.end_ray rfl = ang := rfl

theorem eq_of_lies_int_ray {A B : P} (ha : A LiesInt ang.start_ray) (hb : B LiesInt ang.end_ray) : ANG A ang.source B ha.2 hb.2 = ang :=
  Angle.ext (ANG A ang.source B ha.2 hb.2) ang rfl
    (Ray.pt_pt_toDir_eq_ray_toDir ha) (Ray.pt_pt_toDir_eq_ray_toDir hb)

theorem value_eq_of_lies_int_ray {A B : P} (ha : A LiesInt ang.start_ray) (hb : B LiesInt ang.end_ray) : ∠ A ang.source B ha.2 hb.2 = ang.value :=
  congrArg value (eq_of_lies_int_ray ha hb)

theorem eq_of_lies_on_ray {A B : P} [_ha : PtNe A ang.source] [_hb : PtNe B ang.source] (ha : A LiesOn ang.start_ray) (hb : B LiesOn ang.end_ray) : ANG A ang.source B = ang :=
  eq_of_lies_int_ray ⟨ha, _ha.1⟩ ⟨hb, _hb.1⟩

theorem value_eq_of_lies_on_ray {A B : P} [PtNe A ang.source] [PtNe B ang.source] (ha : A LiesOn ang.start_ray) (hb : B LiesOn ang.end_ray) : ∠ A ang.source B = ang.value :=
  congrArg value (eq_of_lies_on_ray ha hb)

theorem eq_of_lies_on_ray_pt_pt {A B C D O : P} [PtNe A O] [PtNe B O] [_hc : PtNe C O] [_hd : PtNe D O] (hc : C LiesOn (RAY O A)) (hd : D LiesOn (RAY O B) ) : ANG C O D = ANG A O B :=
  have hc : C LiesOn (ANG A O B).start_ray := hc
  have hd : D LiesOn (ANG A O B).end_ray := hd
  haveI : PtNe C (ANG A O B).source := _hc
  haveI : PtNe D (ANG A O B).source := _hd
  eq_of_lies_on_ray hc hd

theorem value_eq_of_lies_on_ray_pt_pt {A B C D O : P} [PtNe A O] [PtNe B O] [PtNe C O] [PtNe D O] (hc : C LiesOn (RAY O A)) (hd :  D LiesOn (RAY O B) ) : ∠ C O D = ∠ A O B :=
  congrArg value (eq_of_lies_on_ray_pt_pt hc hd)

theorem mk_ray_pt_eq_of_lies_int {A : P} (h : A LiesInt ang.end_ray) : mk_ray_pt ang.start_ray A h.2 = ang :=
  Angle.ext (mk_ray_pt ang.start_ray A h.2) ang rfl rfl (Ray.pt_pt_toDir_eq_ray_toDir h)

theorem mk_ray_pt_eq_of_lies_on {A : P} [_h : PtNe A ang.source] (h : A LiesOn ang.end_ray) : mk_ray_pt ang.start_ray A _h.1 = ang :=
  Angle.ext (mk_ray_pt ang.start_ray A _h.1) ang rfl rfl (Ray.pt_pt_toDir_eq_ray_toDir ⟨h, _h.1⟩)

theorem mk_pt_ray_eq_of_lies_int {A : P} (h : A LiesInt ang.start_ray) : mk_pt_ray A ang.end_ray h.2 = ang :=
  Angle.ext (mk_pt_ray A ang.end_ray h.2) ang rfl (Ray.pt_pt_toDir_eq_ray_toDir h) rfl

theorem mk_pt_ray_eq_of_lies_on {A : P} [_h : PtNe A ang.source] (h : A LiesOn ang.start_ray) : mk_pt_ray A ang.end_ray _h.1 = ang :=
  Angle.ext (mk_pt_ray A ang.end_ray _h.1) ang rfl (Ray.pt_pt_toDir_eq_ray_toDir ⟨h, _h.1⟩) rfl

theorem mk_start_dirLine_end_dirLine_eq_self_of_isND (h : ang.IsND): mk_dirline_dirline ang.start_dirLine ang.end_dirLine (start_dirLine_not_para_end_dirLine_of_value_ne_zero h) = ang :=
  Angle.ext (mk_dirline_dirline ang.start_dirLine ang.end_dirLine _) ang
    (Eq.symm <| inx_of_line_eq_inx (start_dirLine_not_para_end_dirLine_of_value_ne_zero h)
      ⟨ang.source_lies_on_start_dirLine, ang.source_lies_on_end_dirLine⟩) rfl rfl

theorem dvalue_eq_of_lies_on_line {A B : P} [PtNe A ang.source] [PtNe B ang.source] (ha : A LiesOn ang.start_ray.toLine) (hb : B LiesOn ang.end_ray.toLine) : ∡ A ang.source B = ang.dvalue := by
  show (SEG_nd ang.1 B).toProj -ᵥ (SEG_nd ang.1 A).toProj = ang.dvalue
  rw [ang.start_ray.toLine.toProj_eq_seg_nd_toProj_of_lies_on source_lies_on_start_dirLine ha]
  rw [ang.end_ray.toLine.toProj_eq_seg_nd_toProj_of_lies_on source_lies_on_end_dirLine hb]
  rfl

theorem dvalue_eq_of_lies_on_line_pt_pt {A B C D O : P} [_ha : PtNe A O] [_hb : PtNe B O] [_hc : PtNe C O] [_hd : PtNe D O] (hc : C LiesOn (LIN O A)) (hd : D LiesOn (LIN O B)) : ∡ C O D = ∡ A O B :=
  haveI : PtNe C (ANG A O B).source := _hc
  haveI : PtNe D (ANG A O B).source := _hd
  (ANG A O B).dvalue_eq_of_lies_on_line hc hd

end mk_compatibility

section cancel

variable {ang ang₁ ang₂ : Angle P}

theorem dir_eq_iff_of_value_eq (h : ang₁.value = ang₂.value) : ang₁.dir₁ = ang₂.dir₁ ↔ ang₁.dir₂ = ang₂.dir₂ := by
  apply (vadd_left_cancel_iff ang₁.value).symm.trans
  nth_rw 1 [value, vsub_vadd, h, value, vsub_vadd]

theorem eq_of_value_eq_of_dir₁_eq_of_source_eq (hs : ang₁.source = ang₂.source) (hr : ang₁.dir₁ = ang₂.dir₁) (hv : ang₁.value = ang₂.value) : ang₁ = ang₂ :=
  Angle.ext ang₁ ang₂ hs hr ((dir_eq_iff_of_value_eq hv).mp hr)

theorem eq_of_value_eq_of_start_ray_eq {ang₁ ang₂ : Angle P} (h : ang₁.start_ray = ang₂.start_ray) (hv : ang₁.value = ang₂.value) : ang₁ = ang₂ :=
  eq_of_value_eq_of_dir₁_eq_of_source_eq (congrArg Ray.source h) (congrArg Ray.toDir h) hv

theorem end_ray_eq_of_value_eq_of_start_ray_eq (h : ang₁.start_ray = ang₂.start_ray) (hv : ang₁.value = ang₂.value) : ang₁.end_ray = ang₂.end_ray :=
  congrArg end_ray (eq_of_value_eq_of_start_ray_eq h hv)

theorem eq_of_value_eq_of_dir₂_eq_of_source_eq (hs : ang₁.source = ang₂.source) (hr : ang₁.dir₂ = ang₂.dir₂) (hv : ang₁.value = ang₂.value) : ang₁ = ang₂ :=
  Angle.ext ang₁ ang₂ hs ((dir_eq_iff_of_value_eq hv).mpr hr) hr

theorem eq_of_value_eq_of_end_ray_eq {ang₁ ang₂ : Angle P} (h : ang₁.end_ray = ang₂.end_ray) (hv : ang₁.value = ang₂.value) : ang₁ = ang₂ :=
  eq_of_value_eq_of_dir₂_eq_of_source_eq (congrArg Ray.source h) (congrArg Ray.toDir h) hv

theorem eq_start_ray_of_eq_value_eq_end_ray (h : ang₁.end_ray = ang₂.end_ray) (hv : ang₁.value = ang₂.value) : ang₁.start_ray = ang₂.start_ray :=
  congrArg start_ray (eq_of_value_eq_of_end_ray_eq h hv)

end cancel

section angle_value

open AngValue

variable {ang ang₁ ang₂ : Angle P} {A O B : P} [PtNe A O] [PtNe B O]

theorem angDiff_eq_zero_of_same_dir {dir₁ dir₂ : Dir} (h : dir₁ = dir₂) : AngDiff dir₁ dir₂ = 0 :=
  vsub_eq_zero_iff_eq.mpr h.symm

theorem same_dir_iff_value_eq_zero : ang.dir₁ = ang.dir₂ ↔ ang.value = 0 :=
  ⟨angDiff_eq_zero_of_same_dir, fun h ↦ (eq_of_vsub_eq_zero h).symm⟩

@[simp]
theorem pt_pt_pt_value_eq_zero_of_same_pt (A O : P) [PtNe A O] : ∠ A O A = 0 :=
  vsub_self (VEC_nd O A).toDir

theorem value_eq_pi_of_eq_neg_dir (h : ang.dir₁ = - ang.dir₂) : ang.value = π :=
  (eq_neg_of_vsub_eq_pi ang.dir₂ ang.dir₁).mp (by rw [h, neg_neg])

theorem value_eq_of_dir_eq (h₁ : ang₁.dir₁ = ang₂.dir₁) (h₂ : ang₁.dir₂ = ang₂.dir₂) : ang₁.value = ang₂.value := by
  rw [value, value, h₁, h₂]

theorem value_eq_of_dir_eq_neg_dir (h₁ : ang₁.dir₁ = - ang₂.dir₁) (h₂ : ang₁.dir₂ = - ang₂.dir₂) : ang₁.value = ang₂.value := by
  rw [value, value, h₁, h₂, neg_vsub_right, neg_vsub_left, add_assoc, coe_pi_add_coe_pi, add_zero]

theorem value_eq_value_add_pi_of_dir_eq_neg_dir_of_dir_eq (h₁ : ang₁.dir₁ = ang₂.dir₁) (h₂ : ang₁.dir₂ = - ang₂.dir₂) : ang₁.value = ang₂.value + π := by
  rw [value, value, h₁, h₂, neg_vsub_left]

theorem value_eq_value_add_pi_of_dir_eq_of_dir_eq_neg_dir (h₁ : ang₁.dir₁ = - ang₂.dir₁) (h₂ : ang₁.dir₂ = ang₂.dir₂) : ang₁.value = ang₂.value + π := by
  rw [value, value, h₁, h₂, neg_vsub_right]

theorem value_add_value_eq_pi_of_isSuppl' (h₁ : ang₁.dir₁ = ang₂.dir₂) (h₂ : ang₁.dir₂ = - ang₂.dir₁) : ang₁.value + ang₂.value = π := by
  rw [value, value, h₂, h₁, neg_vsub_left, add_comm, ← add_assoc, vsub_add_vsub_cancel, vsub_self, zero_add]

theorem value_toReal_le_pi : ang.value.toReal ≤ π :=
  ang.value.toReal_le_pi

theorem neg_pi_lt_value_toReal : - π < ang.value.toReal :=
  ang.value.neg_pi_lt_toReal

theorem dir₂_eq_value_vadd_dir₁ : ang.dir₂ = ang.value +ᵥ ang.dir₁ :=
  (eq_vadd_iff_vsub_eq ang.dir₂ ang.value ang.dir₁).mpr rfl

theorem dvalue_eq_dAngDiff : ang.dvalue = DAngDiff ang.proj₁ ang.proj₂ := rfl

theorem dvalue_eq_vsub : ang.dvalue = ang.proj₂ -ᵥ ang.proj₁ := rfl

theorem dvalue_eq_zero_of_same_dir (h : ang.dir₁ = ang.dir₂) : ang.dvalue = 0 := by
  simp only [dvalue_eq_vsub, toProj_eq_of_eq h, vsub_self]

theorem dvalue_eq_pi_of_eq_neg_dir (h : ang.dir₁ = - ang.dir₂) : ang.dvalue = 0 := by
  simp only [dvalue_eq_vsub, toProj_eq_of_eq_neg h, vsub_self]

theorem dAngDiff_eq_zero_of_same_proj {proj₁ proj₂ : Proj} (h : proj₁ = proj₂) : DAngDiff proj₁ proj₂ = 0 :=
  vsub_eq_zero_iff_eq.mpr h.symm

theorem same_proj_iff_dvalue_eq_zero : ang.proj₁ = ang.proj₂ ↔ ang.dvalue = 0 :=
  eq_comm.trans vsub_eq_zero_iff_eq.symm

theorem same_proj_iff_isND : ang.proj₁ = ang.proj₂ ↔ ¬ ang.IsND :=
  same_proj_iff_dvalue_eq_zero.trans not_isND_iff_coe.symm

@[simp]
theorem pt_pt_pt_dvalue_eq_zero_of_same_pt (A O : P) [PtNe A O] : ∡ A O A = 0 :=
  vsub_self (VEC_nd O A).toProj

theorem dvalue_eq_of_dir_eq (h₁ : ang₁.dir₁ = ang₂.dir₁) (h₂ : ang₁.dir₂ = ang₂.dir₂) : ang₁.dvalue = ang₂.dvalue := by
  simp only [dvalue_eq_vsub, toProj_eq_of_eq h₁, toProj_eq_of_eq h₂]

theorem dvalue_eq_of_dir_eq_neg_dir (h₁ : ang₁.dir₁ = - ang₂.dir₁) (h₂ : ang₁.dir₂ = - ang₂.dir₂) : ang₁.dvalue = ang₂.dvalue := by
  simp only [dvalue_eq_vsub, toProj_eq_of_eq_neg h₁, toProj_eq_of_eq_neg h₂]

theorem dvalue_eq_dvalue_of_dir_eq_neg_dir_of_dir_eq (h₁ : ang₁.dir₁ = ang₂.dir₁) (h₂ : ang₁.dir₂ = - ang₂.dir₂) : ang₁.dvalue = ang₂.dvalue := by
  simp only [dvalue_eq_vsub, toProj_eq_of_eq h₁, toProj_eq_of_eq_neg h₂]

theorem dvalue_eq_dvalue_of_dir_eq_of_dir_eq_neg_dir (h₁ : ang₁.dir₁ = - ang₂.dir₁) (h₂ : ang₁.dir₂ = ang₂.dir₂) : ang₁.dvalue = ang₂.dvalue := by
  simp only [dvalue_eq_vsub, toProj_eq_of_eq h₂, toProj_eq_of_eq_neg h₁]

theorem dvalue_eq_dvalue_of_proj_eq_proj (h₁ : ang₁.proj₁ = ang₂.proj₁) (h₂ : ang₁.proj₂ = ang₂.proj₂) : ang₁.dvalue = ang₂.dvalue := by
  rw [dvalue_eq_dAngDiff, dvalue_eq_dAngDiff, h₁, h₂]

theorem dvalue_eq_neg_dvalue_of_isReverse' (h₁ : ang₁.proj₁ = ang₂.proj₂) (h₂ : ang₁.proj₂ = ang₂.proj₁) : ang₁.dvalue = - ang₂.dvalue := by
  apply (neg_vsub_eq_vsub_rev ang₁.proj₁ ang₁.proj₂).symm.trans
  rw [h₁, h₂]
  rfl

theorem dvalue_eq_neg_dvalue_of_isSuppl' (h₁ : ang₁.dir₁ = ang₂.dir₂) (h₂ : ang₁.dir₂ = - ang₂.dir₁) : ang₁.dvalue = - ang₂.dvalue :=
  dvalue_eq_neg_dvalue_of_isReverse' (Dir.toProj_eq_of_eq h₁) (Dir.toProj_eq_of_eq_neg h₂)

theorem dir_perp_iff_dvalue_eq_pi_div_two : ang.dir₁ ⟂ ang.dir₂ ↔ ang.dvalue = ∡[π / 2] := by
  apply (eq_vadd_iff_vsub_eq ang.proj₁ ∡[Real.pi / 2] ang.proj₂).trans
  nth_rw 1 [← AngDValue.neg_coe_pi_div_two, ← neg_vsub_eq_vsub_rev]
  exact neg_inj

theorem line_pt_pt_perp_iff_dvalue_eq_pi_div_two : LIN O A ⟂ LIN O B ↔ ∡ A O B = ∡[π / 2] :=
  (ANG A O B).dir_perp_iff_dvalue_eq_pi_div_two

theorem dir_perp_iff_isRt : ang.dir₁ ⟂ ang.dir₂ ↔ ang.IsRt :=
  dir_perp_iff_dvalue_eq_pi_div_two.trans isRt_iff_coe.symm

theorem line_pt_pt_perp_iff_isRt : LIN O A ⟂ LIN O B ↔ (ANG A O B).IsRt :=
  (ANG A O B).dir_perp_iff_isRt

theorem value_eq_pi_of_lies_int_seg_nd {A B C : P} [PtNe C A] (h : B LiesInt (SEG_nd A C)) : ∠ A B C h.2.symm h.3.symm = π :=
  value_eq_pi_of_eq_neg_dir ((SEG_nd A C).toDir_eq_neg_toDir_of_lies_int h)

theorem collinear_iff_dvalue_eq_zero : Collinear O A B ↔ ∡ A O B = 0 :=
  collinear_iff_toProj_eq_of_ptNe.trans (eq_comm.trans vsub_eq_zero_iff_eq.symm)

theorem collinear_iff_not_isND : Collinear O A B ↔ ¬ (ANG A O B).IsND :=
  collinear_iff_dvalue_eq_zero.trans not_isND_iff_coe.symm

theorem not_collinear_iff_isND : ¬ Collinear O A B ↔ (ANG A O B).IsND :=
  collinear_iff_not_isND.not.trans not_not

theorem collinear_of_angle_eq_zero (h : ∠ A O B = 0) : Collinear O A B :=
  collinear_iff_not_isND.mpr (not_isND_of_eq_zero h)

theorem collinear_of_angle_eq_pi (h : ∠ A O B = π ) : Collinear O A B :=
  collinear_iff_not_isND.mpr (not_isND_of_eq_pi h)

end angle_value

section sin_cos

open AngValue

variable {ang : Angle P}

theorem sin_pos_iff_isPos : 0 < sin ang.value ↔ ang.IsPos :=
  isPos_iff_sin_pos.symm

theorem sin_neg_iff_isNeg : sin ang.value < 0 ↔ ang.IsNeg :=
  isNeg_iff_sin_neg.symm

theorem sin_ne_zero_iff_isND : sin ang.value ≠ 0 ↔ ang.IsND :=
  isND_iff_sin_ne_zero.symm

theorem sin_eq_zero_iff_not_isND : sin ang.value = 0 ↔ ¬ ang.IsND :=
  not_isND_iff_sin_eq_zero.symm

theorem cos_pos_iff_isAcu : 0 < cos ang.value ↔ ang.IsAcu :=
  isAcu_iff_cos_pos.symm

theorem cos_neg_iff_isObt : cos ang.value < 0 ↔ ang.IsObt :=
  isObt_iff_cos_neg.symm

theorem cos_ne_zero_iff_not_isRt : cos ang.value ≠ 0 ↔ ¬ ang.IsRt :=
  not_isRt_iff_cos_ne_zero.symm

theorem cos_eq_zero_iff_isRt : cos ang.value = 0 ↔ ang.IsRt :=
  isRt_iff_cos_eq_zero.symm

end sin_cos

section inner

open AngValue

variable (A O B : P) [PtNe A O] [PtNe B O]

theorem inner_eq_dist_mul_cos : inner (VEC O A) (VEC O B) = dist O A * dist O B * cos (∠ A O B) := by
  rw [dist_comm, NormedAddTorsor.dist_eq_norm', dist_comm, NormedAddTorsor.dist_eq_norm']
  exact ((VEC_nd O A).norm_mul_cos (VEC_nd O B)).symm

theorem inner_pos_iff_isAcu : 0 < @inner ℝ _ _ (VEC O A) (VEC O B) ↔ (∠ A O B).IsAcu := by
  rw [inner_eq_dist_mul_cos A O B]
  exact (mul_pos_iff_of_pos_left (Real.mul_pos (SEG_nd O A).length_pos (SEG_nd O B).length_pos)).trans
    ((∠ A O B).isAcu_iff_cos_pos).symm

theorem inner_eq_zero_iff_isRt : @inner ℝ _ _ (VEC O A) (VEC O B) = 0 ↔ (∠ A O B).IsRt := by
  rw [inner_eq_dist_mul_cos A O B]
  refine' Iff.trans _ ((∠ A O B).isRt_iff_cos_eq_zero).symm
  exact smul_eq_zero_iff_right (ne_of_gt (Real.mul_pos (SEG_nd O A).length_pos (SEG_nd O B).length_pos))

theorem inner_neg_iff_isObt : @inner ℝ _ _ (VEC O A) (VEC O B) < 0 ↔ (∠ A O B).IsObt :=by
  rw [inner_eq_dist_mul_cos A O B]
  exact (smul_neg_iff_of_pos_left (Real.mul_pos (SEG_nd O A).length_pos (SEG_nd O B).length_pos)).trans
    ((∠ A O B).isObt_iff_cos_neg).symm

end inner

end Angle


/- theorem when angle > 0, IsInt means lies left of start ray + right of end ray; when angle < 0, ...  -/

/- Operations on oriented angles, such a additivity of the evaluation of oriented angles.  -/
/- theorem l1 l2 l3 add angle; sub angle -/
/- theorem O A B C add angle; sub angle-/

/- 90 degree -/

end EuclidGeom
