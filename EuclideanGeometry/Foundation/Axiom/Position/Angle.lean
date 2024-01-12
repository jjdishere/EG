import EuclideanGeometry.Foundation.Axiom.Linear.Parallel
import EuclideanGeometry.Foundation.Axiom.Basic.Angle

noncomputable section
open scoped Real

namespace EuclidGeom

def DirObj.AngDiff {α β} [DirObj α] [DirObj β] (F : α) (G : β) : AngValue := toDir G -ᵥ toDir F

/- Define values of oriented angles, in (-π, π], modulo 2 π. -/
/- Define oriented angles, ONLY taking in two rays starting at one point! And define ways to construct oriented angles, by given three points on the plane, and etc.  -/
@[ext]
structure Angle (P : Type _) [EuclideanPlane P] where
  start_ray : Ray P
  end_ray : Ray P
  source_eq_source : start_ray.source = end_ray.source

variable {P : Type _} [EuclideanPlane P]

namespace Angle

/-- Given vertex $O$ and two distinct points $A$ and $B$, this function returns the angle formed by rays $OA$ and $OB$. We use $\verb|ANG|$ to abbreviate $\verb|Angle.mk_pt_pt_pt|$. -/
def mk_pt_pt_pt (A O B : P) (h₁ : A ≠ O) (h₂ : B ≠ O): Angle P where
  start_ray := Ray.mk_pt_pt O A h₁
  end_ray := Ray.mk_pt_pt O B h₂
  source_eq_source := rfl

def mk_ray_pt (ray : Ray P) (A : P) (h : A ≠ ray.source) : Angle P where
  start_ray := ray
  end_ray := Ray.mk_pt_pt ray.source A h
  source_eq_source := rfl

def mk_dirline_dirline (l₁ l₂ : DirLine P) (h : ¬ l₁ ∥ l₂) : Angle P where
  start_ray := Ray.mk_pt_dirline (Line.inx l₁.toLine l₂.toLine (DirLine.not_para_toLine_of_not_para _ _ h) ) l₁ (Line.inx_lies_on_fst (DirLine.not_para_toLine_of_not_para _ _ h))
  end_ray := Ray.mk_pt_dirline (Line.inx l₁.toLine l₂.toLine (DirLine.not_para_toLine_of_not_para _ _ h) ) l₂ (Line.inx_lies_on_snd (DirLine.not_para_toLine_of_not_para _ _ h))
  source_eq_source := rfl

def value (A : Angle P) : AngValue := A.end_ray.toDir -ᵥ A.start_ray.toDir

abbrev dvalue (A : Angle P) : AngDValue := (A.value : AngDValue)

abbrev IsND (ang : Angle P) : Prop := ang.value.IsND

protected def source (ang : Angle P) : P := ang.start_ray.source

end Angle

theorem angle_value_eq_dir_angle (r r' : Ray P) (h : r.source = r'.source) : (Angle.mk r r' h).value = r'.toDir -ᵥ r.toDir := rfl

/-- The value of $\verb|Angle.mk_pt_pt_pt| A O B$. We use ∠ to abbreviate $\verb|Angle.value_of_angle_of_three_point_nd|$.-/
def value_of_angle_of_three_point_nd (A O B : P) (h₁ : A ≠ O) (h₂ : B ≠ O) : AngValue :=
  (Angle.mk_pt_pt_pt A O B h₁ h₂).value

def value_of_angle_of_two_ray_of_eq_source (start_ray end_ray : Ray P) (h : start_ray.source = end_ray.source) : AngValue := (Angle.mk start_ray end_ray h).value

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

namespace Angle

-- `should discuss this later, is there a better definition?` ite, dite is bitter to deal with
/- `What does it mean to be LiesIn a angle? when the angle < 0`, for now it is defined as the smaller side. and when angle = π, it is defined as the left side -/

protected def IsOn (p : P) (ang : Angle P) : Prop := by
  by_cases h : p = ang.source
  · exact True
  · let ray := Ray.mk_pt_pt ang.source p h
    let o₁ := Angle.mk ang.start_ray ray rfl
    let o₂ := Angle.mk ray ang.end_ray (ang.3)
    exact if ang.value.toReal ≥ 0 then (o₁.value.toReal ≥ 0 ∧ o₂.value.toReal ≥ 0) else (o₁.value.toReal ≤ 0 ∧ o₂.value.toReal ≤ 0)

protected def IsInt (p : P) (ang : Angle P) : Prop := by
  by_cases h : p = ang.source
  · exact False
  · let ray := Ray.mk_pt_pt ang.source p h
    let o₁ := Angle.mk ang.start_ray ray rfl
    let o₂ := Angle.mk ray ang.end_ray (ang.3)
    exact if ang.value.toReal ≥ 0 then (o₁.value.toReal > 0 ∧ o₂.value.toReal > 0) else (o₁.value.toReal < 0 ∧ o₂.value.toReal < 0)

protected theorem ison_of_isint {A : P} {ang : Angle P} : Angle.IsInt A ang → Angle.IsOn A ang := by
  unfold Angle.IsOn Angle.IsInt
  intro g
  by_cases h : A = ang.source
  · simp only [h, ge_iff_le, dite_true]
  · simp only [h, ge_iff_le, dite_false]
    simp only [h, ge_iff_le, gt_iff_lt, dite_false] at g
    by_cases f : 0 ≤ ang.value.toReal
    simp only [f, ite_true] at *
    constructor <;> linarith
    simp only [f, ite_false, not_false_eq_true] at *
    constructor <;> linarith


protected def carrier (ang : Angle P) : Set P := { p : P | Angle.IsOn p ang}

protected def interior (ang : Angle P) : Set P := { p : P | Angle.IsInt p ang }

instance : Interior (Angle P) P where
  interior := Angle.interior

/-
instance : IntFig Angle where
  carrier := Angle.carrier
  interior_subset_carrier _ _ := Angle.ison_of_isint
-/

end Angle

theorem eq_end_ray_of_eq_value_eq_start_ray {ang₁ ang₂ : Angle P} (h : ang₁.start_ray = ang₂.start_ray) (v : ang₁.value = ang₂.value) : ang₁.end_ray = ang₂.end_ray := by
  ext : 1
  rw [← ang₁.source_eq_source, ← ang₂.source_eq_source, (congrArg (fun z => z.source)) h]
  sorry
  /-
  let g := (congrArg (fun z => AngValue.toDir z)) v
  unfold Angle.value DirObj.AngDiff Dir.AngDiff at g
  simp only [div_toangvalue_eq_toangvalue_sub, sub_todir_eq_todir_div, toangvalue_todir_eq_self] at g
  rw [h] at g
  simp only [div_left_inj] at g
  exact g-/

theorem eq_start_ray_of_eq_value_eq_end_ray {ang₁ ang₂ : Angle P} (h : ang₁.end_ray = ang₂.end_ray) (v : ang₁.value = ang₂.value) : ang₁.start_ray = ang₂.start_ray := sorry

theorem eq_of_eq_value_eq_start_ray {ang₁ ang₂ : Angle P} (h : ang₁.start_ray = ang₂.start_ray) (v : ang₁.value = ang₂.value) : ang₁ = ang₂ := Angle.ext ang₁ ang₂ h (eq_end_ray_of_eq_value_eq_start_ray h v)

-- this section should talks about when different making methods make the same angle
section mk_compatibility

end mk_compatibility

/- theorem - π < angle.value, angle.value ≤ π,  -/

/- theorem when angle > 0, IsInt means lies left of start ray + right of end ray; when angle < 0, ...  -/

/- Operations on oriented angles, such a additivity of the evaluation of oriented angles.  -/
/- theorem l1 l2 l3 add angle; sub angle -/
/- theorem O A B C add angle; sub angle-/

/- 90 degree -/

end EuclidGeom
