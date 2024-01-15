import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

noncomputable section
namespace EuclidGeom

open Line

variable {P : Type _} [EuclideanPlane P] {α β γ : Type*} [ProjObj α] [ProjObj β] [ProjObj γ]
  {l₁ : α} {l₂ : β} {l₃ : γ}

/-- This defines two projective objects to be perpendicular, i.e. their associated projective directions are perpendicular. -/
def perpendicular (l₁ : α) (l₂ : β) : Prop :=
  ProjObj.toProj l₁ = (ProjObj.toProj l₂).perp

/-- Abbreviate `perpendicular $l_1$ $l_2$` to `$l_1$ IsPerpendicularTo $l_2$` or `$l_1$ $\perp$ $l_2$`. -/
scoped infix : 50 " IsPerpendicularTo " => perpendicular

scoped infix : 50 " ⟂ " => perpendicular

section Notation
open Lean

syntax (name := perpendicularNotation) (priority := high) term:50 " ⟂ " term:51 : term

@[macro perpendicularNotation] def perpendicularNotationImpl : Macro
  | `($l:term ⟂ $r:term) => `(perpendicular $l $r)
  | _ => Macro.throwUnsupported

end Notation

namespace perpendicular

/-- A projective object $l$ is not perpendicular to itself. -/
@[simp]
protected theorem irrefl (l : α) : ¬ (l ⟂ l) :=
  sorry

protected theorem symm (h : l₁ ⟂ l₂) : (l₂ ⟂ l₁) := by
  rw [perpendicular, Proj.perp, h, Proj.perp, vadd_vadd]
  norm_cast
  simp

end perpendicular

section Perpendicular_and_parallel

/-- If $l_1$ is perpendicular to $l_2$ and $l_2$ is perpendicular to $l_3$, then $l_1$ is perpendicular to $l_3$. -/
theorem parallel_of_perp_perp (h₁ : l₁ ⟂ l₂) (h₂ : l₂ ⟂ l₃) : l₁ ∥ l₃ := by
  unfold perpendicular at h₂
  simp only [perpendicular, h₂, Proj.perp_perp] at h₁
  exact h₁

theorem perp_of_parallel_perp (h₁ : l₁ ∥ l₂) (h₂ : l₂ ⟂ l₃) : l₁ ⟂ l₃ := h₁.trans h₂

theorem perp_of_perp_parallel (h₁ : l₁ ⟂ l₂) (h₂ : l₂ ∥ l₃) : l₁ ⟂ l₃ := h₁.trans (congrArg Proj.perp h₂)

/-- If $l_1$ is perpendicular to $l_2$, then they have different projective direction. -/
theorem toProj_ne_toProj_of_perp (h : l₁ ⟂ l₂) : ProjObj.toProj l₁ ≠ ProjObj.toProj l₂ :=
  sorry

theorem not_parallel_of_perp (h : l₁ ⟂ l₂) : ¬ l₁ ∥ l₂ := toProj_ne_toProj_of_perp h

end Perpendicular_and_parallel

section Perpendicular_constructions

/-- Given a point $A$ and a line $l$, this function returns the line through $A$ perpendicular to $l$. -/
def perp_line (A : P) (l : Line P) := Line.mk_pt_proj A (l.toProj.perp)

@[simp]
theorem toProj_of_perp_line_eq_toProj_perp (A : P) (l : Line P) : (perp_line A l).toProj = l.toProj.perp :=
  proj_eq_of_mk_pt_proj A l.toProj.perp

/-- For a point $A$ and a line $l$, the line through $A$ perpendicular to $l$ constructed using `perp_line` is perpendicular to $l$. -/
theorem perp_line_perp (A : P) (l : Line P) : perp_line A l ⟂ l := toProj_of_perp_line_eq_toProj_perp A l

/-- For a point $A$ and a line $l$, the projective direction of $l$ is different from the projective direction of the line through $A$ perpendicular to $l$. -/
theorem toProj_ne_perp_toProj (A : P) (l : Line P) : l.toProj ≠ (perp_line A l).toProj :=
  Ne.trans_eq (perpendicular.irrefl l) (toProj_of_perp_line_eq_toProj_perp A l).symm

/-- For a point $A$ and a line $l$, this function returns the perpendicular foot from $A$ to $l$.  -/
def perp_foot (A : P) (l : Line P) : P := Line.inx l (perp_line A l) (toProj_ne_perp_toProj A l)

theorem perp_foot_lies_on_line (A : P) (l : Line P) : perp_foot A l LiesOn l := (Line.inx_is_inx _).1

/-- Given a point $A$ and a line $l$, the perpendicular foot from $A$ to $l$ is the same as $A$ if and only if $A$ lies on $l$. -/
theorem perp_foot_eq_self_iff_lies_on (A : P) (l : Line P) : perp_foot A l = A ↔ A LiesOn l := ⟨
  fun h ↦ Eq.mpr (h.symm ▸ Eq.refl (A LiesOn l)) (perp_foot_lies_on_line A l),
  fun h ↦ (inx_of_line_eq_inx _ ⟨h, (pt_lies_on_of_mk_pt_proj A (Proj.perp (Line.toProj l)))⟩).symm⟩

theorem perp_foot_ne_self_iff_not_lies_on (A : P) (l : Line P) : perp_foot A l ≠ A ↔ ¬ A LiesOn l :=
  (perp_foot_eq_self_iff_lies_on A l).not

theorem pt_ne_iff_not_lies_on_of_eq_perp_foot {A B : P} {l : Line P} (h : B = perp_foot A l) : B ≠ A ↔ ¬ A LiesOn l := by
  rw [h]
  exact (perp_foot_ne_self_iff_not_lies_on A l)

/-- If a point $A$ does not lie on a line $l$, then the line through $A$ and the perpendicular root from $A$ to $l$ is the line through $A$ perpendicular to $l$. -/
theorem line_of_self_perp_foot_eq_perp_line_of_not_lies_on {A : P} {l : Line P} (h : ¬ A LiesOn l) : LIN A (perp_foot A l) ((perp_foot_ne_self_iff_not_lies_on A l).2 h) = perp_line A l :=
  eq_line_of_pt_pt_of_ne (_h := ⟨(perp_foot_ne_self_iff_not_lies_on A l).2 h⟩) (pt_lies_on_of_mk_pt_proj A l.toProj.perp) (Line.inx_is_inx (toProj_ne_perp_toProj A l)).2

/-- If a point $A$ does on lie on a line $l$, the line through $A$ and the perpendicular roort from $A$ to $l$ is perpendicular to $l$. -/
theorem line_of_self_perp_foot_perp_line_of_not_lies_on {A : P} {l : Line P} (h : ¬ (A LiesOn l)) : LIN A (perp_foot A l) ((perp_foot_ne_self_iff_not_lies_on A l).2 h) ⟂ l :=
  (congrArg toProj (line_of_self_perp_foot_eq_perp_line_of_not_lies_on h)).trans (perp_line_perp A l)

/-- This function returns the distance from a point $A$ to a line $l$, as the distance between $A$ and the perpendicular root from $A$ to $l$. -/
def dist_pt_line (A : P) (l : Line P) := Seg.length (SEG A (perp_foot A l))

theorem dist_eq_zero_iff_lies_on (A : P) (l : Line P) : dist_pt_line A l = 0 ↔ A LiesOn l :=
  length_eq_zero_iff_deg.trans (perp_foot_eq_self_iff_lies_on A l)

-- Maybe the proof of this theorem should require the Pythagorean Theorem.
/-- Let $B$ be a point on a line $l$, then the distance from a point $A$ to $B$ is greater or equal to the distance from $A$ to $l$. -/
theorem dist_pt_line_shortest (A B : P) {l : Line P} (h : B LiesOn l) : dist A B ≥ dist_pt_line A l := sorry

end Perpendicular_constructions

end EuclidGeom
