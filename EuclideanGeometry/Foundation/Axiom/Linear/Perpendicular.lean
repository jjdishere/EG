import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

def perpendicular (l₁ l₂: LinearObj P) : Prop := l₁.toProj = l₂.toProj.perp

scoped infix : 50 "IsPerpendicularTo" => perpendicular
scoped infix : 50 "⟂" => perpendicular

namespace perpendicular

@[simp]
protected theorem irrefl (l : LinearObj P)  : ¬ (l ⟂ l) := by sorry

protected theorem symm (l₁ l₂ : LinearObj P) : (l₁ ⟂ l₂) → (l₂ ⟂ l₁) := by
  dsimp only [perpendicular] 
  dsimp only [Proj.perp]
  intro h
  have h0 : (Proj.I)*(Proj.I) = 1 := by 
    exact Proj.I_mul_I_eq_one_of_Proj
  rw[h,←mul_assoc,h0,one_mul]

end perpendicular

section Perpendicular_and_parallel

theorem parallel_of_perp_perp (l₁ l₂ l₃ : LinearObj P) : (l₁ ⟂ l₂) → (l₂ ⟂ l₃) → (l₁ ∥ l₃) := by
  unfold perpendicular parallel
  intro h₁ h₂
  rw [h₂] at h₁
  simp at h₁
  exact h₁

theorem perp_of_parallel_perp (l₁ l₂ l₃ : LinearObj P) : (l₁ ∥ l₂) → (l₂ ⟂ l₃) → (l₁ ⟂ l₃) := sorry 

theorem perp_of_perp_parallel (l₁ l₂ l₃ : LinearObj P) : (l₁ ⟂ l₂) → (l₂ ∥ l₃) → (l₁ ⟂ l₃) := sorry 

theorem toProj_ne_toProj_of_perp (l₁ l₂: LinearObj P) : (l₁ ⟂ l₂) → (l₁.toProj ≠ l₂.toProj) := sorry

end Perpendicular_and_parallel

section Perpendicular_constructions

def perp_line (A : P) (l : Line P) := Line.mk_pt_proj A (l.toProj.perp)

@[simp]
theorem toProj_of_perp_line_eq_toProj_perp (A : P) (l : Line P) : (perp_line A l).toProj = l.toProj.perp := (pt_lies_on_and_proj_eq_of_line_mk_pt_proj A _).2



theorem perp_foot_preparation (A : P) (l : Line P) : l.toProj ≠ (perp_line A l).toProj := by
  sorry

def perp_foot (A : P) (l : Line P) : P := intersection_of_nonparallel_line l (perp_line A l) (perp_foot_preparation A l)

def dist_pt_line (A : P) (l : Line P) := Seg.length (SEG A (perp_foot A l))

theorem perp_foot_eq_self_iff_lies_on (A : P) (l : Line P) : perp_foot A l = A ↔ A LiesOn l := by
  sorry

theorem line_of_self_perp_foot_eq_perp_line_of_not_lies_on (A : P) (l : Line P) (h : ¬ A LiesOn l) : LIN A (perp_foot A l) (by sorry) = perp_line A l := by
  sorry

theorem dist_eq_zero_iff_lies_on (A : P) (l : Line P) : dist_pt_line A l = 0 ↔ A LiesOn l := by
  sorry

end Perpendicular_constructions

end EuclidGeom