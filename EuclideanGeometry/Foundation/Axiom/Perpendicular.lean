import EuclideanGeometry.Foundation.Axiom.Parallel
import EuclideanGeometry.Foundation.Axiom.Plane

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

def perpendicular (l₁ l₂: LinearObj P) : Prop := l₁.toProj = l₂.toProj.perp

scoped infix : 50 "IsPerpendicularTo" => perpendicular
scoped infix : 50 "⟂" => perpendicular

namespace perpendicular

protected theorem irrefl (l : LinearObj P)  : ¬ (l ⟂ l) := by sorry

protected theorem symm (l₁ l₂ : LinearObj P) : (l₁ ⟂ l₂) → (l₂ ⟂ l₁) := sorry

end perpendicular

theorem parallel_of_perp_perp (l₁ l₂ l₃ : LinearObj P) : (l₁ ⟂ l₂) → (l₂ ⟂ l₃) → (l₁ ∥ l₃) := by
  unfold perpendicular parallel
  intro h₁ h₂
  rw [h₂] at h₁
  simp at h₁
  exact h₁

theorem perp_of_parallel_perp (l₁ l₂ l₃ : LinearObj P) : (l₁ ∥ l₂) → (l₂ ⟂ l₃) → (l₁ ⟂ l₃) := sorry 

theorem perp_of_perp_parallel (l₁ l₂ l₃ : LinearObj P) : (l₁ ⟂ l₂) → (l₂ ∥ l₃) → (l₁ ⟂ l₃) := sorry 

theorem toProj_ne_toProj_of_perp (l₁ l₂: LinearObj P) : (l₁ ⟂ l₂) → (l₁.toProj ≠ l₂.toProj) := sorry

section Perpendicular_foot

-- Now LinearObj is not finished. After we finished it, please rewrite the def of perp_foot by a better way
theorem perp_foot_preparation (A : P) (l : Line P) : l.toProj ≠ (Line.mk_pt_proj A (l.toProj.perp)).toProj := by
  sorry

def perp_foot (A : P) (l : Line P) : P := intersection_of_nonparallel_line (perp_foot_preparation A l)

-- Thing goes wrong when a merged version is used
-- def perp_foot' (A : P) (l : Line P) : P := intersection_of_nonparallel_line (l.toProj ≠ (Line.mk_pt_proj A (l.toProj.perp)).toProj)

-- theorem length_sq_eq_length_sq_add_length_sq_of_perp 

end Perpendicular_foot

end EuclidGeom