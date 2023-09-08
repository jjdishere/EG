import EuclideanGeometry.Foundation.Axiom.Parallel

import EuclideanGeometry.Foundation.Axiom.Plane

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

def perpendicular (l₁ l₂: LinearObj P) : Prop := l₁.toProj = sorry

scoped infix : 50 "IsPerpendicularTo" => perpendicular
scoped infix : 50 "⟂" => perpendicular

namespace perpendicular

protected theorem irrefl (l : LinearObj P)  : ¬ (l ⟂ l) := by sorry

protected theorem symm (l₁ l₂ : LinearObj P) : (l₁ ⟂ l₂) → (l₂ ⟂ l₁) := sorry

end perpendicular

theorem parallel_of_perp_perp (l₁ l₂ l₃ : LinearObj P) : (l₁ ⟂ l₂) → (l₂ ⟂ l₃) → (l₁ ∥ l₃) := sorry 

theorem perp_of_parallel_perp (l₁ l₂ l₃ : LinearObj P) : (l₁ ∥ l₂) → (l₂ ⟂ l₃) → (l₁ ⟂ l₃) := sorry 

theorem perp_of_perp_parallel (l₁ l₂ l₃ : LinearObj P) : (l₁ ⟂ l₂) → (l₂ ∥ l₃) → (l₁ ⟂ l₃) := sorry 

end EuclidGeom