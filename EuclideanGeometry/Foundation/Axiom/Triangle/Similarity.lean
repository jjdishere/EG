import EuclideanGeometry.Foundation.Axiom.Triangle.Trigonometric

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

/- The relation of two triangle being similar to each other, i.e. each angle is equal to the corresponding angle.-/
def IsSim (tr₁ tr₂ : Triangle_nd P): Prop := tr₁.angle₁.value = tr₂.angle₁.value ∧ tr₁.angle₂.value = tr₂.angle₂.value ∧ tr₁.angle₃.value = tr₂.angle₃.value

/- The relation of two triangle being anti-similar to each other, i.e. each angle is equal to the negative of corresponding angle.-/
def IsASim (tr₁ tr₂ : Triangle_nd P): Prop := tr₁.angle₁.value = - tr₂.angle₁.value ∧ tr₁.angle₂.value = - tr₂.angle₂.value ∧ tr₁.angle₃.value = - tr₂.angle₃.value

/- The similarity relation is denoted by infix "IsSimTo"-/
scoped infix :50 "IsSimTo" => IsSim
/- The anti-similarity relation is denoted by infix "IsASimTo"-/
scoped infix :50 "IsASimTo" => IsASim
/- The similarity relation is denoted by infix $\sim$-/
scoped infix :50 "∼" => IsSim
/- The anti-similarity relation is denoted by infix $\sim_a$-/
scoped infix :50 "∼ₐ" => IsASim

namespace IsSim

variable (tr₁ tr₂ : Triangle_nd P) (h : tr₁ ∼ tr₂)

/- If $tr_1 ∼ tr_2$, then ... -/
theorem ratio₁ : tr₁.1.edge₂.length / tr₁.1.edge₃.length = tr₂.1.edge₂.length / tr₂.1.edge₃.length := sorry

theorem ratio₂ : tr₁.1.edge₃.length / tr₁.1.edge₁.length = tr₂.1.edge₃.length / tr₂.1.edge₁.length := sorry

theorem ratio₃ : tr₁.1.edge₁.length / tr₁.1.edge₂.length = tr₂.1.edge₁.length / tr₂.1.edge₂.length := sorry

end IsSim

namespace IsASim

variable (tr₁ tr₂ : Triangle_nd P) (h : tr₁ ∼ₐ tr₂)

/- If $tr_1 ∼ tr_2$, then ... -/
theorem ratio₁ : tr₁.1.edge₂.length / tr₁.1.edge₃.length = tr₂.1.edge₂.length / tr₂.1.edge₃.length := sorry

theorem ratio₂ : tr₁.1.edge₃.length / tr₁.1.edge₁.length = tr₂.1.edge₃.length / tr₂.1.edge₁.length := sorry

theorem ratio₃ : tr₁.1.edge₁.length / tr₁.1.edge₂.length = tr₂.1.edge₁.length / tr₂.1.edge₂.length := sorry

end IsASim

section simiarity_criterion

/- AA -/
theorem sim_of_AA (tr₁ tr₂ : Triangle_nd P) (h₂ : tr₁.angle₂.value = tr₂.angle₂.value) (h₃ : tr₁.angle₃.value = tr₂.angle₃.value) : tr₁ ∼ tr₂ := sorry 

theorem asim_of_AA (tr₁ tr₂ : Triangle_nd P) (h₂ : tr₁.angle₂.value = - tr₂.angle₂.value) (h₃ : tr₁.angle₃.value = - tr₂.angle₃.value) : tr₁ ∼ₐ tr₂ := sorry

end simiarity_criterion

end EuclidGeom