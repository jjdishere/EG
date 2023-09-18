import EuclideanGeometry.Foundation.Axiom.Triangle.Trigonometric

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

/- The relation of two triangle being similar to each other, i.e. each angle is equal to the corresponding angle.-/
def IsSim (tr₁ tr₂ : Triangle_nd P): Prop := tr₁.oangle₁.value = tr₂.oangle₁.value ∧ tr₁.oangle₂.value = tr₂.oangle₂.value ∧ tr₁.oangle₃.value = tr₂.oangle₃.value

/- The relation of two triangle being similar to each other, i.e. each angle is equal to the negative of corresponding angle.-/
def IsASim (tr₁ tr₂ : Triangle_nd P): Prop := tr₁.oangle₁.value = - tr₂.oangle₁.value ∧ tr₁.oangle₂.value = - tr₂.oangle₂.value ∧ tr₁.oangle₃.value = - tr₂.oangle₃.value

scoped infix :50 "IsSimTo" => IsSim
scoped infix :50 "IsASimTo" => IsASim
scoped infix :50 "∼" => IsSim
scoped infix :50 "∼ₐ" => IsASim

namespace IsSim

variable (tr₁ )
theorem ratio₁ : sorry := sorry



end IsSim

end EuclidGeom