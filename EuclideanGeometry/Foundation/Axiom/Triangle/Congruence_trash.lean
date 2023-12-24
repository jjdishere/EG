import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem Triangle.IsCongr.unique_of_eq_eq {tr₁ tr₂ : Triangle P} (h : tr₁.IsCongr tr₂) (p₁ : tr₁.point₁ = tr₂.point₁) (p₂ : tr₁.point₂ = tr₂.point₂) [hne : PtNe tr₁.point₁ tr₁.point₂] : tr₁.point₃ = tr₂.point₃ := sorry

end EuclidGeom
