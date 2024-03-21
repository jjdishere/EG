import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence

noncomputable section
namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

theorem Triangle.IsCongr.unique_of_eq_eq {tr₁ tr₂ : Triangle P} (h : tr₁.IsCongr tr₂) (p₁ : tr₁.point₁ = tr₂.point₁) (p₂ : tr₁.point₂ = tr₂.point₂) [hne : PtNe tr₁.point₁ tr₁.point₂] : tr₁.point₃ = tr₂.point₃ := sorry

theorem acongr_of_AAS_variant (tr_nd₁ tr_nd₂ : TriangleND P) (a₁ : tr_nd₁.angle₁.dvalue = - tr_nd₂.angle₁.dvalue) (a₂ : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value) (e₃ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length) : tr_nd₁ ≅ₐ tr_nd₂ := by sorry

theorem acongr_of_AAS' (tr_nd₁ tr_nd₂ : TriangleND P) (a₁ : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value) (a₂ : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value) (e₃ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length) : tr_nd₁ ≅ₐ tr_nd₂ := by sorry

theorem congr_of_perm_congr {tr_nd₁ tr_nd₂ : TriangleND P} (h : (TriangleND.perm_vertices tr_nd₁).IsCongr (TriangleND.perm_vertices tr_nd₂)) : tr_nd₁ ≅ tr_nd₂ := sorry

theorem acongr_of_perm_acongr {tr_nd₁ tr_nd₂ : TriangleND P} (h : (TriangleND.perm_vertices tr_nd₁).IsACongr (TriangleND.perm_vertices tr_nd₂)) : tr_nd₁ ≅ₐ tr_nd₂ := sorry

end EuclidGeom
