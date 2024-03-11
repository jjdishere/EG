import EuclideanGeometry.Foundation.Axiom.Triangle.Similarity

noncomputable section

namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

open TriangleND AngValue

theorem sim_of_AA' (tr₁ tr₂ : TriangleND P) (h₂ : tr₁.angle₂.dvalue = tr₂.angle₂.dvalue) (h₃ : tr₁.angle₃.value = tr₂.angle₃.value) : tr₁ ∼ tr₂ := sorry

theorem sim_of_AA_of_isRt (tr₁ tr₂ : TriangleND P) (h₁ : tr₁.IsRt) (h₂ : tr₂.IsRt) (h : tr₁.angle₂.dvalue = tr₂.angle₂.dvalue) : tr₁ ∼ tr₂ := by
  refine' IsSim.sim_iff_perm_sim.mpr (IsSim.sim_iff_perm_sim.mpr (sim_of_AA' _ _ _ _))
  · exact (isRt_iff_coe.mp h₁).trans (isRt_iff_coe.mp h₂).symm
  · exact eq_of_isAcu_of_coe_eq (angle₂_isAcu_of_isRt h₁) (angle₂_isAcu_of_isRt h₂) h

theorem asim_of_AA' (tr₁ tr₂ : TriangleND P) (h₂ : tr₁.angle₂.dvalue = - tr₂.angle₂.dvalue) (h₃ : tr₁.angle₃.value = - tr₂.angle₃.value) : tr₁ ∼ₐ tr₂ := sorry

theorem asim_of_AA_of_isRt (tr₁ tr₂ : TriangleND P) (h₁ : tr₁.IsRt) (h₂ : tr₂.IsRt) (h : tr₁.angle₂.dvalue = - tr₂.angle₂.dvalue) : tr₁ ∼ₐ tr₂ := by
  refine' IsASim.asim_iff_perm_asim.mpr (IsASim.asim_iff_perm_asim.mpr (asim_of_AA' _ _ _ _))
  · sorry
  · sorry

end EuclidGeom
