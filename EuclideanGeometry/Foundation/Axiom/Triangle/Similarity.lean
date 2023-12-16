import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] {tr₁ tr₂ tr₃ : TriangleND P}

open TriangleND

/- The relation of two triangle being similar to each other, i.e. each angle is equal to the corresponding angle.-/
structure IsSim (tr₁ tr₂ : TriangleND P) : Prop where intro ::
  angle₁ : tr₁.angle₁.value = tr₂.angle₁.value
  angle₂ : tr₁.angle₂.value = tr₂.angle₂.value
  angle₃ : tr₁.angle₃.value = tr₂.angle₃.value

/- The relation of two triangle being anti-similar to each other, i.e. each angle is equal to the negative of corresponding angle.-/
structure IsASim (tr₁ tr₂ : TriangleND P) : Prop where intro ::
  angle₁ : tr₁.angle₁.value = - tr₂.angle₁.value
  angle₂ : tr₁.angle₂.value = - tr₂.angle₂.value
  angle₃ : tr₁.angle₃.value = - tr₂.angle₃.value

namespace IsSim

protected theorem refl (tr : TriangleND P): IsSim tr tr where
  angle₁ := rfl
  angle₂ := rfl
  angle₃ := rfl

protected theorem symm (h : IsSim tr₁ tr₂) : IsSim tr₂ tr₁ := sorry

protected theorem trans (h₁ : IsSim tr₁ tr₂) (h₂ : IsSim tr₂ tr₃) : IsSim tr₁ tr₃ := sorry

instance instHasSim : HasSim (TriangleND P) where
  sim := IsSim
  refl := IsSim.refl
  trans := IsSim.trans
  symm := IsSim.symm

theorem perm_sim (h : IsSim tr₁ tr₂) : IsSim (perm_vertices tr₁) (perm_vertices tr₂) := sorry

theorem sim_iff_perm_sim : IsSim tr₁ tr₂ ↔ IsSim (perm_vertices tr₁) (perm_vertices tr₂) :=
  ⟨fun h ↦ h.perm_sim, fun h ↦ h.perm_sim.perm_sim⟩

theorem is_cclock_of_cclock (h : IsSim tr₁ tr₂) (cc : tr₁.is_cclock) : tr₂.is_cclock := sorry

def ratio (h : IsSim tr₁ tr₂) : ℝ := tr₁.edge₁.length / tr₂.edge₁.length

/- If $tr_1 ∼ tr_2$, then ... -/
variable (h : IsSim tr₁ tr₂)

theorem ratio₁ : h.ratio = tr₁.edge₁.length / tr₂.edge₁.length := rfl

theorem ratio₂ : h.ratio = tr₁.edge₂.length / tr₂.edge₂.length := sorry

theorem ratio₃ : h.ratio = tr₁.edge₃.length / tr₂.edge₃.length := sorry

theorem ratio₂₃ : tr₁.edge₂.length / tr₁.edge₃.length = tr₂.edge₂.length / tr₂.edge₃.length := sorry

theorem ratio₃₁ : tr₁.edge₃.length / tr₁.edge₁.length = tr₂.edge₃.length / tr₂.edge₁.length := sorry

theorem ratio₁₂ : tr₁.edge₁.length / tr₁.edge₂.length = tr₂.edge₁.length / tr₂.edge₂.length := sorry

-- The proof of this theorem will need to wait until the definition of area is completed.
theorem area : tr₁.area / tr₂.area = h.ratio * h.ratio := sorry

end IsSim

namespace IsASim

protected theorem symm (h : IsASim tr₁ tr₂) : IsASim tr₂ tr₁ := sorry

instance instHasASim : HasASim (TriangleND P) where
  asim := IsASim
  symm := IsASim.symm

theorem not_cclock_of_cclock (h : IsASim tr₁ tr₂) (cc : tr₁.is_cclock) : ¬ tr₂.is_cclock := sorry

def ratio (h : IsASim tr₁ tr₂) : ℝ := tr₁.edge₁.length / tr₂.edge₁.length

/- If $tr_1 ∼ tr_2$, then ... -/
variable (h : IsASim tr₁ tr₂)

theorem ratio₁ : h.ratio = tr₁.edge₁.length / tr₂.edge₁.length := rfl

theorem ratio₂ : h.ratio = tr₁.edge₂.length / tr₂.edge₂.length := sorry

theorem ratio₃ : h.ratio = tr₁.edge₃.length / tr₂.edge₃.length := sorry

theorem ratio₂₃ : tr₁.edge₂.length / tr₁.edge₃.length = tr₂.edge₂.length / tr₂.edge₃.length := sorry

theorem ratio₃₁ : tr₁.edge₃.length / tr₁.edge₁.length = tr₂.edge₃.length / tr₂.edge₁.length := sorry

theorem ratio₁₂ : tr₁.edge₁.length / tr₁.edge₂.length = tr₂.edge₁.length / tr₂.edge₂.length := sorry

end IsASim

theorem sim_of_asim_asim (h₁ : IsASim tr₁ tr₂) (h₂ : IsASim tr₁ tr₂) : IsSim tr₁ tr₂ := sorry

theorem asim_of_sim_asim (h₁ : IsSim tr₁ tr₂) (h₂ : IsASim tr₁ tr₂) : IsASim tr₁ tr₂ := sorry

theorem asim_of_asim_sim (h₁ : IsASim tr₁ tr₂) (h₂ : IsSim tr₁ tr₂) : IsASim tr₁ tr₂ := sorry

section simiarity_criterion

/- AA -/
theorem sim_of_AA (tr₁ tr₂ : TriangleND P) (h₂ : tr₁.angle₂.value = tr₂.angle₂.value) (h₃ : tr₁.angle₃.value = tr₂.angle₃.value) : tr₁ ∼ tr₂ := sorry

theorem asim_of_AA (tr₁ tr₂ : TriangleND P) (h₂ : tr₁.angle₂.value = - tr₂.angle₂.value) (h₃ : tr₁.angle₃.value = - tr₂.angle₃.value) : tr₁ ∼ₐ tr₂ := sorry

/- SAS -/
theorem sim_of_SAS (tr₁ tr₂ : TriangleND P) (e : tr₁.edge₂.length / tr₂.edge₂.length = tr₁.edge₃.length / tr₂.edge₃.length) (a : tr₁.angle₁.value = tr₂.angle₁.value): tr₁ ∼ tr₂ := sorry

theorem asim_of_SAS (tr₁ tr₂ : TriangleND P) (e : tr₁.edge₂.length / tr₂.edge₂.length = tr₁.edge₃.length / tr₂.edge₃.length) (a : tr₁.angle₁.value = - tr₂.angle₁.value): tr₁ ∼ₐ tr₂ := sorry

end simiarity_criterion

section congr_and_sim

theorem TriangleND.IsCongr.IsSim (h : tr₁.IsCongr tr₂) : IsSim tr₁ tr₂ where
  angle₁ := h.angle₁
  angle₂ := h.angle₂
  angle₃ := h.angle₃

theorem IsSim.congr_of_ratio_eq_one (h : IsSim tr₁ tr₂) (hr : h.ratio = 1) : tr₁.IsCongr tr₂ := sorry

theorem TriangleND.IsACongr.IsASim (h : tr₁.IsACongr tr₂) : IsASim tr₁ tr₂ where
  angle₁ := h.angle₁
  angle₂ := h.angle₂
  angle₃ := h.angle₃

theorem IsASim.acongr_of_ratio_eq_one (h : IsASim tr₁ tr₂) (hr : h.ratio = 1) : tr₁.IsACongr tr₂ := sorry

end congr_and_sim

end EuclidGeom
