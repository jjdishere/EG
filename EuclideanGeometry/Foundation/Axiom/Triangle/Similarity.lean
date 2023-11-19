import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_ex
import EuclideanGeometry.Foundation.Axiom.Triangle.Trigonometric

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

open Triangle_nd

/- The relation of two triangle being similar to each other, i.e. each angle is equal to the corresponding angle.-/
structure IsSim (tr₁ tr₂ : Triangle_nd P) : Prop where intro ::
  angle₁ : tr₁.angle₁.value = tr₂.angle₁.value
  angle₂ : tr₁.angle₂.value = tr₂.angle₂.value
  angle₃ : tr₁.angle₃.value = tr₂.angle₃.value

/- The relation of two triangle being anti-similar to each other, i.e. each angle is equal to the negative of corresponding angle.-/
structure IsASim (tr₁ tr₂ : Triangle_nd P) : Prop where intro ::
  angle₁ : tr₁.angle₁.value = - tr₂.angle₁.value
  angle₂ : tr₁.angle₂.value = - tr₂.angle₂.value
  angle₃ : tr₁.angle₃.value = - tr₂.angle₃.value

namespace IsSim

variable {tr₁ tr₂ tr₃ : Triangle_nd P}

protected theorem refl (tr : Triangle_nd P): IsSim tr tr := sorry

protected theorem symm (h : IsSim tr₁ tr₂) : IsSim tr₂ tr₁ := sorry

protected theorem trans (h₁ : IsSim tr₁ tr₂) (h₂ : IsSim tr₂ tr₃) : IsSim tr₁ tr₃ := sorry

instance instHasSim : HasSim (Triangle_nd P) where
  sim := IsSim
  refl := IsSim.refl
  trans := IsSim.trans
  symm := IsSim.symm

theorem perm_sim (h : IsSim tr₁ tr₂) : (perm_vertices tr₁) ∼ (perm_vertices tr₂) := sorry

theorem sim_iff_perm_sim : tr₁ ∼ tr₂ ↔ (perm_vertices tr₁) ∼ (perm_vertices tr₂) :=
  ⟨fun h ↦ h.perm_sim, fun h ↦ h.perm_sim.perm_sim⟩

/- If $tr_1 ∼ tr_2$, then ... -/
def ratio (h : IsSim tr₁ tr₂) : ℝ := tr₁.edge₁.length / tr₂.edge₁.length

variable (h : IsSim tr₁ tr₂)

theorem ratio₁ : h.ratio = tr₁.edge₁.length / tr₂.edge₁.length := rfl

theorem ratio₂ : h.ratio = tr₁.edge₂.length / tr₂.edge₂.length := sorry

theorem ratio₃ : h.ratio = tr₁.edge₃.length / tr₂.edge₃.length := sorry

theorem ratio₂₃ : tr₁.edge₂.length / tr₁.edge₃.length = tr₂.edge₂.length / tr₂.edge₃.length := sorry

theorem ratio₃₁ : tr₁.edge₃.length / tr₁.edge₁.length = tr₂.edge₃.length / tr₂.edge₁.length := sorry

theorem ratio₁₂ : tr₁.edge₁.length / tr₁.edge₂.length = tr₂.edge₁.length / tr₂.edge₂.length := sorry

end IsSim

namespace IsASim

variable {tr₁ tr₂ : Triangle_nd P}

protected theorem symm (h : IsASim tr₁ tr₂) : IsASim tr₂ tr₁ := sorry

instance instHasASim : HasASim (Triangle_nd P) where
  asim := IsASim
  symm := IsASim.symm

variable (h : IsASim tr₁ tr₂)

/- If $tr_1 ∼ tr_2$, then ... -/
def ratio (h : IsASim tr₁ tr₂) : ℝ := tr₁.edge₁.length / tr₂.edge₁.length

variable (h : IsSim tr₁ tr₂)

theorem ratio₁ : h.ratio = tr₁.edge₁.length / tr₂.edge₁.length := rfl

theorem ratio₂ : h.ratio = tr₁.edge₂.length / tr₂.edge₂.length := sorry

theorem ratio₃ : h.ratio = tr₁.edge₃.length / tr₂.edge₃.length := sorry

theorem ratio₂₃ : tr₁.edge₂.length / tr₁.edge₃.length = tr₂.edge₂.length / tr₂.edge₃.length := sorry

theorem ratio₃₁ : tr₁.edge₃.length / tr₁.edge₁.length = tr₂.edge₃.length / tr₂.edge₁.length := sorry

theorem ratio₁₂ : tr₁.edge₁.length / tr₁.edge₂.length = tr₂.edge₁.length / tr₂.edge₂.length := sorry

end IsASim

section simiarity_criterion

/- AA -/
theorem sim_of_AA (tr₁ tr₂ : Triangle_nd P) (h₂ : tr₁.angle₂.value = tr₂.angle₂.value) (h₃ : tr₁.angle₃.value = tr₂.angle₃.value) : tr₁ ∼ tr₂ := sorry

theorem asim_of_AA (tr₁ tr₂ : Triangle_nd P) (h₂ : tr₁.angle₂.value = - tr₂.angle₂.value) (h₃ : tr₁.angle₃.value = - tr₂.angle₃.value) : tr₁ ∼ₐ tr₂ := sorry

/- SAS -/
theorem sim_of_SAS (tr₁ tr₂ : Triangle_nd P) (e : tr₁.edge₂.length / tr₂.edge₂.length = tr₁.edge₃.length / tr₂.edge₃.length) (a : tr₁.angle₁.value = tr₂.angle₁.value): tr₁ ∼ tr₂ := sorry

theorem asim_of_SAS (tr₁ tr₂ : Triangle_nd P) (e : tr₁.edge₂.length / tr₂.edge₂.length = tr₁.edge₃.length / tr₂.edge₃.length) (a : tr₁.angle₁.value = - tr₂.angle₁.value): tr₁ ∼ₐ tr₂ := sorry

end simiarity_criterion

end EuclidGeom
