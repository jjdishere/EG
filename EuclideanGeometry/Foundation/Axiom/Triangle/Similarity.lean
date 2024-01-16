import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence
import EuclideanGeometry.Foundation.Axiom.Basic.Angle

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] {tr₁ tr₂ tr₃ : TriangleND P}

open TriangleND AngValue

/-- The relation of two triangle being similar to each other, i.e. each angle is equal to the corresponding angle.-/
structure IsSim (tr₁ tr₂ : TriangleND P) : Prop where intro ::
  angle₁ : tr₁.angle₁.value = tr₂.angle₁.value
  angle₂ : tr₁.angle₂.value = tr₂.angle₂.value
  angle₃ : tr₁.angle₃.value = tr₂.angle₃.value

/-- The relation of two triangle being anti-similar to each other, i.e. each angle is equal to the negative of corresponding angle.-/
structure IsASim (tr₁ tr₂ : TriangleND P) : Prop where intro ::
  angle₁ : tr₁.angle₁.value = - tr₂.angle₁.value
  angle₂ : tr₁.angle₂.value = - tr₂.angle₂.value
  angle₃ : tr₁.angle₃.value = - tr₂.angle₃.value

namespace IsSim

protected theorem refl (tr : TriangleND P): IsSim tr tr where
  angle₁ := rfl
  angle₂ := rfl
  angle₃ := rfl

protected theorem symm (h : IsSim tr₁ tr₂) : IsSim tr₂ tr₁ where
  angle₁ := h.angle₁.symm
  angle₂ := h.angle₂.symm
  angle₃ := h.angle₃.symm

protected theorem trans (h₁ : IsSim tr₁ tr₂) (h₂ : IsSim tr₂ tr₃) : IsSim tr₁ tr₃ where
  angle₁ := h₁.angle₁.trans h₂.angle₁
  angle₂ := h₁.angle₂.trans h₂.angle₂
  angle₃ := h₁.angle₃.trans h₂.angle₃

instance instHasSim : HasSim ( TriangleND P) where
  sim := IsSim
  refl := IsSim.refl
  trans := IsSim.trans
  symm := IsSim.symm

theorem perm_sim (h : IsSim tr₁ tr₂) : IsSim (perm_vertices tr₁) (perm_vertices tr₂) where
  angle₁ := h.2
  angle₂ := h.3
  angle₃ := h.1

theorem sim_iff_perm_sim : IsSim tr₁ tr₂ ↔ IsSim (perm_vertices tr₁) (perm_vertices tr₂) :=
  ⟨fun h ↦ h.perm_sim, fun h ↦ h.perm_sim.perm_sim⟩

theorem is_cclock_of_cclock (h : IsSim tr₁ tr₂) (cc : tr₁.is_cclock) : tr₂.is_cclock := by
  apply (angle₁_pos_iff_cclock tr₂).mpr
  simp only [<- h.1]
  apply (angle₁_pos_iff_cclock tr₁).mp
  exact cc

def ratio (_h : IsSim tr₁ tr₂) : ℝ := tr₁.edge₁.length / tr₂.edge₁.length

/- If $tr_1 ∼ tr_2$, then ... -/
variable (h : IsSim tr₁ tr₂)

theorem ratio₁ : h.ratio = tr₁.edge₁.length / tr₂.edge₁.length := rfl

theorem ratio₂ : h.ratio = tr₁.edge₂.length / tr₂.edge₂.length := by
  have sine₁ := Triangle.sine_rule₃ tr₁
  have sine₂ := Triangle.sine_rule₃ tr₂
  rw [h.1,h.2] at sine₁
  have s₁₂: tr₁.edge₁.length / tr₁.edge₂.length = (sin (Angle.value tr₂.angle₁)) / (sin (Angle.value tr₂.angle₂)) := by
    rw [mul_comm] at sine₁
    exact ((div_eq_div_iff  (sine_ne_zero_of_nd (perm_vertices tr₂)) (Seg.length_ne_zero_iff_nd.mpr tr₁.edge_nd₂.2).symm).mpr sine₁).symm
  have t₁₂: tr₂.edge₁.length / tr₂.edge₂.length = (sin (Angle.value tr₂.angle₁)) / (sin (Angle.value tr₂.angle₂)) := by
    rw [mul_comm] at sine₂
    exact ((div_eq_div_iff  (sine_ne_zero_of_nd (perm_vertices tr₂)) (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₂.2).symm).mpr sine₂).symm
  rw [<-t₁₂] at s₁₂
  unfold ratio
  have eq := mul_eq_mul_of_div_eq_div tr₁.edge₁.length tr₂.edge₁.length (Seg.length_ne_zero_iff_nd.mpr tr₁.edge_nd₂.2).symm (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₂.2).symm s₁₂
  apply (div_eq_div_iff (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₁.2).symm (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₂.2).symm).mpr
  have e₂ : (tr₂.edge_nd₂).1.length = tr₂.edge₂.length := rfl
  have e₁ : (tr₂.edge_nd₁).1.length = tr₂.edge₁.length := rfl
  have e₂' : (tr₁.edge_nd₂).1.length = tr₁.edge₂.length := rfl
  rw [e₂, e₂'] at eq
  simp only [e₂, e₁, eq, mul_comm]

theorem ratio₃ : h.ratio = tr₁.edge₃.length / tr₂.edge₃.length :=
  (ratio₂ h).trans (ratio₂ (perm_sim h))

theorem ratio₁₂ : tr₁.edge₁.length / tr₁.edge₂.length = tr₂.edge₁.length / tr₂.edge₂.length := by
  have sine₁ := Triangle.sine_rule₃ tr₁
  have sine₂ := Triangle.sine_rule₃ tr₂
  rw [h.1,h.2] at sine₁
  have s₁₂: tr₁.edge₁.length / tr₁.edge₂.length = (sin (Angle.value tr₂.angle₁)) / (sin (Angle.value tr₂.angle₂)) := by
    rw [mul_comm] at sine₁
    exact ((div_eq_div_iff  (sine_ne_zero_of_nd (perm_vertices tr₂)) (Seg.length_ne_zero_iff_nd.mpr tr₁.edge_nd₂.2).symm).mpr sine₁).symm
  have t₁₂: tr₂.edge₁.length / tr₂.edge₂.length = (sin (Angle.value tr₂.angle₁)) / (sin (Angle.value tr₂.angle₂)) := by
    rw [mul_comm] at sine₂
    exact ((div_eq_div_iff  (sine_ne_zero_of_nd (perm_vertices tr₂)) (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₂.2).symm).mpr sine₂).symm
  rw [<-t₁₂] at s₁₂
  exact s₁₂

theorem ratio₂₃ : tr₁.edge₂.length / tr₁.edge₃.length = tr₂.edge₂.length / tr₂.edge₃.length := by
  apply ratio₁₂ (perm_sim h)

theorem ratio₃₁ : tr₁.edge₃.length / tr₁.edge₁.length = tr₂.edge₃.length / tr₂.edge₁.length := by
  apply ratio₂₃ (perm_sim h)

theorem oarea : tr₁.oarea / tr₂.oarea = h.ratio ^ 2 := sorry

theorem area : tr₁.area / tr₂.area = h.ratio ^ 2 := sorry

end IsSim

namespace IsASim

protected theorem symm (h : IsASim tr₁ tr₂) : IsASim tr₂ tr₁ := by
  constructor
  simp only [h.1, neg_neg]
  simp only [h.2, neg_neg]
  simp only [h.3, neg_neg]

instance instHasASim : HasASim ( TriangleND P) where
  asim := IsASim
  symm := IsASim.symm

theorem not_cclock_of_cclock (h : IsASim tr₁ tr₂) (cc : tr₁.is_cclock) : ¬ tr₂.is_cclock := by
  have : tr₁.angle₁.value.IsPos := by
    apply (angle₁_pos_iff_cclock tr₁).mp
    exact cc
  rw [h.1] at this
  simp only [neg_isPos_iff_isNeg] at this
  apply (angle₁_neg_iff_not_cclock tr₂).mpr
  exact this

def ratio (_h : IsASim tr₁ tr₂) : ℝ := tr₁.edge₁.length / tr₂.edge₁.length

/- If $tr_1 ∼ tr_2$, then ... -/
variable (h : IsASim tr₁ tr₂)

theorem perm_asim (h : IsASim tr₁ tr₂) : IsASim (perm_vertices tr₁) (perm_vertices tr₂) where
  angle₁ := h.2
  angle₂ := h.3
  angle₃ := h.1

theorem ratio₁ : h.ratio = tr₁.edge₁.length / tr₂.edge₁.length := rfl

theorem ratio₂ : h.ratio = tr₁.edge₂.length / tr₂.edge₂.length := by
  have sine₁ := Triangle.sine_rule₃ tr₁
  have sine₂ := Triangle.sine_rule₃ tr₂
  rw [h.1,h.2] at sine₁
  have nd := sine_ne_zero_of_nd (flip_vertices (perm_vertices (perm_vertices tr₂)))
  have : -Angle.value (perm_vertices (perm_vertices tr₂)).angle₁ = Angle.value (flip_vertices (perm_vertices (perm_vertices tr₂))).angle₁ := by
    simp only [(angle_eq_neg_angle_of_flip_vertices (perm_vertices (perm_vertices tr₂))).1, neg_neg]
  rw [<-this,<-(angle_eq_angle_of_perm_vertices (perm_vertices tr₂)).2.2,<-(angle_eq_angle_of_perm_vertices  tr₂).2.1] at nd
  have s₁₂: tr₁.edge₁.length / tr₁.edge₂.length = (sin (- Angle.value tr₂.angle₁)) / (sin (-Angle.value tr₂.angle₂)) := by
    rw [mul_comm] at sine₁
    exact ((div_eq_div_iff nd (Seg.length_ne_zero_iff_nd.mpr tr₁.edge_nd₂.2).symm).mpr sine₁).symm
  have t₁₂: tr₂.edge₁.length / tr₂.edge₂.length = (sin (Angle.value tr₂.angle₁)) / (sin (Angle.value tr₂.angle₂)) := by
    rw [mul_comm] at sine₂
    exact ((div_eq_div_iff (sine_ne_zero_of_nd (perm_vertices tr₂)) (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₂.2).symm).mpr sine₂).symm
  rw [sin_neg (Angle.value tr₂.angle₁),sin_neg (Angle.value tr₂.angle₂),neg_div_neg_eq] at s₁₂
  rw [<-t₁₂] at s₁₂
  unfold ratio
  have eq := mul_eq_mul_of_div_eq_div tr₁.edge₁.length tr₂.edge₁.length (Seg.length_ne_zero_iff_nd.mpr tr₁.edge_nd₂.2).symm (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₂.2).symm s₁₂
  apply (div_eq_div_iff (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₁.2).symm (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₂.2).symm).mpr
  have e₂ : (tr₂.edge_nd₂).1.length = tr₂.edge₂.length := rfl
  have e₁ : (tr₂.edge_nd₁).1.length = tr₂.edge₁.length := rfl
  have e₂' : (tr₁.edge_nd₂).1.length = tr₁.edge₂.length := rfl
  rw [e₂, e₂'] at eq
  simp only [e₂, e₁, eq, mul_comm]

theorem ratio₃ : h.ratio = tr₁.edge₃.length / tr₂.edge₃.length :=
  (ratio₂ h).trans (ratio₂ (perm_asim h))

theorem ratio₁₂ : tr₁.edge₁.length / tr₁.edge₂.length = tr₂.edge₁.length / tr₂.edge₂.length := by
  have sine₁ := Triangle.sine_rule₃ tr₁
  have sine₂ := Triangle.sine_rule₃ tr₂
  rw [h.1,h.2] at sine₁
  have nd := sine_ne_zero_of_nd (flip_vertices (perm_vertices (perm_vertices tr₂)))
  have : -Angle.value (perm_vertices (perm_vertices tr₂)).angle₁ = Angle.value (flip_vertices (perm_vertices (perm_vertices tr₂))).angle₁ := by
    simp only [(angle_eq_neg_angle_of_flip_vertices (perm_vertices (perm_vertices tr₂))).1, neg_neg]
  rw [<-this,<-(angle_eq_angle_of_perm_vertices (perm_vertices tr₂)).2.2,<-(angle_eq_angle_of_perm_vertices  tr₂).2.1] at nd
  have s₁₂: tr₁.edge₁.length / tr₁.edge₂.length = (sin (- Angle.value tr₂.angle₁)) / (sin (-Angle.value tr₂.angle₂)) := by
    rw [mul_comm] at sine₁
    exact ((div_eq_div_iff nd (Seg.length_ne_zero_iff_nd.mpr tr₁.edge_nd₂.2).symm).mpr sine₁).symm
  have t₁₂: tr₂.edge₁.length / tr₂.edge₂.length = (sin (Angle.value tr₂.angle₁)) / (sin (Angle.value tr₂.angle₂)) := by
    rw [mul_comm] at sine₂
    exact ((div_eq_div_iff (sine_ne_zero_of_nd (perm_vertices tr₂)) (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₂.2).symm).mpr sine₂).symm
  rw [sin_neg (Angle.value tr₂.angle₁), sin_neg (Angle.value tr₂.angle₂), neg_div_neg_eq, ← t₁₂] at s₁₂
  exact s₁₂

theorem ratio₂₃ : tr₁.edge₂.length / tr₁.edge₃.length = tr₂.edge₂.length / tr₂.edge₃.length := by
  apply ratio₁₂ (perm_asim h)

theorem ratio₃₁ : tr₁.edge₃.length / tr₁.edge₁.length = tr₂.edge₃.length / tr₂.edge₁.length := by
  apply ratio₂₃ (perm_asim h)

theorem oarea : tr₁.oarea / tr₂.oarea = - h.ratio ^ 2 := sorry

theorem area : tr₁.area / tr₂.area = h.ratio ^ 2 := sorry

end IsASim

theorem sim_of_asim_asim (h₁ : IsASim tr₁ tr₂) (h₂ : IsASim tr₂ tr₃) : IsSim tr₁ tr₃ := by
  constructor
  simp only [h₁.1, h₂.1, neg_neg]
  simp only [h₁.2, h₂.2, neg_neg]
  simp only [h₁.3, h₂.3, neg_neg]

theorem asim_of_sim_asim (h₁ : IsSim tr₁ tr₂) (h₂ : IsASim tr₂ tr₃) : IsASim tr₁ tr₃ := by
  constructor
  simp only [h₁.1, h₂.1, neg_neg]
  simp only [h₁.2, h₂.2, neg_neg]
  simp only [h₁.3, h₂.3, neg_neg]

theorem asim_of_asim_sim (h₁ : IsASim tr₁ tr₂) (h₂ : IsSim tr₂ tr₃) : IsASim tr₁ tr₃ := by
  constructor
  simp only [h₁.1, h₂.1, neg_neg]
  simp only [h₁.2, h₂.2, neg_neg]
  simp only [h₁.3, h₂.3, neg_neg]

section simiarity_criterion

-- Add a version of mod π
/- AA -/
theorem sim_of_AA (tr₁ tr₂ : TriangleND P) (h₂ : tr₁.angle₂.value = tr₂.angle₂.value) (h₃ : tr₁.angle₃.value = tr₂.angle₃.value) : tr₁ ∼ tr₂ := by
  constructor
  by_cases cc : tr₁.is_cclock
  . have : tr₂.is_cclock := by
      have : tr₂.angle₂.value.IsPos := by
        simp only [<- h₂]
        apply (angle₂_pos_iff_cclock tr₁).mp
        exact cc
      apply (angle₂_pos_iff_cclock tr₂).mpr
      exact this
    have eq₂ := angle_sum_eq_pi_of_cclock tr₂ this
    simp only [<- angle_sum_eq_pi_of_cclock tr₁ cc, h₂, h₃, add_left_inj] at eq₂
    exact eq₂.symm
  . have : ¬ tr₂.is_cclock := by
      have : tr₂.angle₂.value.IsNeg := by
        simp only [<- h₂]
        apply (angle₂_neg_iff_not_cclock tr₁).mp
        exact cc
      apply (angle₂_neg_iff_not_cclock tr₂).mpr
      exact this
    have eq₂ := angle_sum_eq_neg_pi_of_clock tr₂ this
    simp only [<- angle_sum_eq_neg_pi_of_clock tr₁ cc, h₂, h₃, add_left_inj] at eq₂
    exact eq₂.symm
  exact h₂
  exact h₃

theorem asim_of_AA (tr₁ tr₂ : TriangleND P) (h₂ : tr₁.angle₂.value = - tr₂.angle₂.value) (h₃ : tr₁.angle₃.value = - tr₂.angle₃.value) : tr₁ ∼ₐ tr₂ := by
  constructor
  by_cases cc : tr₁.is_cclock
  . have : ¬ tr₂.is_cclock := by
      have : tr₁.angle₂.value.IsPos := by
        apply (angle₂_pos_iff_cclock tr₁).mp
        exact cc
      rw [h₂] at this
      simp only [neg_isPos_iff_isNeg] at this
      apply (angle₂_neg_iff_not_cclock tr₂).mpr
      exact this
    have eq₂ := angle_sum_eq_neg_pi_of_clock tr₂ this
    simp only [<- angle_sum_eq_pi_of_cclock tr₁ cc, h₂, h₃, neg_add_rev, neg_neg] at eq₂
    rw [add_comm,add_right_inj,add_comm,add_right_inj] at eq₂
    exact neg_eq_iff_eq_neg.mp (id eq₂.symm)
  . have : tr₂.is_cclock := by
      have : tr₁.angle₂.value.IsNeg := by
        apply (angle₂_neg_iff_not_cclock tr₁).mp
        exact cc
      rw [h₂] at this
      simp only [neg_isNeg_iff_isPos] at this
      apply (angle₂_pos_iff_cclock tr₂).mpr
      exact this
    have eq₂ := angle_sum_eq_pi_of_cclock tr₂ this
    have eq₁ := TriangleND.angle_sum_eq_neg_pi_of_clock tr₁ cc
    simp only [h₂, h₃, <- eq₂, neg_add_rev] at eq₁
    rw [add_comm,add_right_inj,add_comm,add_right_inj] at eq₁
    exact eq₁
  exact h₂
  exact h₃

/- SAS -/
theorem sim_of_SAS (tr₁ tr₂ : TriangleND P) (e : tr₁.edge₂.length / tr₂.edge₂.length = tr₁.edge₃.length / tr₂.edge₃.length) (a : tr₁.angle₁.value = tr₂.angle₁.value): tr₁ ∼ tr₂ := by
  have eq : tr₁.edge₂.length * tr₂.edge₃.length = tr₁.edge₃.length * tr₂.edge₂.length := by
    exact (div_eq_div_iff (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₂.2).symm (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₃.2).symm).mp e
  rw [mul_comm tr₁.edge₃.length  tr₂.edge₂.length] at eq
  have e' : tr₁.edge₂.length / tr₁.edge₃.length = tr₂.edge₂.length / tr₂.edge₃.length := (div_eq_div_iff (Seg.length_ne_zero_iff_nd.mpr tr₁.edge_nd₃.2).symm (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₃.2).symm).mpr eq
  have sine₁ := Triangle.sine_rule₁ tr₁
  have sine₂ := Triangle.sine_rule₁ tr₂
  have sine₁' : tr₁.edge₂.length * sin (Angle.value tr₁.angle₃) = sin (Angle.value tr₁.angle₂) *  tr₁.edge₃.length := by
    rw [sine₁, mul_comm]
  have sine₂' : tr₂.edge₂.length * sin (Angle.value tr₂.angle₃) = sin (Angle.value tr₂.angle₂) *  tr₂.edge₃.length := by
    rw [sine₂, mul_comm]
  have ne₁₃ : sin (Angle.value tr₁.angle₃) ≠ 0 := by
    simp only [(angle_eq_angle_of_perm_vertices tr₁).2.2, ne_eq,sine_ne_zero_of_nd,
        not_false_eq_true]
  have ne₂₃ : sin (Angle.value tr₂.angle₃) ≠ 0 := by
    simp only [(angle_eq_angle_of_perm_vertices tr₂).2.2,ne_eq, sine_ne_zero_of_nd,
        not_false_eq_true]
  have s₁₂ : tr₁.edge₂.length / tr₁.edge₃.length = sin (Angle.value tr₁.angle₂) / sin (Angle.value tr₁.angle₃) := (div_eq_div_iff (Seg.length_ne_zero_iff_nd.mpr tr₁.edge_nd₃.2).symm ne₁₃).mpr sine₁'
  have t₁₂ : tr₂.edge₂.length / tr₂.edge₃.length = sin (Angle.value tr₂.angle₂) / sin (Angle.value tr₂.angle₃) := (div_eq_div_iff (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₃.2).symm ne₂₃).mpr sine₂'
  rw [s₁₂,t₁₂] at e'
  have e'' := (div_eq_div_iff ne₁₃ ne₂₃).mp e'
  have summul := Real.cos_sub_cos ((Angle.value tr₁.angle₂).toReal + (Angle.value tr₂.angle₃).toReal) ((Angle.value tr₁.angle₂).toReal - (Angle.value tr₂.angle₃).toReal)
  field_simp at summul
  unfold toReal at summul
  have : Real.cos (Real.Angle.toReal (Angle.value tr₁.angle₂) + Real.Angle.toReal (Angle.value tr₂.angle₃)) = Real.Angle.cos (Real.Angle.toReal (Angle.value tr₁.angle₂) + Real.Angle.toReal (Angle.value tr₂.angle₃)) := rfl
  simp only [Real.Angle.coe_toReal] at this
  rw [this] at summul
  have : Real.cos (Real.Angle.toReal (Angle.value tr₁.angle₂) - Real.Angle.toReal (Angle.value tr₂.angle₃)) = Real.Angle.cos (Real.Angle.toReal (Angle.value tr₁.angle₂) - Real.Angle.toReal (Angle.value tr₂.angle₃)) := rfl
  simp only [Real.Angle.coe_toReal] at this
  rw [this] at summul
  rw [mul_assoc,e''] at summul
  have summul' := Real.cos_sub_cos ((Angle.value tr₂.angle₂).toReal + (Angle.value tr₁.angle₃).toReal) ((Angle.value tr₂.angle₂).toReal - (Angle.value tr₁.angle₃).toReal)
  field_simp at summul'
  unfold toReal at summul'
  have : Real.cos (Real.Angle.toReal (Angle.value tr₂.angle₂) + Real.Angle.toReal (Angle.value tr₁.angle₃)) = Real.Angle.cos (Real.Angle.toReal (Angle.value tr₂.angle₂) + Real.Angle.toReal (Angle.value tr₁.angle₃)) := rfl
  simp only [Real.Angle.coe_toReal] at this
  rw [this] at summul'
  have : Real.cos (Real.Angle.toReal (Angle.value tr₂.angle₂) - Real.Angle.toReal (Angle.value tr₁.angle₃)) = Real.Angle.cos (Real.Angle.toReal (Angle.value tr₂.angle₂) - Real.Angle.toReal (Angle.value tr₁.angle₃)) := rfl
  simp only [Real.Angle.coe_toReal] at this
  rw [this, mul_assoc, <-summul] at summul'
  have addeq := sum_of_other_angle_same_if_one_angle_same tr₁ tr₂ a
  have subeq : Angle.value tr₂.angle₂ - Angle.value tr₁.angle₃ = Angle.value tr₁.angle₂ - Angle.value tr₂.angle₃ := by
    rw [<-add_right_inj (Angle.value tr₁.angle₃ + Angle.value tr₂.angle₃)]
    simp only [add_add_sub_cancel, addeq]
    rw [add_comm] at addeq
    rw [addeq] ; abel
  rw [subeq,sub_left_inj,Real.Angle.cos_eq_iff_eq_or_eq_neg] at summul'
  rcases summul' with c|b
  . have : tr₁.angle₃.value = tr₂.angle₃.value := by
      have : tr₁.angle₂.value = tr₂.angle₂.value - tr₁.angle₃.value + tr₂.angle₃.value := by
        simp only [subeq, sub_add_cancel]
      simp only [this, sub_eq_add_neg, add_assoc, add_right_inj] at c
      have := (add_right_inj (Angle.value tr₁.angle₃)).mpr c
      simp only [add_neg_cancel_left] at this
      rw [<-two_smul ℕ (Angle.value tr₁.angle₃), <-two_smul ℕ (Angle.value tr₂.angle₃)] at this
      have := (two_zsmul_eq_iff).mp this
      rcases this with (e₁|e₂)
      . exact e₁
      have cc_eq := cclock_of_eq_angle tr₁ tr₂ a
      by_cases cc : tr₁.is_cclock
      . have pos₁ : tr₁.angle₃.value.IsPos := by
          apply (angle₃_pos_iff_cclock tr₁).mp
          exact cc
        rw [cc_eq] at cc
        have pos₂ : tr₂.angle₃.value.IsPos := by
          apply (angle₃_pos_iff_cclock tr₂).mp
          exact cc
        have npos₁ := add_pi_isNeg_iff_isPos.mpr pos₂
        rw [<-e₂] at npos₁
        exact (not_isPos_of_isNeg npos₁ pos₁).elim
      . have neg₁ : tr₁.angle₃.value.IsNeg := by
          apply (angle₃_neg_iff_not_cclock tr₁).mp
          exact cc
        rw [cc_eq] at cc
        have neg₂ : tr₂.angle₃.value.IsNeg := by
          apply (angle₃_neg_iff_not_cclock tr₂).mp
          exact cc
        have nneg₁ := add_pi_isPos_iff_isNeg.mpr neg₂
        rw [<-e₂] at nneg₁
        exact (not_isNeg_of_isPos nneg₁ neg₁).elim
    have e₂ : Angle.value tr₁.angle₂ = Angle.value tr₂.angle₂ := by
      have sum_eq := sum_of_other_angle_same_if_one_angle_same tr₁ tr₂ a
      simp only [this, add_left_inj] at sum_eq
      exact sum_eq
    exact ⟨a,e₂,this⟩
  have eq_zero : Angle.value tr₂.angle₂ + Angle.value tr₁.angle₃ + Angle.value tr₁.angle₂ + Angle.value tr₂.angle₃ = 0 := by
    rw [b, neg_add_rev, neg_add_cancel_right, add_left_neg]
  have eq_zero' : (Angle.value tr₁.angle₂ + Angle.value tr₁.angle₃) + (Angle.value tr₂.angle₂ + Angle.value tr₂.angle₃) = 0 := by
    rw [<-eq_zero] ; abel
  by_cases cc : tr₁.is_cclock
  . have eq_pi : Angle.value tr₁.angle₂ + Angle.value tr₁.angle₃ = π - Angle.value tr₁.angle₁ := by
      rw [<-angle_sum_eq_pi_of_cclock tr₁ cc] ; abel
    have eq_pi' : Angle.value tr₂.angle₂ + Angle.value tr₂.angle₃ = π - Angle.value tr₂.angle₁ := by
      rw [cclock_of_eq_angle tr₁ tr₂ a] at cc
      rw [<-angle_sum_eq_pi_of_cclock tr₂ cc] ; abel
    rw [eq_pi, eq_pi',a] at eq_zero'
    have : tr₂.angle₁.value + tr₂.angle₁.value = π + π := by
      rw [<-add_zero (Angle.value tr₂.angle₁ + Angle.value tr₂.angle₁), <-eq_zero']
      abel
    rw [<-two_smul ℕ (Angle.value tr₂.angle₁),<-two_smul ℕ _] at this
    rw [two_nsmul_coe_pi] at this
    have nd := two_nsmul_eq_zero_iff_not_isND.mp this
    rw [cclock_of_eq_angle tr₁ tr₂ a] at cc
    exfalso
    apply nd
    apply isND_iff_isPos_or_isNeg.mpr
    left
    apply (angle₁_pos_iff_cclock tr₂).mp
    exact cc
  have eq_pi : Angle.value tr₁.angle₂ + Angle.value tr₁.angle₃ = - π - Angle.value tr₁.angle₁ := by
      rw [<-angle_sum_eq_neg_pi_of_clock tr₁ cc] ; abel
  have eq_pi' : Angle.value tr₂.angle₂ + Angle.value tr₂.angle₃ = - π - Angle.value tr₂.angle₁ := by
    rw [cclock_of_eq_angle tr₁ tr₂ a] at cc
    rw [<-angle_sum_eq_neg_pi_of_clock tr₂ cc] ; abel
  rw [eq_pi, eq_pi',a] at eq_zero'
  have : tr₂.angle₁.value + tr₂.angle₁.value =- π + - π := by
      rw [<-add_zero (Angle.value tr₂.angle₁ + Angle.value tr₂.angle₁), <-eq_zero']
      abel
  rw [<-two_smul ℕ (Angle.value tr₂.angle₁),<-two_smul ℕ _] at this
  rw [neg_coe_pi,two_nsmul_coe_pi] at this
  have nd := two_nsmul_eq_zero_iff_not_isND.mp this
  rw [cclock_of_eq_angle tr₁ tr₂ a] at cc
  exfalso
  apply nd
  apply isND_iff_isPos_or_isNeg.mpr
  right
  apply (angle₁_neg_iff_not_cclock tr₂).mp
  exact cc

theorem asim_of_SAS (tr₁ tr₂ : TriangleND P) (e : tr₁.edge₂.length / tr₂.edge₂.length = tr₁.edge₃.length / tr₂.edge₃.length) (a : tr₁.angle₁.value = - tr₂.angle₁.value): tr₁ ∼ₐ tr₂ := by
  have eq : tr₁.edge₂.length * tr₂.edge₃.length = tr₁.edge₃.length * tr₂.edge₂.length := by
    exact (div_eq_div_iff (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₂.2).symm (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₃.2).symm).mp e
  rw [mul_comm tr₁.edge₃.length  tr₂.edge₂.length] at eq
  have e' : tr₁.edge₂.length / tr₁.edge₃.length = tr₂.edge₂.length / tr₂.edge₃.length := (div_eq_div_iff (Seg.length_ne_zero_iff_nd.mpr tr₁.edge_nd₃.2).symm (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₃.2).symm).mpr eq
  have sine₁ := Triangle.sine_rule₁ tr₁
  have sine₂ := Triangle.sine_rule₁ tr₂
  have sine₁' : tr₁.edge₂.length * sin (Angle.value tr₁.angle₃) = sin (Angle.value tr₁.angle₂) *  tr₁.edge₃.length := by
    rw [sine₁, mul_comm]
  have sine₂' : tr₂.edge₂.length * sin (Angle.value tr₂.angle₃) = sin (Angle.value tr₂.angle₂) *  tr₂.edge₃.length := by
    rw [sine₂, mul_comm]
  have ne₁₃ : sin (Angle.value tr₁.angle₃) ≠ 0 := by
    simp only [(angle_eq_angle_of_perm_vertices tr₁).2.2, ne_eq,sine_ne_zero_of_nd, not_false_eq_true]
  have ne₂₃ : sin (Angle.value tr₂.angle₃) ≠ 0 := by
    simp only [(angle_eq_angle_of_perm_vertices tr₂).2.2,ne_eq, sine_ne_zero_of_nd, not_false_eq_true]
  have s₁₂ : tr₁.edge₂.length / tr₁.edge₃.length = sin (Angle.value tr₁.angle₂) / sin (Angle.value tr₁.angle₃) := (div_eq_div_iff (Seg.length_ne_zero_iff_nd.mpr tr₁.edge_nd₃.2).symm ne₁₃).mpr  sine₁'
  have t₁₂ : tr₂.edge₂.length / tr₂.edge₃.length = sin (Angle.value tr₂.angle₂) / sin (Angle.value tr₂.angle₃) := (div_eq_div_iff (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₃.2).symm ne₂₃).mpr  sine₂'
  rw [s₁₂,t₁₂] at e'
  have e'' := (div_eq_div_iff ne₁₃ ne₂₃).mp e'
  have summul := Real.cos_sub_cos ((Angle.value tr₁.angle₂).toReal + (Angle.value tr₂.angle₃).toReal) ((Angle.value tr₁.angle₂).toReal - (Angle.value tr₂.angle₃).toReal)
  field_simp at summul
  unfold toReal at summul
  have : Real.cos (Real.Angle.toReal (Angle.value tr₁.angle₂) + Real.Angle.toReal (Angle.value tr₂.angle₃)) = Real.Angle.cos (Real.Angle.toReal (Angle.value tr₁.angle₂) + Real.Angle.toReal (Angle.value tr₂.angle₃)) := rfl
  simp only [Real.Angle.coe_toReal] at this
  rw [this] at summul
  have : Real.cos (Real.Angle.toReal (Angle.value tr₁.angle₂) - Real.Angle.toReal (Angle.value tr₂.angle₃)) = Real.Angle.cos (Real.Angle.toReal (Angle.value tr₁.angle₂) - Real.Angle.toReal (Angle.value tr₂.angle₃)) := rfl
  simp only [Real.Angle.coe_toReal] at this
  rw [this] at summul
  rw [mul_assoc,e''] at summul
  have summul' := Real.cos_sub_cos ((Angle.value tr₂.angle₂).toReal + (Angle.value tr₁.angle₃).toReal) ((Angle.value tr₂.angle₂).toReal - (Angle.value tr₁.angle₃).toReal)
  field_simp at summul'
  unfold toReal at summul'
  have : Real.cos (Real.Angle.toReal (Angle.value tr₂.angle₂) + Real.Angle.toReal (Angle.value tr₁.angle₃)) = Real.Angle.cos (Real.Angle.toReal (Angle.value tr₂.angle₂) + Real.Angle.toReal (Angle.value tr₁.angle₃)) := rfl
  simp only [Real.Angle.coe_toReal] at this
  rw [this] at summul'
  have : Real.cos (Real.Angle.toReal (Angle.value tr₂.angle₂) - Real.Angle.toReal (Angle.value tr₁.angle₃)) = Real.Angle.cos (Real.Angle.toReal (Angle.value tr₂.angle₂) - Real.Angle.toReal (Angle.value tr₁.angle₃)) := rfl
  simp only [Real.Angle.coe_toReal] at this
  rw [this, mul_assoc, <-summul] at summul'
  have addeq := sum_of_other_angle_same_neg_if_one_angle_same_neg tr₁ tr₂ a
  have subeq : Angle.value tr₂.angle₂ + Angle.value tr₁.angle₃ = - (Angle.value tr₁.angle₂ + Angle.value tr₂.angle₃) := by
    rw [<-add_left_inj (Angle.value tr₁.angle₂) , add_assoc, add_comm (Angle.value tr₁.angle₃),addeq]
    abel
  have coseq : Real.Angle.cos (Angle.value tr₂.angle₂ + Angle.value tr₁.angle₃) = Real.Angle.cos (Angle.value tr₁.angle₂ + Angle.value tr₂.angle₃) := by
    rw [subeq]
    exact cos_eq_iff_coe_eq_or_eq_neg.mpr (.inr rfl)
  rw [coseq, sub_right_inj, Real.Angle.cos_eq_iff_eq_or_eq_neg] at summul'
  rcases summul' with c | b
  . by_cases cc : tr₁.is_cclock
    . have eq_zero : (Angle.value tr₂.angle₂ + Angle.value tr₂.angle₃) - (Angle.value tr₁.angle₂ + Angle.value tr₁.angle₃)  = 0 := by
        rw [<-add_sub,<-sub_sub,<-neg_neg (Angle.value tr₂.angle₃ - Angle.value tr₁.angle₂),neg_sub,<-c]
        abel
      have eq_pi : Angle.value tr₁.angle₂ + Angle.value tr₁.angle₃ = π - Angle.value tr₁.angle₁ := by
        rw [<-angle_sum_eq_pi_of_cclock tr₁ cc] ; abel
      have eq_pi' : Angle.value tr₂.angle₂ + Angle.value tr₂.angle₃ = - π - Angle.value tr₂.angle₁ := by
        rw [clock_of_eq_neg_angle tr₁ tr₂ a] at cc
        rw [<-angle_sum_eq_neg_pi_of_clock tr₂ cc] ; abel
      simp only [eq_pi', neg_coe_pi, eq_pi, a, sub_neg_eq_add] at eq_zero
      rw [<-sub_sub] at eq_zero
      have comm : ∠[Real.pi] - Angle.value tr₂.angle₁ - ∠[Real.pi] - Angle.value tr₂.angle₁ = ∠[Real.pi] - ∠[Real.pi] - Angle.value tr₂.angle₁ - Angle.value tr₂.angle₁ := by abel
      simp only [comm,sub_self, zero_sub] at eq_zero
      rw [sub_eq_add_neg,<-neg_add] at eq_zero
      rw [<-two_smul ℕ (Angle.value tr₂.angle₁),neg_eq_zero] at eq_zero
      have nd := two_nsmul_eq_zero_iff_not_isND.mp eq_zero
      rw [clock_of_eq_neg_angle tr₁ tr₂ a] at cc
      exfalso
      apply nd
      apply isND_iff_isPos_or_isNeg.mpr
      right
      apply (angle₁_neg_iff_not_cclock tr₂).mp
      exact cc
    . have eq_zero : (Angle.value tr₂.angle₂ + Angle.value tr₂.angle₃) - (Angle.value tr₁.angle₂ + Angle.value tr₁.angle₃)  = 0 := by
        rw [<-add_sub,<-sub_sub,<-neg_neg (Angle.value tr₂.angle₃ - Angle.value tr₁.angle₂),neg_sub,<-c]
        abel
      have eq_pi : Angle.value tr₁.angle₂ + Angle.value tr₁.angle₃ = - π - Angle.value tr₁.angle₁ := by
        rw [<-angle_sum_eq_neg_pi_of_clock tr₁ cc] ; abel
      have eq_pi' : Angle.value tr₂.angle₂ + Angle.value tr₂.angle₃ = π - Angle.value tr₂.angle₁ := by
        rw [clock_of_eq_neg_angle tr₁ tr₂ a] at cc
        push_neg at cc
        rw [<-angle_sum_eq_pi_of_cclock tr₂ cc] ; abel
      simp only [eq_pi', neg_coe_pi, eq_pi, a, sub_neg_eq_add] at eq_zero
      rw [<-sub_sub] at eq_zero
      have comm : ∠[Real.pi] - Angle.value tr₂.angle₁ - ∠[Real.pi] - Angle.value tr₂.angle₁ = ∠[Real.pi] - ∠[Real.pi] - Angle.value tr₂.angle₁ - Angle.value tr₂.angle₁ := by abel
      simp only [comm,sub_self, zero_sub] at eq_zero
      rw [sub_eq_add_neg,<-neg_add] at eq_zero
      rw [<-two_smul ℕ (Angle.value tr₂.angle₁),neg_eq_zero] at eq_zero
      have nd := two_nsmul_eq_zero_iff_not_isND.mp eq_zero
      rw [clock_of_eq_neg_angle tr₁ tr₂ a] at cc
      push_neg at cc
      exfalso
      apply nd
      apply isND_iff_isPos_or_isNeg.mpr
      left
      apply (angle₁_pos_iff_cclock tr₂).mp
      exact cc
  . have : tr₁.angle₃.value = - tr₂.angle₃.value := by
      have : tr₁.angle₂.value = - (tr₂.angle₂.value + tr₂.angle₃.value) - tr₁.angle₃.value := by
        rw [<-addeq] ; abel
      simp only [sub_eq_add_neg, this, neg_add_rev, add_assoc, neg_neg] at b
      rw [<-add_assoc, add_comm (Angle.value tr₂.angle₃ + Angle.value tr₁.angle₃),add_assoc,add_right_inj,<-add_assoc,<-add_left_inj (Angle.value tr₁.angle₃)] at b
      simp only [add_left_neg] at b
      rw [<-two_smul ℕ (Angle.value tr₂.angle₃),add_assoc,<-two_smul ℕ (Angle.value tr₁.angle₃)] at b
      have b' := eq_neg_of_add_eq_zero_right b.symm
      have : - ((2 : ℕ)  • Angle.value tr₂.angle₃) = 2 • (-Angle.value tr₂.angle₃) := by simp only [smul_neg]
      rw [this] at b'
      rcases (two_zsmul_eq_iff).mp b' with e₁ | e₂
      . exact e₁
      have cc_eq := clock_of_eq_neg_angle tr₁ tr₂ a
      by_cases cc : tr₁.is_cclock
      . have pos₁ : tr₁.angle₃.value.IsPos := by
          apply (angle₃_pos_iff_cclock tr₁).mp
          exact cc
        rw [cc_eq] at cc
        have pos₂ : tr₂.angle₃.value.IsNeg := by
          apply (angle₃_neg_iff_not_cclock tr₂).mp
          exact cc
        have pos₃ : (-tr₂.angle₃.value).IsPos := by simp only [neg_isPos_iff_isNeg,
          pos₂]
        have npos₁ := add_pi_isNeg_iff_isPos.mpr pos₃
        rw [<-e₂] at npos₁
        exact ((not_isPos_of_isNeg npos₁) pos₁).elim
      . have neg₁ : tr₁.angle₃.value.IsNeg := by
          apply (angle₃_neg_iff_not_cclock tr₁).mp
          exact cc
        rw [cc_eq] at cc
        push_neg at cc
        have neg₂ : tr₂.angle₃.value.IsPos := by
          apply (angle₃_pos_iff_cclock tr₂).mp
          exact cc
        have neg₃ : (-tr₂.angle₃.value).IsNeg := by simp only [neg_isNeg_iff_isPos,
          neg₂]
        have nneg₁ := add_pi_isPos_iff_isNeg.mpr neg₃
        rw [<-e₂] at nneg₁
        exact (not_isNeg_of_isPos nneg₁ neg₁).elim
    have e₂ : Angle.value tr₁.angle₂ = - Angle.value tr₂.angle₂ := by
      have sum_eq := sum_of_other_angle_same_neg_if_one_angle_same_neg tr₁ tr₂ a
      simp only [this, neg_add_rev,add_comm, add_left_inj] at sum_eq
      exact sum_eq
    exact ⟨a, e₂, this⟩

end simiarity_criterion

section congr_and_sim

theorem TriangleND.IsCongr.IsSim (h : tr₁.IsCongr tr₂) : IsSim tr₁ tr₂ where
  angle₁ := h.angle₁
  angle₂ := h.angle₂
  angle₃ := h.angle₃

theorem IsSim.congr_of_ratio_eq_one (h : IsSim tr₁ tr₂) (hr : h.ratio = 1) : tr₁.IsCongr tr₂ := by
  constructor
  have := ratio₁ h
  rw [hr] at this
  exact (div_eq_one_iff_eq (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₁.2).symm).mp this.symm
  have := ratio₂ h
  rw [hr] at this
  exact (div_eq_one_iff_eq (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₂.2).symm).mp this.symm
  have := ratio₃ h
  rw [hr] at this
  exact (div_eq_one_iff_eq (Seg.length_ne_zero_iff_nd.mpr tr₂.edge_nd₃.2).symm).mp this.symm
  exact h.1
  exact h.2
  exact h.3

theorem TriangleND.IsACongr.IsASim (h : tr₁.IsACongr tr₂) : IsASim tr₁ tr₂ where
  angle₁ := h.angle₁
  angle₂ := h.angle₂
  angle₃ := h.angle₃

theorem IsASim.acongr_of_ratio_eq_one (h : IsASim tr₁ tr₂) (hr : h.ratio = 1) : tr₁.IsACongr tr₂ := by
  constructor
  have := ratio₁ h
  simp only [hr] at this
  exact eq_of_div_eq_one this.symm
  have := ratio₂ h
  simp only [hr] at this
  exact eq_of_div_eq_one this.symm
  have := ratio₃ h
  simp only [hr] at this
  exact eq_of_div_eq_one this.symm
  exact h.1
  exact h.2
  exact h.3

end congr_and_sim

end EuclidGeom
