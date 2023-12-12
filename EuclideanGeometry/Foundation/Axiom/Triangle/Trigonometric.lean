import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular

noncomputable section
namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

open Real AngValue

namespace Triangle

-- Cosine rule : for a nontrivial triangle ABC, BC^2 = AB^2 + AC^2 - 2 * AB * AC * cos ANG BAC.

theorem cosine_rule' (A B C : P) (hab : B ≠ A) (hac : C ≠ A) :
    2 * (‖VEC_nd A B hab‖ * ‖VEC_nd A C hac‖ *
      cos (VecND.angle (VEC_nd A B hab) (VEC_nd A C hac))) =
      Seg.length (SEG A B) ^ 2 + Seg.length (SEG A C) ^ 2 - Seg.length (SEG B C) ^ 2 := by
  rw [VecND.norm_mul_cos, length_sq_eq_inner_toVec_toVec,
    length_sq_eq_inner_toVec_toVec, length_sq_eq_inner_toVec_toVec, seg_toVec_eq_vec,
    seg_toVec_eq_vec, seg_toVec_eq_vec, ← vec_sub_vec A B C, inner_sub_sub_self,
    ← InnerProductSpace.conj_symm, IsROrC.conj_to_real]
  ring_nf
  rw [real_inner_comm (VEC A C), mul_two]
  rfl

theorem cosine_rule (tr_nd : TriangleND P) : 2 * (tr_nd.edge₃.length * tr_nd.edge₂.length * cos tr_nd.angle₁.value) = tr_nd.edge₃.length ^ 2 + tr_nd.edge₂.length ^ 2 - tr_nd.edge₁.length ^ 2 := by
  let A := tr_nd.1.point₁
  let B := tr_nd.1.point₂
  let C := tr_nd.1.point₃
  let h₃ := cosine_rule' A B C (tr_nd.nontriv₃) (Ne.symm tr_nd.nontriv₂)
  have h₄ : ‖VEC_nd A C (Ne.symm tr_nd.nontriv₂)‖ = ‖VEC_nd C A (tr_nd.nontriv₂)‖
  · simp_rw [VecND.mkPtPt, ← neg_vec A C]
    simp
  have h₅ : Seg.length (SEG A C) = Seg.length (SEG C A)
  · unfold Seg.length Seg.toVec
    rw [← neg_vec (SEG A C).target (SEG A C).source]
    simp only [norm_neg, Complex.norm_eq_abs]
  rw [h₄, h₅] at h₃
  simp only [ne_eq, Nat.cast_ofNat] at h₃
  exact h₃

theorem cosine_rule'' (tr_nd : TriangleND P) : tr_nd.edge₁.length = (tr_nd.edge₃.length ^ 2 + tr_nd.edge₂.length ^ 2 -  2 * (tr_nd.edge₃.length * tr_nd.edge₂.length * cos tr_nd.angle₁.value)) ^ (1/2) := by sorry

-- Sine rule (but only for counterclockwise triangle here, or we need some absolute values)
-- Should we reformulate it without circle?
-- theorem side_eq_cradius_times_sine_angle (tr_nd : TriangleND P) (cclock : tr_nd.is_cclock) : tr_nd.1.edge₁.length = 2 * (tr_nd.toCir).radius * sin (tr_nd.angle₁.value) ∧ tr_nd.1.edge₂.length = 2 * (tr_nd.toCir).radius * sin (tr_nd.angle₂.value) ∧ tr_nd.1.edge₃.length = 2 * (tr_nd.toCir).radius * sin (tr_nd.angle₃.value):= sorry

theorem sine_rule₁ (tr_nd : TriangleND P) : tr_nd.edge₂.length * sin tr_nd.angle₃.value = tr_nd.edge₃.length * sin tr_nd.angle₂.value := sorry

theorem sine_rule₂ (tr_nd : TriangleND P) : tr_nd.edge₁.length * sin tr_nd.angle₃.value = tr_nd.edge₃.length * sin tr_nd.angle₁.value := sorry

theorem sine_rule₃ (tr_nd : TriangleND P) : tr_nd.edge₂.length * sin tr_nd.angle₁.value = tr_nd.edge₁.length * sin tr_nd.angle₂.value := sorry
end Triangle

section Pythagoras

theorem Pythagoras_of_ne_ne_perp {A B C : P} (hab : B ≠ A) (hac : C ≠ A) (h : (SegND.toProj ⟨SEG A B, hab⟩).perp = (SegND.toProj ⟨SEG A C, hac⟩)) : (SEG A B).length ^ 2 + (SEG A C).length ^ 2 = (SEG B C).length ^ 2 := by

  sorry

theorem Pythagoras_of_perp_foot (A B : P) {l : Line P} (h : B LiesOn l) : (SEG A (perp_foot A l)).length ^ 2 + (SEG B (perp_foot A l)).length ^ 2 = (SEG A B).length ^ 2 := by
  sorry

--(tr_nd : TriangleND P) : 2 * (tr_nd.1.edge₃.length * tr_nd.1.edge₂.length * cos tr_nd.angle₁.value) = tr_nd.1.edge₃.length ^ 2 + tr_nd.1.edge₂.length ^ 2 - tr_nd.1.edge₁.length ^ 2 := by
  --let A := tr_nd.1.point₁
  --let B := tr_nd.1.point₂
  --let C := tr_nd.1.point₃

/-- Given ▵ A B C with ∠ B A C = π / 2, A B ^ 2 + A C ^ 2 = B C ^ 2, namely (SEG A B).length ^ 2 + (SEG A C).length ^ 2 = (SEG B C).length ^ 2. -/
theorem Pythagoras_of_right_triangle_non_trivial (A B C : P) {hnd : ¬ colinear A B C} (right_triangle: ∠ B A C (ne_of_not_colinear hnd).2.2 (ne_of_not_colinear hnd).2.1.symm = (π / 2 : ℝ)) : (SEG A B).length ^ 2 + (SEG A C).length ^ 2 = (SEG B C).length ^ 2 := by
  have h : cos (∠ B A C (ne_of_not_colinear hnd).2.2 (ne_of_not_colinear hnd).2.1.symm) = 0
  · rw [right_triangle]
    simp
  have eq : 2 * ((SEG A B).length * (SEG A C).length * cos (∠ B A C (ne_of_not_colinear hnd).2.2 (ne_of_not_colinear hnd).2.1.symm)) = (SEG A B).length ^ 2 + (SEG A C).length ^ 2 - (SEG B C).length ^ 2
  · --cos rule
    sorry
  simp [h, eq_sub_iff_add_eq] at eq
  exact eq.symm

theorem Pythagoras_of_tr_nd (tr_nd : TriangleND P) (h : tr_nd.angle₁.value = ↑ (π / 2) ∨ tr_nd.angle₁.value =↑ (- π /2)) : tr_nd.edge₂.length ^ 2 + tr_nd.edge₃.length ^ 2 = tr_nd.edge₁.length ^2 := sorry

end Pythagoras

end EuclidGeom
