import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Circle.Basic
-- should we exclude circle in this file? this file is supposed to be used to establish congruent.

noncomputable section
namespace EuclidGeom
variable {P : Type _} [EuclideanPlane P]

namespace Triangle

-- Cosine rule : for a nontrivial triangle ABC, BC^2 = AB^2 + AC^2 - 2 * AB * AC * cos ∠ BAC.

theorem cosine_rule' (A B C : P) (hab : B ≠ A) (hac : C ≠ A) : 2 * (Vec.norm (⟨VEC A B, (ne_iff_vec_ne_zero A B).mp hab⟩ : Vec_nd) * Vec.norm (⟨VEC A C, (ne_iff_vec_ne_zero A C).mp hac⟩ : Vec_nd) * Real.cos (Vec_nd.angle ⟨VEC A B, (ne_iff_vec_ne_zero A B).mp hab⟩ ⟨VEC A C, (ne_iff_vec_ne_zero A C).mp hac⟩)) = Seg.length (SEG A B) ^ 2 + Seg.length (SEG A C) ^ 2 - Seg.length (SEG B C) ^ 2 := by
  rw [norm_mul_norm_mul_cos_angle_eq_inner_of_Vec_nd, Seg.length_sq_eq_inner_toVec_toVec (SEG A B), Seg.length_sq_eq_inner_toVec_toVec (SEG A C), Seg.length_sq_eq_inner_toVec_toVec (SEG B C), Seg.seg_toVec_eq_vec, Seg.seg_toVec_eq_vec, Seg.seg_toVec_eq_vec, ← vec_sub_vec A B C, Vec.InnerProductSpace.Core.inner_sub_sub_self, ← Vec.InnerProductSpace.Core.conj_symm (VEC A B) (VEC A C), IsROrC.conj_to_real]
  ring

theorem cosine_rule (tr_nd : Triangle_nd P) : 2 * (tr_nd.1.edge₃.length * tr_nd.1.edge₂.length * Real.cos tr_nd.angle₁) = tr_nd.1.edge₃.length ^ 2 + tr_nd.1.edge₂.length ^ 2 - tr_nd.1.edge₁.length ^ 2 := by
  let A := tr_nd.1.point₁
  let B := tr_nd.1.point₂
  let C := tr_nd.1.point₃
  sorry


-- Sine rule (but only for counterclockwise triangle here, or we need some absolute values)
-- Should we reformulate it without circle?
-- theorem side_eq_cradius_times_sine_angle (tr_nd : Triangle_nd P) (cclock : tr_nd.is_cclock) : tr_nd.1.edge₁.length = 2 * (tr_nd.toCir).radius * Real.sin (tr_nd.angle₁) ∧ tr_nd.1.edge₂.length = 2 * (tr_nd.toCir).radius * Real.sin (tr_nd.angle₂) ∧ tr_nd.1.edge₃.length = 2 * (tr_nd.toCir).radius * Real.sin (tr_nd.angle₃):= sorry

end Triangle

section Pythagoras

theorem Pythagoras_of_ne_ne_perp {A B C : P} (hab : B ≠ A) (hac : C ≠ A) (h : (Seg_nd.toProj ⟨SEG A B, hab⟩).perp = (Seg_nd.toProj ⟨SEG A C, hac⟩)) : (SEG A B).length ^ 2 + (SEG A C).length ^ 2 = (SEG B C).length ^ 2 := by
  sorry

theorem Pythagoras_of_perp_foot (A B : P) {l : Line P} (h : B LiesOn l) : (SEG A (perp_foot A l)).length ^ 2 + (SEG B (perp_foot A l)).length ^ 2 = (SEG A B).length ^ 2 := by
  sorry

end Pythagoras

end EuclidGeom