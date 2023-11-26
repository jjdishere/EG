import EuclideanGeometry.Foundation.Axiom.Position.Angle

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem sin_pos_iff_angle_pos (A : Angle P) : 0 < Real.Angle.sin A.value ↔ A.value.IsPos := sorry

theorem end_ray_todir_rev_todir_of_ang_rev_ang {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = (ang₂.start_ray).reverse.toDir) (h : ang₁.value = ang₂.value) : ang₁.end_ray.toDir = (ang₂.end_ray).reverse.toDir := sorry

theorem start_ray_todir_rev_todir_of_ang_rev_ang {ang₁ ang₂ : Angle P} (hs : ang₁.end_ray.toDir = (ang₂.end_ray).reverse.toDir) (h : ang₁.value = ang₂.value) : ang₁.start_ray.toDir = (ang₂.start_ray).reverse.toDir := sorry

theorem angle_value_eq_angle (A : P) (ray : Ray P) (h : A ≠ ray.1) : (Angle.mk_ray_pt ray A h).value = Vec_nd.angle ray.2.toVec_nd (VEC_nd ray.source A h) := sorry

theorem ang_eq_ang_of_todir_rev_todir {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = - ang₂.start_ray.toDir) (he : ang₁.end_ray.toDir = - ang₂.end_ray.toDir) : ang₁.value = ang₂.value := sorry

theorem angle_eq_zero_or_pi_of_colinear {A O B : P} {h₁ : A ≠ O} {h₂ : B ≠ O} : colinear O A B → (∠ A O B h₁ h₂ = 0 ∨ ∠ A O B h₁ h₂ = π) := sorry

theorem angle_eq_zero_of_same_dir {A O : P} {h : A ≠ O} : ∠ A O A h h = 0 := sorry

theorem not_ispos_of_not_isnd {θ : AngValue} : ¬ θ.IsND → ¬ θ.IsPos := sorry

theorem not_isneg_of_not_isnd {θ : AngValue} : ¬ θ.IsND → ¬ θ.IsNeg := sorry

end EuclidGeom
