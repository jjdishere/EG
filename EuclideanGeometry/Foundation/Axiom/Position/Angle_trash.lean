import EuclideanGeometry.Foundation.Axiom.Position.Angle

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem sin_pos_iff_angle_pos (A : Angle P) : 0 < Real.sin A.value ↔ (0 < A.value ∧ A.value < π) := sorry

theorem end_ray_todir_rev_todir_of_ang_rev_ang {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = (ang₂.start_ray).reverse.toDir) (h : ang₁.value = ang₂.value) : ang₁.end_ray.toDir = (ang₂.end_ray).reverse.toDir := sorry

theorem start_ray_todir_rev_todir_of_ang_rev_ang {ang₁ ang₂ : Angle P} (hs : ang₁.end_ray.toDir = (ang₂.end_ray).reverse.toDir) (h : ang₁.value = ang₂.value) : ang₁.start_ray.toDir = (ang₂.start_ray).reverse.toDir := sorry

theorem angle_value_eq_angle (A : P) (ray : Ray P) (h : A ≠ ray.1) : (Angle.mk_ray_pt ray A h).value = Vec_nd.angle ray.2.toVec_nd (VEC_nd ray.source A h) := sorry

theorem angle_slide_vertice (A A' B B' O: P) (h₁ : A ≠ O) (h₂ : B ≠ O) (h₁' : A' ≠ O) (h₂' : B' ≠ O) (LiesInt1 : A' LiesInt (RAY O A h₁) )  (LiesInt2 :  B' LiesInt (RAY O B h₂) ) : ANG A O B h₁ h₂ = ANG A' O B' h₁' h₂' := sorry

end EuclidGeom
