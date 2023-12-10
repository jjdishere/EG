import EuclideanGeometry.Foundation.Axiom.Position.Angle

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem sin_pos_iff_angle_pos (A : Angle P) : 0 < AngValue.sin A.value ↔ A.value.IsPos := sorry

theorem end_ray_toDir_rev_toDir_of_ang_rev_ang {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = (ang₂.start_ray).reverse.toDir) (h : ang₁.value = ang₂.value) : ang₁.end_ray.toDir = (ang₂.end_ray).reverse.toDir := sorry

theorem start_ray_toDir_rev_toDir_of_ang_rev_ang {ang₁ ang₂ : Angle P} (hs : ang₁.end_ray.toDir = (ang₂.end_ray).reverse.toDir) (h : ang₁.value = ang₂.value) : ang₁.start_ray.toDir = (ang₂.start_ray).reverse.toDir := sorry

theorem angle_value_eq_angle (A : P) (ray : Ray P) (h : A ≠ ray.1) : (Angle.mk_ray_pt ray A h).value = VecND.angle ray.2.unitVecND (VEC_nd ray.source A h) := sorry

theorem ang_eq_ang_of_toDir_rev_toDir {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = - ang₂.start_ray.toDir) (he : ang₁.end_ray.toDir = - ang₂.end_ray.toDir) : ang₁.value = ang₂.value := sorry

theorem eq_ang_of_lies_int_liesint {A A' B B' O: P} (h₁ : A ≠ O) (h₂ : B ≠ O) (h₁' : A' ≠ O) (h₂' : B' ≠ O) (LiesInt1 : A' LiesInt (RAY O A h₁) )  (LiesInt2 :  B' LiesInt (RAY O B h₂) ) : ANG A O B h₁ h₂ = ANG A' O B' h₁' h₂' := sorry

theorem eq_ang_value_of_lies_int_lies_int {A A' B B' O: P} (h₁ : A ≠ O) (h₂ : B ≠ O) (h₁' : A' ≠ O) (h₂' : B' ≠ O) (LiesInt1 : A' LiesInt (RAY O A h₁) )  (LiesInt2 :  B' LiesInt (RAY O B h₂) ) : ∠  A O B h₁ h₂ = ∠  A' O B' h₁' h₂' := sorry

theorem neg_value_of_rev_ang {A B O: P} (h₁ : A ≠ O) (h₂ : B ≠ O) : ∠ A O B h₁ h₂ = -∠ B O A h₂ h₁ := sorry

namespace Angle

theorem end_ray_eq_value_vadd_start_ray (ang : Angle P) : ang.end_ray.toDir = ang.value +ᵥ ang.start_ray.toDir := sorry

theorem ang_source_eq_end_ray_source (ang : Angle P) : ang.source = ang.end_ray.source := sorry

def mk_strat_ray (ang : Angle P) (ray : Ray P) (h : ang.source = ray.source) : Angle P := Angle.mk ang.start_ray ray h

def mk_ray_end (ang : Angle P) (ray : Ray P) (h : ang.source = ray.source) : Angle P := Angle.mk ray ang.end_ray (by rw[h.symm, ang_source_eq_end_ray_source])

theorem value_eq_vsub (ray₁ : Ray P) (ray₂ : Ray P) (h: ray₁.source = ray₂.source) : (Angle.mk ray₁ ray₂ h).value = ray₂.toDir -ᵥ ray₁.toDir := sorry

theorem mk_strat_ray_value_eq_vsub (ang : Angle P) (ray : Ray P) (h : ang.source = ray.source) : (Angle.mk_strat_ray ang ray h).value = ray.toDir -ᵥ ang.start_ray.toDir := sorry

theorem mk_ray_end_value_eq_vsub (ang : Angle P) (ray : Ray P) (h : ang.source = ray.source) : (Angle.mk_ray_end ang ray h).value = ang.end_ray.toDir -ᵥ ray.toDir := sorry

end Angle

end EuclidGeom
