import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash

namespace EuclidGeom

open AngValue

variable {P : Type _} [EuclideanPlane P]

theorem Angle.sin_pos_iff_isPos (ang : Angle P) : 0 < sin ang.value ↔ ang.IsPos := isPos_iff_zero_lt_sin.symm

theorem end_ray_toDir_rev_toDir_of_ang_rev_ang {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = (ang₂.start_ray).reverse.toDir) (h : ang₁.value = ang₂.value) : ang₁.end_ray.toDir = (ang₂.end_ray).reverse.toDir := sorry

theorem start_ray_toDir_rev_toDir_of_ang_rev_ang {ang₁ ang₂ : Angle P} (hs : ang₁.end_ray.toDir = (ang₂.end_ray).reverse.toDir) (h : ang₁.value = ang₂.value) : ang₁.start_ray.toDir = (ang₂.start_ray).reverse.toDir := sorry

theorem angle_value_eq_angle (A : P) (ray : Ray P) [h : PtNe A ray.source] : (Angle.mk_ray_pt ray A h.out).value = VecND.angle ray.2.unitVecND (VEC_nd ray.source A) := sorry

theorem ang_eq_ang_of_toDir_rev_toDir {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = - ang₂.start_ray.toDir) (he : ang₁.end_ray.toDir = - ang₂.end_ray.toDir) : ang₁.value = ang₂.value := sorry

theorem angle_eq_zero_of_same_dir {A O : P} [h₁ : PtNe A O] : ∠ A O A = 0 := sorry

theorem eq_ang_of_lies_int_liesint {A A' B B' O: P} [h₁ : PtNe A O] [h₂ : PtNe B O] [h₁' : PtNe A' O] [h₂' : PtNe B' O] (LiesInt1 : A' LiesInt (RAY O A) )  (LiesInt2 :  B' LiesInt (RAY O B) ) : ANG A O B = ANG A' O B' := sorry

--Nailin Guan
theorem neg_value_of_rev_ang {A B O: P} [h₁ : PtNe A O] [h₂ : PtNe B O] : ∠ A O B = -∠ B O A := sorry

theorem neg_dvalue_of_rev_ang {A B O: P} (h₁ : A ≠ O) (h₂ : B ≠ O) : (ANG A O B h₁ h₂).dvalue = -(ANG B O A h₂ h₁).dvalue := sorry
-- WangJingTing
namespace Angle

theorem end_ray_eq_value_vadd_start_ray (ang : Angle P) : ang.dir₂ = ang.value +ᵥ ang.dir₁ := sorry

def mk_start_ray (ang : Angle P) (ray : Ray P) (h : ang.source = ray.source) : Angle P := Angle.mk_two_ray_of_eq_source ang.start_ray ray h

def mk_end_ray (ang : Angle P) (ray : Ray P) (h : ang.source = ray.source) : Angle P := Angle.mk_two_ray_of_eq_source ray ang.end_ray h.symm

theorem value_eq_vsub (ray₁ : Ray P) (ray₂ : Ray P) (h: ray₁.source = ray₂.source) : (Angle.mk_two_ray_of_eq_source ray₁ ray₂ h).value = ray₂.toDir -ᵥ ray₁.toDir := sorry

theorem mk_strat_ray_value_eq_vsub (ang : Angle P) (ray : Ray P) (h : ang.source = ray.source) : (Angle.mk_start_ray ang ray h).value = ray.toDir -ᵥ ang.dir₁ := sorry

theorem mk_end_ray_value_eq_vsub (ang : Angle P) (ray : Ray P) (h : ang.source = ray.source) : (Angle.mk_end_ray ang ray h).value = ang.dir₂ -ᵥ ray.toDir := sorry

end Angle

theorem dvalue_eq_ang_rays_perp {ang : Angle P} (h : ang.dvalue = ∡[π / 2]) : ang.start_ray ⟂ ang.end_ray := by
  show ang.start_ray.toProj = ∡[π / 2] +ᵥ ang.end_ray.toProj
  sorry

theorem liesint_segnd_value_eq_pi {A B C : P} (hne : B ≠ A) (h : C LiesInt (SEG_nd A B hne)) : ∠ A C B h.2.symm h.3.symm = π := sorry

end EuclidGeom
