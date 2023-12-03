import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash
import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Circle.Basic

import EuclideanGeometry.Foundation.Axiom.Basic.Angle_trash
/-!

-/
noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

-- Feel free to change the name of the theorems and comments into better ones, or add sections to better organize theorems.
-- `Currently, the theorems are not well-organized, please follow the plan file to write and add theorems in this file into the plan file if they are not already in the plan`

-- we don't need to put the following definitions in the namespace Angle, since we will certainly not use it in the form of `ang.IsBis ray`
-- if only one condition is used, please change `structure : Prop` back to `def : Prop`, if more than one condition is used, please name each condition under structure, please do not use `∧`.



structure IsAngBis (ang : Angle P) (ray : Ray P) : Prop where
  eq_source : ang.source = ray.source
  eq_value : (Angle.mk_start_ray ang ray eq_source).value = (Angle.mk_ray_end ang ray eq_source).value
  same_sgn : ((Angle.mk_start_ray ang ray eq_source).value.IsPos ∧ ang.value.IsPos) ∨ ((Angle.mk_start_ray ang ray eq_source).value.IsNeg ∧ ang.value.IsNeg) ∨ ((Angle.mk_start_ray ang ray eq_source).value = (2⁻¹ * π).toAngValue ∧ ang.value = π ) ∨ ((Angle.mk_start_ray ang ray eq_source).value = 0 ∧ ang.value = 0)


structure IsAngBisLine (ang : Angle P) (l : Line P) : Prop where
  source_on : ang.source LiesOn l

structure IsExAngBis

structure IsExAngBiscetorLine

namespace Angle


/- when the Angle is flat, bis is on the left side-/
def AngBis (ang : Angle P) : Ray P where
  source := ang.source
  toDir := ang.start_ray.toDir * (2⁻¹ * ang.value.toReal).toAngValue.toDir

def AngBisLine (ang : Angle P) : Line P := ang.AngBis.toLine

def ExAngBis (ang : Angle P) : Ray P where
  source := ang.source
  toDir := ang.start_ray.toDir * (2⁻¹ * ang.value.toReal + 2⁻¹ * π).toAngValue.toDir

def ExAngBisLine (ang : Angle P) : Line P := ang.ExAngBis.toLine

end Angle

namespace Angle

theorem eq_source {ang : Angle P} : ang.source = ang.AngBis.source := rfl

theorem mk_start_ray_value_eq_half_angvalue {ang : Angle P} : (Angle.mk_start_ray ang ang.AngBis eq_source).value.toReal = 2⁻¹ * ang.value.toReal := by
  rw [mk_start_ray_value_eq_angdiff eq_source]
  rw [Dir.AngDiff]
  unfold AngBis
  simp
  have h₁ : (-π < 2⁻¹ * (value ang).toReal) ∧ (2⁻¹ * (value ang).toReal ≤ π) := by simp [neg_half_pi_le_half_angvalue, half_angvalue_le_half_pi]
  simp [real_eq_toangvalue_toreal_real_iff_neg_pi_le_real_le_pi, h₁]

theorem angbis_is_angbis {ang : Angle P} : IsAngBis ang ang.AngBis where
  eq_source := rfl
  eq_value := by
    have h : ang.source = ang.AngBis.source := rfl
    rw [mk_start_ray_value_eq_angdiff h]
    rw [mk_ray_end_value_eq_angdiff h]
    rw [Dir.AngDiff, Dir.AngDiff, ← dir_eq_of_angvalue_eq]
    rw [AngBis]
    rw [end_ray_eq_start_ray_mul_value]
    simp
    rw [← sub_todir_eq_todir_div, theta_sub_half_theta_eq_half_theta]
  same_sgn := by
    have h : ang.source = ang.AngBis.source := rfl
    have g : (ang.value.IsPos) ∨ (ang.value.IsNeg) ∨ (ang.value = π) ∨ (ang.value = 0) := by sorry
    rcases g with g₁|g₂|g₃|g₄
    · left
      simp [g₁]
      apply half_angvalue_is_pos_if_angvalue_is_pos
      apply mk_start_ray_value_eq_half_angvalue
      exact g₁
    · right
      left
      simp [g₂]
      apply half_angvalue_is_neg_if_angvalue_is_neg
      apply mk_start_ray_value_eq_half_angvalue
      exact g₂
    · right
      right
      left
      constructor
      · apply toreal_eq_half_pi_of_eq_half_pi_toangvalue
        simp [toreal_eq_half_pi_of_eq_half_pi_toangvalue,mk_start_ray_value_eq_half_angvalue, g₃]
      · exact g₃
    · right
      right
      right
      constructor
      · apply AngValue.eq_zero_of_toreal_eq_zero
        simp [mk_start_ray_value_eq_half_angvalue, g₄]
      · exact g₄





theorem angbis_iff_angbis {ang : Angle P} {r : Ray P} : IsAngBis ang r ↔ r = ang.AngBis := by
  constructor
  · sorry
  · exact fun h ↦ (by rw [h]; apply angbis_is_angbis)


theorem ang_source_rev_eq_source_bis {ang : Angle P} {r : Ray P} (h : IsAngBis ang r) : ang.rev.source = r.source := by rw[ang.ang_source_rev_eq_source, h.eq_source]

theorem nonpi_bisector_eq_bisector_of_rev {ang : Angle P} {r : Ray P} (h : IsAngBis ang r) (nonpi : ang.value ≠ π ): IsAngBis ang.rev r where
  eq_source := by rw[h.eq_source.symm, ang.ang_source_rev_eq_source]
  eq_value := by
    have : (Angle.mk_start_ray ang.rev r (ang_source_rev_eq_source_bis h)) = (Angle.mk_ray_end ang r h.eq_source).rev := rfl
    rw [this, (Angle.mk_ray_end ang r h.eq_source).ang_value_rev_eq_neg_value]
    have : (Angle.mk_ray_end ang.rev r (ang_source_rev_eq_source_bis h)) = (Angle.mk_start_ray ang r h.eq_source).rev := rfl
    rw [this, (Angle.mk_start_ray ang r h.eq_source).ang_value_rev_eq_neg_value]
    simp [h.eq_value]
  same_sgn := by
    have : (Angle.mk_start_ray ang.rev r (ang_source_rev_eq_source_bis h)) = (Angle.mk_ray_end ang r h.eq_source).rev := rfl
    rw [this, (Angle.mk_ray_end ang r h.eq_source).ang_value_rev_eq_neg_value]
    rw [ang.ang_value_rev_eq_neg_value]
    simp
    rw [h.eq_value.symm]
    rcases h.same_sgn with h₁ | h₂ | h₃ | h₄
    · exact Or.inr (Or.inl h₁)
    · exact Or.inl h₂
    · absurd nonpi
      exact h₃.2
    · exact Or.inr (Or.inr (Or.inr h₄))


theorem bisector_eq_bisector_of_rev' {ang : Angle P} : ang.AngBis = ang.rev.AngBis := by
  sorry

theorem angbisline_is_angbisline : sorry := sorry

theorem exangbis_is_exangbis : sorry := sorry

theorem exangbisline_is_exangbisline : sorry := sorry

end Angle

/-definition property: lies on the bis means bisect the angle-/
theorem lie_on_angbis (ang: Angle P) (A : P) (h : A ≠ ang.source): A LiesOn ang.AngBis ↔ IsAngBis ang (RAY _ _ h) := by
  rw [Angle.angbis_iff_angbis]
  exact ⟨fun g ↦ (by rw [← Ray.pt_pt_eq_ray ⟨g, h⟩]; rfl),
    fun g ↦ (by rw [← g]; apply Ray.pt_lies_on_pt_pt)⟩

/- underlying line of bis as the locus satisfying the sum of distance to each ray of the angle is 0 -/
theorem lie_on_angbisline_of_distance_zero (ang: Angle P) : sorry := sorry

theorem lie_on_angbis_of_lie_on_angbisline_inside_angle (ang : Angle P)  : sorry := sorry

/-bis lies inside the angle-/

/-construct the intercentor as the intersection of two bis-/

/-a triangle_nd admit an unique intercenter-/


structure IsIncenter (tri_nd : Triangle_nd P) (I : P) : Prop where

structure IsExcenter1 (tri_nd : Triangle_nd P) (E : P) : Prop where

structure IsIncircle (tri_nd : Triangle_nd P) (cir : Circle P) : Prop where

structure IsExcircle1 (tri_nd : Triangle_nd P) (cir : Circle P) : Prop where

namespace Triangle_nd

def Incenter (tri_nd : Triangle_nd P) : P := sorry

def Excenter1 (tri_nd : Triangle_nd P) : P := sorry

def Incircle (tri_nd : Triangle_nd P) : Circle P := sorry

def Excircle1 (tri_nd : Triangle_nd P) : Circle P := sorry

end Triangle_nd

namespace Triangle_nd

theorem incenter_is_incenter : sorry := sorry

theorem excenter1_is_excenter1 : sorry := sorry

theorem incircle_is_incircle : sorry := sorry

theorem excircle1_is_excircle1 : sorry := sorry

end Triangle_nd

/-the intercenter lies inside of the triangle-/

theorem incenter_lies_int_triangle (triangle_nd : Triangle_nd P): sorry := sorry

end EuclidGeom
