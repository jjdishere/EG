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

open AngValue Angle

variable {P : Type _} [EuclideanPlane P]

-- Feel free to change the name of the theorems and comments into better ones, or add sections to better organize theorems.
-- `Currently, the theorems are not well-organized, please follow the plan file to write and add theorems in this file into the plan file if they are not already in the plan`

-- we don't need to put the following definitions in the namespace Angle, since we will certainly not use it in the form of `ang.IsBis ray`
-- if only one condition is used, please change `structure : Prop` back to `def : Prop`, if more than one condition is used, please name each condition under structure, please do not use `∧`.



structure IsAngBis (ang : Angle P) (ray : Ray P) : Prop where
  eq_source : ang.source = ray.source
  eq_value : (mk_dir₁ ang ray.toDir).value = (mk_dir₂ ang ray.toDir).value
  -- `the definition of same_sgn should be rewrite, using btw`.
  -- May change it to `- π / 2 < (mk_dir₁ ang ray.toDir).value ≤ π / 2`.
  same_sgn : ((mk_dir₁ ang ray.toDir).value.IsPos ∧ ang.value.IsPos) ∨ ((mk_dir₁ ang ray.toDir).value.IsNeg ∧ ang.value.IsNeg) ∨ ((mk_dir₁ ang ray.toDir).value = ↑(π/2) ∧ ang.value = π ) ∨ ((mk_dir₁ ang ray.toDir).value = 0 ∧ ang.value = 0)


structure IsAngBisLine (ang : Angle P) (l : Line P) : Prop where
  source_on : ang.source LiesOn l

structure IsExAngBis where

structure IsExAngBiscetorLine where

namespace Angle


/- when the Angle is flat, bis is on the left side-/
def AngBis (ang : Angle P) : Ray P where
  source := ang.source
  toDir := ang.value.half +ᵥ ang.dir₁

def AngBisLine (ang : Angle P) : Line P := ang.AngBis.toLine

def ExAngBis (ang : Angle P) : Ray P where
  source := ang.source
  toDir := ∠[ang.value.toReal/2 + π/2] +ᵥ ang.dir₁

def ExAngBisLine (ang : Angle P) : Line P := ang.ExAngBis.toLine

end Angle

namespace Angle

theorem eq_source {ang : Angle P} : ang.source = ang.AngBis.source := rfl

theorem value_angBis_eq_half_value {ang : Angle P} : (mk_dir₁ ang ang.AngBis.toDir).value = ang.value.half := by
  simp only [mk_dir₁_value, AngBis, vadd_vsub]

theorem mk_start_ray_value_eq_half_angvalue {ang : Angle P} : (mk_dir₁ ang ang.AngBis.toDir).value.toReal = ang.value.toReal / 2 :=
  (Eq.congr_right (ang.value.half_toReal).symm).mpr (congrArg toReal ang.value_angBis_eq_half_value)

theorem angbis_is_angbis {ang : Angle P} : IsAngBis ang ang.AngBis where
  eq_source := rfl
  eq_value := by
    simp only [mk_dir₁_value, mk_dir₂_value, AngBis, vadd_vsub, vsub_vadd_eq_vsub_sub]
    exact sub_half_eq_half.symm
  same_sgn := by
    have g : (ang.value.IsPos) ∨ (ang.value.IsNeg) ∨ (ang.value = π) ∨ (ang.value = 0) := by
      rcases ang.value.not_isND_or_isPos_or_isNeg with d|_|_
      simp [AngValue.not_isND_iff'] at d
      tauto
      tauto
      tauto
    rcases g with g₁|g₂|g₃|g₄
    · simp only [g₁, and_true, value_angBis_eq_half_value]
      exact .inl (half_isPos_of_isPos g₁)
    · simp only [value_angBis_eq_half_value, g₂, and_true]
      exact .inr (.inl (half_isNeg_iff_isNeg.mpr g₂))
    · right
      right
      left
      constructor
      · apply toReal_eq_pi_div_two_iff.mp
        simp only [mk_start_ray_value_eq_half_angvalue, g₃, neg_lt_self_iff, toReal_pi]
      · exact g₃
    · right
      right
      right
      constructor
      · rw [← AngValue.toReal_inj]
        simp only [mk_start_ray_value_eq_half_angvalue, g₄, toReal_zero, zero_div]
      · exact g₄

theorem angbis_iff_angbis {ang : Angle P} {r : Ray P} : IsAngBis ang r ↔ r = ang.AngBis := by
  constructor
  · sorry
  · exact fun h ↦ (by rw [h]; apply angbis_is_angbis)


theorem ang_source_rev_eq_source_bis {ang : Angle P} {r : Ray P} (h : IsAngBis ang r) : ang.reverse.source = r.source := h.eq_source

theorem nonpi_bisector_eq_bisector_of_rev {ang : Angle P} {r : Ray P} (h : IsAngBis ang r) (nonpi : ang.value ≠ π ): IsAngBis ang.reverse r where
  eq_source := h.eq_source
  eq_value := by
    simp only [mk_dir₁_value, mk_dir₂_value, reverse]
    rw [← neg_vsub_eq_vsub_rev ang.dir₂ r.toDir, ← neg_vsub_eq_vsub_rev r.toDir ang.dir₁]
    exact neg_inj.mpr h.eq_value.symm
  same_sgn := sorry /- by
    have : (Angle.mk_start_ray ang.reverse r (ang_source_rev_eq_source_bis h)) = (Angle.mk_end_ray ang r h.eq_source).reverse := rfl
    rw [this, (Angle.mk_end_ray ang r h.eq_source).rev_value_eq_neg_value]
    rw [ang.rev_value_eq_neg_value]
    simp
    rw [h.eq_value.symm]
    rcases h.same_sgn with h₁ | h₂ | h₃ | h₄
    · exact Or.inr (Or.inl h₁)
    · exact Or.inl h₂
    · absurd nonpi
      exact h₃.2
    · exact Or.inr (Or.inr (Or.inr h₄)) -/


theorem bisector_eq_bisector_of_rev' {ang : Angle P} : ang.AngBis = ang.reverse.AngBis := by
  sorry

theorem angbisline_is_angbisline : sorry := sorry

theorem exangbis_is_exangbis : sorry := sorry

theorem exangbisline_is_exangbisline : sorry := sorry

end Angle

/-definition property: lies on the bis means bisect the angle-/
theorem lie_on_angbis (ang: Angle P) (A : P) [h : PtNe A ang.source]: A LiesOn ang.AngBis ↔ IsAngBis ang (RAY ang.source A) := by
  rw [Angle.angbis_iff_angbis]
  exact ⟨fun g ↦ (by rw [← Ray.pt_pt_eq_ray ⟨g, h.out⟩]; rfl),
    fun g ↦ (by rw [← g]; exact Ray.snd_pt_lies_on_mk_pt_pt (h := h))⟩

/- underlying line of bis as the locus satisfying the sum of distance to each ray of the angle is 0 -/
theorem lie_on_angbisline_of_distance_zero (ang: Angle P) : sorry := sorry

theorem lie_on_angbis_of_lie_on_angbisline_inside_angle (ang : Angle P)  : sorry := sorry

/-bis lies inside the angle-/

/-construct the intercentor as the intersection of two bis-/

/-a TriangleND admit an unique intercenter-/

structure IsIncenter (tri_nd : TriangleND P) (I : P) : Prop where

structure IsExcenter1 (tri_nd : TriangleND P) (E : P) : Prop where

structure IsIncircle (tri_nd : TriangleND P) (cir : Circle P) : Prop where

structure IsExcircle1 (tri_nd : TriangleND P) (cir : Circle P) : Prop where

namespace TriangleND

theorem angbisline_of_angle₁_angle₂_not_parallel {tri_nd : TriangleND P} : ¬ tri_nd.angle₁.AngBis.toLine ∥ tri_nd.angle₂.AngBis.toLine := by
  by_contra g
  let A₁ := (mk_dir₁ tri_nd.angle₁ tri_nd.angle₁.AngBis.toDir).reverse
  let A₂ := mk_dir₂ tri_nd.angle₂ tri_nd.angle₂.AngBis.toDir
  have sr : A₁.start_ray.toDir = A₂.start_ray.toDir := by
    have h₁ : A₁.start_ray = tri_nd.angle₁.AngBis := rfl
    have h₂ : A₂.start_ray = tri_nd.angle₂.AngBis := rfl
    rw [Ray.para_iff_para_toLine] at g
    rw [← h₁] at g
    rw [← h₂] at g
    sorry
  have er : A₁.end_ray.toDirLine = A₂.end_ray.toDirLine.reverse := by
    have h₃ : A₁.end_ray = tri_nd.edge_nd₃.toRay := rfl
    have h₄ : A₂.end_ray = tri_nd.edge_nd₃.reverse.toRay := rfl
    rw [h₃]
    rw [h₄]
    have h₅ : tri_nd.edge_nd₃.reverse.toDirLine.reverse = tri_nd.edge_nd₃.reverse.reverse.toDirLine := by rw [SegND.toDirLine_rev_eq_rev_toDirLine]
    have h₆ : tri_nd.edge_nd₃.reverse.reverse.toDirLine = tri_nd.edge_nd₃.toDirLine := rfl
    rw [h₆] at h₅
    exact h₅.symm
  have g₁ : IsConsecutiveIntAng A₁ A₂ := ⟨sr, er⟩
  have g₂ : A₁.value - A₂.value = π := by
    simp only [value_sub_eq_pi_of_isConsecutiveIntAng g₁, add_sub_cancel']
  sorry


def Incenter (tri_nd : TriangleND P) : P := Line.inx tri_nd.angle₁.AngBis.toLine tri_nd.angle₂.AngBis.toLine angbisline_of_angle₁_angle₂_not_parallel


def Excenter1 (tri_nd : TriangleND P) : P := sorry

def Incircle (tri_nd : TriangleND P) : Circle P := sorry

def Excircle1 (tri_nd : TriangleND P) : Circle P := sorry

end TriangleND

namespace TriangleND

theorem incenter_is_incenter : sorry := sorry

theorem excenter1_is_excenter1 : sorry := sorry

theorem incircle_is_incircle : sorry := sorry

theorem excircle1_is_excircle1 : sorry := sorry

end TriangleND

/-the intercenter lies inside of the triangle-/

theorem incenter_lies_int_triangle (TriangleND : TriangleND P): sorry := sorry

end EuclidGeom
