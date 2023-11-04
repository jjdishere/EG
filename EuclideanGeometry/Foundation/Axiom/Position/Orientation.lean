import EuclideanGeometry.Foundation.Axiom.Position.Angle

/- This file discuss the relative positions of points and rays on a plane. -/
noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P]

/- Definition of the area of a triangle, could be used to develop orientation of triangles.-/

section wedge

def wedge (A B C : P) : ℝ := det (VEC A B) (VEC A C)

def oarea (A B C : P) : ℝ := wedge A B C / 2

theorem wedge213 (A B C : P) : wedge B A C = - wedge A B C := by
  dsimp only [wedge]
  have h1 : VEC B A = (-1 : ℝ) • VEC A B := by
    dsimp only [Vec.mk_pt_pt]
    rw[Complex.real_smul]
    field_simp
  rw [h1, det_smul_left_eq_mul_det, det_eq_neg_det, det_eq_neg_det (VEC A B) _]
  field_simp
  have h2 : VEC B C = VEC A C - VEC A B := by
    dsimp only [Vec.mk_pt_pt]
    exact Eq.symm (vsub_sub_vsub_cancel_right C B A)
  rw [h2, det_sub_eq_det]

theorem wedge132 (A B C : P) : wedge A C B = - wedge A B C := by
  dsimp only [wedge]
  apply det_symm

theorem wedge312 (A B C : P) : wedge C A B = wedge A B C := by
  rw [wedge213, wedge132]
  ring

theorem wedge231 (A B C : P) : wedge B C A = wedge A B C := by rw [wedge312, wedge312]

theorem wedge321 (A B C : P) : wedge C B A = - wedge A B C := by rw [wedge213, wedge231]

theorem area_eq_sine_mul_lenght_mul_length (A B C : P) (aneb : B ≠ A) (anec : C ≠ A) : wedge A B C = (Real.sin (Angle.mk_pt_pt_pt B A C aneb anec).value * (SEG A B).length *(SEG A C).length) := by
  dsimp only [wedge]
  have vecabnd : VEC A B ≠ 0 := by
   exact (ne_iff_vec_ne_zero A B).mp aneb
  have vecacnd : VEC A C ≠ 0 := by
   exact (ne_iff_vec_ne_zero A C).mp anec
  have h0 : (Angle.mk_pt_pt_pt B A C aneb anec).value = Vec_nd.angle ⟨VEC A B , vecabnd⟩ ⟨VEC A C, vecacnd⟩ := by
   dsimp only [Angle.mk_pt_pt_pt,Vec_nd.angle,angle_value_eq_dir_angle]
   rfl
  rw [h0]
  apply det_eq_sin_mul_norm_mul_norm ⟨VEC A B , vecabnd⟩ ⟨VEC A C, vecacnd⟩

end wedge

/- Directed distance-/
section oriented_distance

def odist (A : P) (ray : Ray P) : ℝ := det ray.2.1 (VEC ray.1 A)

/- may insert some theorems relating colinearity and zero directed distance, which might take some efforts-/

theorem odist_eq_sine_mul_length (A : P) (ray : Ray P) (h : A ≠ ray.source) : odist A ray = Real.sin ((Angle.mk_ray_pt ray A h).value) * (SEG ray.source A).length := by sorry

theorem wedge_eq_odist_mul_length (A B C : P) (aneb : B ≠ A) : (wedge A B C) = ((odist A (RAY A B aneb)) * (SEG A B).length) := by sorry

end oriented_distance

/- Positions of points on a line, ray, oriented segments. -/

section point_to_ray

def Ray.sign (A : P) (ray : Ray P) : ℝ := Real.sign (odist A ray)

def IsOnLeftSide (A : P) (ray : Ray P) : Prop := by
  by_cases 0 < odist A ray
  · exact True
  · exact False

def IsOnRightSide (A : P) (ray : Ray P) : Prop := by
  by_cases odist A ray < 0
  · exact True
  · exact False

/- Relation of position of points on a ray and directed distance-/

end point_to_ray

scoped infix : 50 "LiesOnLeft" => IsOnLeftSide
scoped infix : 50 "LiesOnRight" => IsOnRightSide

/- Position of two rays -/
section ray_to_ray

/- Statement of his theorem should change, since ray₀.source ≠ ray₂.source. -/
theorem intersect_of_ray_on_left_iff (ray₁ ray₂ : Ray P) (h : ray₂.source ≠ ray₁.source) : let ray₀ := Ray.mk_pt_pt ray₁.source ray₂.source h; (0 < value_of_angle_of_two_ray_of_eq_source ray₀ ray₁ rfl) ∧ (value_of_angle_of_two_ray_of_eq_source ray₀ ray₁ rfl < value_of_angle_of_two_ray_of_eq_source ray₀ ray₂ sorry) ∧ (value_of_angle_of_two_ray_of_eq_source ray₀ ray₂ sorry < π) ↔ (∃ A : P, (A LiesOn ray₁) ∧ (A LiesOn ray₂) ∧ (A LiesOnLeft ray₀))  := sorry

end ray_to_ray



/- Position of two lines; need a function to take the intersection of two lines (when they intersect). -/


/- A lot more theorems regarding positions -/
/- e.g. 180 degree implies colinear -/

end EuclidGeom
