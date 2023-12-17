import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_ex
import EuclideanGeometry.Foundation.Axiom.Triangle.Trigonometric
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

-- Prefer to define IsIsocelesTriangle than to just state the properties. Isoceles triangle by definition has a prefered orientation

section IsocelesTriangles

open Triangle

def Triangle.IsIsoceles (tri : Triangle P) : Prop := tri.edge₂.length = tri.edge₃.length

theorem is_isoceles_tri_iff_ang_eq_ang_of_nd_tri {tri_nd : TriangleND P} : tri_nd.1.IsIsoceles ↔ (tri_nd.angle₂.value=  tri_nd.angle₃.value) := by
-- To show angle equal => sides equal, use anti-congruent of the triangle with itself. SAS
rcases TriangleND.edge_eq_edge_of_flip_vertices tri_nd with ⟨a, b, c⟩
rcases TriangleND.angle_eq_neg_angle_of_flip_vertices tri_nd with ⟨x, y, z⟩
constructor
intro h0
have h1 : tri_nd.edge₂.length = tri_nd.edge₃.length := by
  exact h0
have h2 : tri_nd ≅ₐ tri_nd.flip_vertices := by
  apply TriangleND.acongr_of_SAS
  rw [← c, h1]
  rw [x]
  rw [← b, ← h1]
rw [h2.5,<-z]
intro k0
have k1 : tri_nd ≅ₐ tri_nd.flip_vertices  := by
  apply TriangleND.acongr_of_ASA
  rw [k0, z]
  exact a
  rw [← k0, y]
have k2 := k1.2
rw [← c] at k2
exact k2

namespace Triangle

-- Changing the order of vertices 2 and 3 in an isoceles triangle does not change the property of being an isoceles triangle.
theorem is_isoceles_of_flip_vert_isoceles (tri : Triangle P) (h : tri.IsIsoceles) : tri.flip_vertices.IsIsoceles := by
have h₂ : tri.flip_vertices.edge₂.length = tri.flip_vertices.edge₃.length := by
  rcases Triangle.edge_eq_edge_of_flip_vertices tri with ⟨_, b, c⟩
  rw [← b, ← c, h]
exact h₂

end Triangle

end IsocelesTriangles

-- Define regular triangle

def Triangle.IsRegular (tri : Triangle P) : Prop := tri.edge₁.length = tri.edge₂.length ∧ tri.edge₁.length = tri.edge₃.length

namespace Triangle

theorem isoceles_of_regular (tri : Triangle P) (h : tri.IsRegular) : tri.IsIsoceles := by
rcases h with ⟨s,t⟩
rw [s] at t
exact t

-- Changing the order of vertices in a regular triangle does not change the property of being an regular triangle.
theorem regular_of_regular_flip_vert (tri : Triangle P) (h : tri.IsRegular) : tri.flip_vertices.IsRegular := by
rcases Triangle.edge_eq_edge_of_flip_vertices tri with ⟨a, b, c⟩
rcases h with ⟨x, y⟩
rw [a, b] at x
rw [a, c] at y
constructor
exact y
exact x

theorem regular_of_regular_perm_vert (tri : Triangle P) (h : tri.IsRegular) : tri.perm_vertices.IsRegular := by
rcases Triangle.edge_eq_edge_of_perm_vertices tri with ⟨a, b, c⟩
rcases h with ⟨x, y⟩
rw [a, b] at x
rw [a, c] at y
constructor
rw [y]
rw [← x, ← y]

end Triangle

-- A nontrivial triangle is an regular triangle if and only if all of its angles are equal.
theorem regular_tri_iff_eq_angle_of_nd_tri (tri_nd : TriangleND P) : tri_nd.1.IsRegular ↔ tri_nd.angle₁.value = tri_nd.angle₂.value ∧ tri_nd.angle₁.value = tri_nd.angle₃.value := by
rcases TriangleND.angle_eq_angle_of_perm_vertices tri_nd with ⟨a1, a2, _⟩
rcases TriangleND.edge_eq_edge_of_perm_vertices tri_nd with ⟨b1, b2, _⟩
constructor
intro h
have perm_isisocele₁ : tri_nd.1.perm_vertices.IsIsoceles := by
  apply Triangle.isoceles_of_regular
  apply Triangle.regular_of_regular_perm_vert
  exact h
constructor
rw [a1, a2]
rw [is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mp]
exact perm_isisocele₁
rw [← is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mp,a1, a2, is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mp]
exact perm_isisocele₁
apply Triangle.isoceles_of_regular
exact h
intro k0
rcases k0 with ⟨k1, k2⟩
have perm_isisocele₂ : tri_nd.perm_vertices.1.IsIsoceles := by
  apply is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mpr
  rw [a1, a2] at k1
  exact k1
have k3 : tri_nd.edge₁.length = tri_nd.edge₂.length := by
  rw [b1, b2]
  exact perm_isisocele₂
constructor
. exact k3
have := Triangle.sine_rule₂ tri_nd
rw [<-k2] at this
simp only [mul_eq_mul_right_iff] at this
rcases this with k4 | k5
. exact k4
. have nd := sine_ne_zero_of_nd tri_nd
  exact b1

-- An clockwise regular triangle has all angles being π/3

theorem ang_eq_sixty_deg_of_cclock_regular_tri (tri_nd : TriangleND P) (cclock : tri_nd.is_cclock)(h : tri_nd.1.IsRegular) : tri_nd.angle₁.value= ↑(π / 3) ∧ tri_nd.angle₂.value = ↑(π / 3) ∧ tri_nd.angle₃.value = ↑(π / 3) := by
sorry
/-
rw [regular_tri_iff_eq_angle_of_nd_tri] at h
rcases h with ⟨h1, h2⟩
have h3 := TriangleND.angle_sum_eq_pi_of_cclock tri_nd cclock
rw [← h1, ← h2, ← mul_add, ← mul_add] at h3
norm_num at h3
rw [← eq_div_iff] at h3
constructor
exact h3
constructor
rw [← h1, h3]
rw [← h2, h3]
norm_num
-/

-- An anticlockwise equilateral triangle has all angles being - π/3

theorem ang_eq_sixty_deg_of_acclock_regular_tri (tri_nd : TriangleND P) (acclock : ¬ tri_nd.is_cclock)(h : tri_nd.1.IsRegular) : tri_nd.angle₁.value= ↑ (- π / 3) ∧ tri_nd.angle₂.value = ↑(- π / 3) ∧ tri_nd.angle₃.value = ↑ (- π / 3) := by sorry
/-
rw [regular_tri_iff_eq_angle_of_nd_tri] at h
rcases h with ⟨h1, h2⟩
have h3 := TriangleND.angle_sum_eq_neg_pi_of_clock tri_nd acclock
rw [← h1, ← h2, ← mul_one tri_nd.angle₁.value , ← mul_add, ← mul_add] at h3
norm_num at h3
rw [← eq_div_iff] at h3
constructor
exact h3
constructor
rw [← h1, h3]
rw [← h2, h3]
norm_num
-/

-- An isoceles triangle is an equilateral triangle if one of its angle is π/3 (or -π /3). Here there are two possibilities

theorem regular_tri_of_isoceles_tri_of_fst_ang_eq_sixty_deg(tri_nd : TriangleND P) (h : tri_nd.angle₁.value = ↑ (π /3) ∨ tri_nd.angle₁.value = ↑ (- π / 3)) (h1 : tri_nd.1.IsIsoceles) : tri_nd.1.IsRegular := by
sorry
/-
rcases h with (p1 | p2)
have cclock : tri_nd.is_cclock := by
  apply TriangleND.cclock_of_pos_angle
  left
  rw [p1]
  linarith [Real.pi_pos]
have sum₁ := TriangleND.angle_sum_eq_pi_of_cclock tri_nd cclock
have h2 : tri_nd.angle₂.value = π / 3 := by
  rw [← is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mp h1] at sum₁
  linarith [sum₁]
have h3 : tri_nd.angle₃.value = π / 3 := by
  simp only [← is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mp h1, h2]
rw [regular_tri_iff_eq_angle_of_nd_tri]
constructor
rw [p1, h2]
rw [p1, h3]
have clock : ¬ tri_nd.is_cclock := by
  apply TriangleND.clock_of_neg_angle
  left
  rw [p2]
  linarith [Real.pi_pos]
have sum₂ := TriangleND.angle_sum_eq_neg_pi_of_clock tri_nd clock
have f4 : tri_nd.angle₂.value = -π / 3 := by
  rw [← is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mp h1, p2] at sum₂
  linarith [sum₂]
have f5 : tri_nd.angle₃.value = -π / 3 := by
  rw [← is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mp h1]
  rw [f4]
rw [regular_tri_iff_eq_angle_of_nd_tri]
constructor
rw [p2 , f4]
rw [p2 , f5]
-/

theorem regular_tri_of_isoceles_tri_of_snd_ang_eq_sixty_deg (tri_nd : TriangleND P) (h : tri_nd.angle₂.value = ↑ (π /3) ∨ tri_nd.angle₂.value = ↑ (- π / 3)) (h1 : tri_nd.1.IsIsoceles) : tri_nd.1.IsRegular:= by sorry
/-
apply regular_tri_of_isoceles_tri_of_fst_ang_eq_sixty_deg
rcases h with (p1 | p2)
left
have h2 : tri_nd.is_cclock := by
  apply TriangleND.cclock_of_pos_angle
  right
  left
  rw [p1]
  linarith [Real.pi_pos]
have h3 := TriangleND.angle_sum_eq_pi_of_cclock tri_nd h2
rw [← is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mp h1, p1] at h3
linarith [h3]
right
have f3 : ¬ tri_nd.is_cclock := by
  apply TriangleND.clock_of_neg_angle
  right
  left
  rw [p2]
  linarith [Real.pi_pos]
have f3 := TriangleND.angle_sum_eq_neg_pi_of_clock tri_nd f3
rw [← is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mp h1, p2] at f3
linarith [f3]
exact h1
-/

theorem regular_tri_of_isoceles_tri_of_trd_ang_eq_sixty_deg (tri_nd : TriangleND P) (h : tri_nd.angle₃.value = ↑ (π /3) ∨ tri_nd.angle₃.value = ↑(- π / 3)) (h1 : tri_nd.1.IsIsoceles) : tri_nd.1.IsRegular:= by sorry
/-
apply regular_tri_of_isoceles_tri_of_fst_ang_eq_sixty_deg
rcases h with (p1 | p2)
left
have h2 : tri_nd.is_cclock := by
  apply TriangleND.cclock_of_pos_angle
  right
  right
  rw [p1]
  linarith [Real.pi_pos]
have h3 := TriangleND.angle_sum_eq_pi_of_cclock tri_nd h2
rw [is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mp h1, p1] at h3
linarith [h3]
right
have f2 : ¬ tri_nd.is_cclock := by
  apply TriangleND.clock_of_neg_angle
  right
  right
  rw [p2]
  linarith [Real.pi_pos]
have f3 := TriangleND.angle_sum_eq_neg_pi_of_clock tri_nd f2
rw [is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mp h1, p2] at f3
linarith [f3]
exact h1
-/
end EuclidGeom
