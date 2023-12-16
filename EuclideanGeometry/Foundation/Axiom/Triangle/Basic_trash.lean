import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_ex

namespace EuclidGeom
open AngValue

variable {P : Type _} [EuclideanPlane P]

-- `IsAcute should be be prepared in Angle!!`
structure TriangleND.IsAcute (tri_nd : TriangleND P) : Prop where
  angle₁ : - π / 2 < tri_nd.angle₁.value.toReal ∧ tri_nd.angle₁.value.toReal < π / 2
  angle₂ : - π / 2 < tri_nd.angle₂.value.toReal ∧ tri_nd.angle₂.value.toReal < π / 2
  angle₃ : - π / 2 < tri_nd.angle₃.value.toReal ∧ tri_nd.angle₃.value.toReal < π / 2

variable {tr_nd₁ tr_nd₂ : TriangleND P}

theorem edge_toLine_not_para_of_not_colinear {A B C : P} (h : ¬ colinear A B C) : ¬ (SEG_nd A B (ne_of_not_colinear h).2.2) ∥ SEG_nd B C (ne_of_not_colinear h).1 ∧ ¬  (SEG_nd B C (ne_of_not_colinear h).1) ∥ SEG_nd C A (ne_of_not_colinear h).2.1 ∧ ¬  (SEG_nd C A (ne_of_not_colinear h).2.1) ∥ SEG_nd A B (ne_of_not_colinear h).2.2 := by
  constructor
  by_contra h1
  have eq1 : LIN A B (ne_of_not_colinear h).2.2 = LIN B C (ne_of_not_colinear h).1 := by
    apply eq_of_parallel_and_pt_lies_on
    exact (SEG_nd A B (ne_of_not_colinear h).2.2).target_lies_on_toLine
    exact (SEG_nd B C (ne_of_not_colinear h).1).source_lies_on_toLine
    exact h1
  have a_lies_on_ab : A LiesOn (LIN A B (ne_of_not_colinear h).2.2) := (SEG_nd A B (ne_of_not_colinear h).2.2).source_lies_on_toLine
  have a_not_lies_on_bc := (Line.lies_on_line_of_pt_pt_iff_colinear (ne_of_not_colinear h).1 A).mp.mt (flip_colinear_snd_trd.mt (flip_colinear_fst_snd.mt h))
  simp only[← eq1] at a_not_lies_on_bc
  apply a_not_lies_on_bc
  exact a_lies_on_ab
  constructor
  by_contra h2
  have eq2 : LIN B C (ne_of_not_colinear h).1 = LIN C A (ne_of_not_colinear h).2.1 := by
    apply eq_of_parallel_and_pt_lies_on
    exact (SEG_nd B C (ne_of_not_colinear h).1).target_lies_on_toLine
    exact (SEG_nd C A (ne_of_not_colinear h).2.1).source_lies_on_toLine
    exact h2
  have b_lies_on_bc : B LiesOn (LIN B C (ne_of_not_colinear h).1) := (SEG_nd B C (ne_of_not_colinear h).1).source_lies_on_toLine
  have b_not_lies_on_ca := (Line.lies_on_line_of_pt_pt_iff_colinear (ne_of_not_colinear h).2.1 B).mp.mt (flip_colinear_fst_snd.mt (flip_colinear_snd_trd.mt h))
  simp only[← eq2] at b_not_lies_on_ca
  apply b_not_lies_on_ca
  exact b_lies_on_bc
  by_contra h3
  have eq3 : LIN C A (ne_of_not_colinear h).2.1 = LIN A B (ne_of_not_colinear h).2.2 := by
    apply eq_of_parallel_and_pt_lies_on
    exact (SEG_nd C A (ne_of_not_colinear h).2.1).target_lies_on_toLine
    exact (SEG_nd A B (ne_of_not_colinear h).2.2).source_lies_on_toLine
    exact h3
  have c_lies_on_ca : C LiesOn (LIN C A (ne_of_not_colinear h).2.1) := (SEG_nd C A (ne_of_not_colinear h).2.1).source_lies_on_toLine
  have c_not_lies_on_ab := (Line.lies_on_line_of_pt_pt_iff_colinear (ne_of_not_colinear h).2.2 C).mp.mt h
  simp only[← eq3] at c_not_lies_on_ab
  apply c_not_lies_on_ab
  exact c_lies_on_ca

theorem angle_eq_of_cosine_eq_of_cclock (cclock : tr_nd₁.is_cclock ↔ tr_nd₂.is_cclock) (cosine : cos tr_nd₁.angle₁.value = cos tr_nd₂.angle₁.value) : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value := by
  have g : (tr_nd₁.angle₁.value.IsPos ∧ tr_nd₂.angle₁.value.IsPos) ∨ (tr_nd₁.angle₁.value.IsNeg ∧ tr_nd₂.angle₁.value.IsNeg) := by
      exact (TriangleND.pos_pos_or_neg_neg_of_iff_cclock).mp cclock
  rcases g with x | y
  · have x₁ : tr_nd₁.angle₁.value.IsPos := sorry
    have x₂ : tr_nd₂.angle₁.value.IsPos := sorry
    exact (pos_angle_eq_angle_iff_cos_eq_cos tr_nd₁.angle₁.value tr_nd₂.angle₁.value x₁ x₂).mp cosine
  · have y₁ : tr_nd₁.angle₁.value.IsNeg := sorry
    have y₂ : tr_nd₂.angle₁.value.IsNeg := sorry
    exact (neg_angle_eq_angle_iff_cos_eq_cos tr_nd₁.angle₁.value tr_nd₂.angle₁.value y₁ y₂).mp cosine

theorem angle_eq_neg_of_cosine_eq_of_clock (clock : tr_nd₁.is_cclock ↔ ¬ tr_nd₂.is_cclock) (cosine : cos tr_nd₁.angle₁.value = cos tr_nd₂.angle₁.value) : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value := by sorry

theorem sine_ne_zero_of_nd (tr_nd : TriangleND P) : sin (tr_nd.angle₁.value)  ≠ 0 := by sorry

namespace TriangleND

theorem edge_eq_edge_of_perm_vertices_two_times (tr_nd : TriangleND P) : tr_nd.1.edge₁.length = tr_nd.perm_vertices.perm_vertices.1.edge₃.length ∧ tr_nd.1.edge₂.length = tr_nd.perm_vertices.perm_vertices.1.edge₁.length ∧ tr_nd.1.edge₃.length = tr_nd.perm_vertices.perm_vertices.1.edge₂.length := sorry

theorem angle_eq_angle_of_perm_vertices_two_times (tr_nd : TriangleND P) : tr_nd.angle₁.value = tr_nd.perm_vertices.perm_vertices.angle₃.value ∧ tr_nd.angle₂.value = tr_nd.perm_vertices.perm_vertices.angle₁.value ∧ tr_nd.angle₃.value = tr_nd.perm_vertices.perm_vertices.angle₂.value := by sorry

theorem points_ne_of_colinear_of_not_colinear1 {A B C D : P} (ncolin : ¬ colinear A B C) (colin : colinear D B C) : D ≠ A := sorry

theorem points_ne_of_colinear_of_not_colinear2 {A B C D : P} (ncolin : ¬ colinear A B C) (colin : colinear D C A) : D ≠ B := sorry

theorem points_ne_of_colinear_of_not_colinear3 {A B C D : P} (ncolin : ¬ colinear A B C) (colin : colinear D A B) : D ≠ C := sorry

theorem not_parallel_of_not_colinear_of_colinear_colinear {A B C D E : P} (nd : ¬ colinear A B C) (colindbc : colinear D B C) (colineca : colinear E C A) : ¬ (LIN A D (points_ne_of_colinear_of_not_colinear1 nd colindbc)) ∥ (LIN B E (points_ne_of_colinear_of_not_colinear2 nd colineca)) := sorry

theorem intersection_not_colinear_of_nondegenerate {A B C D E : P} (nd : ¬ colinear A B C) (colindbc : colinear D B C) (colineca : colinear E C A) (dneb : D ≠ B) (dnec : D ≠ C) (enea : E ≠ A) (enec : E ≠ C) (F : P) (fdef : F = Line.inx (LIN A D (points_ne_of_colinear_of_not_colinear1 nd colindbc)) (LIN B E (points_ne_of_colinear_of_not_colinear2 nd colineca)) (not_parallel_of_not_colinear_of_colinear_colinear nd colindbc colineca)) : (¬ colinear A B F) ∧ (¬ colinear B C F) ∧ (¬ colinear C A F) := by sorry

end TriangleND

theorem angle_sum_eq_pi_of_tri (tri : Triangle P) (h₁ : tri.point₂ ≠ tri.point₃) (h₂ : tri.point₃ ≠ tri.point₁) (h₃ : tri.point₁ ≠ tri.point₂) : ∠ tri.point₂ tri.point₁ tri.point₃ h₃.symm h₂ + ∠ tri.point₃ tri.point₂ tri.point₁ h₁.symm h₃ + ∠ tri.point₁ tri.point₃ tri.point₂ h₂.symm h₁ = π := sorry

end EuclidGeom
