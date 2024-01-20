import EuclideanGeometry.Foundation.Construction.ComputationTool.Ceva
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_trash

noncomputable section
namespace EuclidGeom

open Classical

section Ceva's_converse_theorem

structure Setting (P : Type*) [EuclideanPlane P] where
  -- Let $\triangle ABC$ be a nondegenerate triangle.
  A : P
  B : P
  C : P
  not_collinear_ABC : ¬ Collinear A B C
  -- Let $E$ be a point on $BC$.
  E : P
  collinear_EBC : Collinear E B C
  -- Let $F$ be a point on $CA$.
  F : P
  collinear_FCA : Collinear F C A
  -- Let $G$ be a point on $AB$.
  G : P
  collinear_GAB : Collinear G A B
  -- Claim : $E \ne A$.
  E_ne_A : E ≠ A := TriangleND.points_ne_of_collinear_of_not_collinear1 not_collinear_ABC collinear_EBC
  -- Claim : $F \ne B$.
  F_ne_B : F ≠ B := TriangleND.points_ne_of_collinear_of_not_collinear2 not_collinear_ABC collinear_FCA
  -- Claim : $G \ne C$.
  G_ne_C : G ≠ C := TriangleND.points_ne_of_collinear_of_not_collinear3 not_collinear_ABC collinear_GAB
  -- $\frac{EB}{EC} \cdot \frac{FC}{FA} \cdot \frac{GA}{GB} = -1$.
  ratio_mul_eq_minus_one : (divratio E B C) * (divratio F C A) * (divratio G A B) = -1

theorem Ceva_converse_theorem {P : Type*} [EuclideanPlane P] (e : Setting P) : ∃ (X : P), (X LiesOn (LIN e.A e.E e.E_ne_A)) ∧ (X LiesOn (LIN e.B e.F e.F_ne_B)) ∧ (X LiesOn (LIN e.C e.G e.G_ne_C)) := by
  let D := Line.inx (LIN e.A e.E (TriangleND.points_ne_of_collinear_of_not_collinear1 e.not_collinear_ABC e.collinear_EBC)) (LIN e.B e.F (TriangleND.points_ne_of_collinear_of_not_collinear2 e.not_collinear_ABC e.collinear_FCA)) (TriangleND.not_parallel_of_not_collinear_of_collinear_collinear e.not_collinear_ABC e.collinear_EBC e.collinear_FCA)
  have ratiomul : (divratio e.E e.B e.C) * (divratio e.F e.C e.A) * (divratio e.G e.A e.B) = -1 := e.ratio_mul_eq_minus_one
  have E_ne_C : e.E ≠ e.C := by
    intro h0
    have h1 : divratio e.E e.B e.C = 0 := by
      rw [h0]
      exact ratio_eq_zero_of_point_eq2 e.C e.B
    rw [h1] at ratiomul
    field_simp at ratiomul
  have E_ne_B : e.E ≠ e.B := by
    intro h0
    have h1 : divratio e.E e.B e.C = 0 := by
      rw [h0]
      exact ratio_eq_zero_of_point_eq1 e.B e.C
    rw [h1] at ratiomul
    field_simp at ratiomul
  have F_ne_A : e.F ≠ e.A := by
    intro h0
    have h1 : divratio e.F e.C e.A = 0 := by
      rw [h0]
      exact ratio_eq_zero_of_point_eq2 e.A e.C
    rw [h1] at ratiomul
    field_simp at ratiomul
  have F_ne_C : e.F ≠ e.C := by
    intro h0
    have h1 : divratio e.F e.C e.A =0 := by
      rw [h0]
      exact ratio_eq_zero_of_point_eq1 e.C e.A
    rw [h1] at ratiomul
    field_simp at ratiomul
  /-
  have collinear_DAE : Collinear e.A e.E D := Line.pt_pt_linear (TriangleND.points_ne_of_collinear_of_not_collinear1 e.not_collinear_ABC e.collinear_EBC) (Line.inx_lies_on_fst (TriangleND.not_parallel_of_not_collinear_of_collinear_collinear e.not_collinear_ABC e.collinear_EBC e.collinear_FCA))
  -/
  have abd_nd : ¬ Collinear e.A e.B D := (TriangleND.intersection_not_collinear_of_nondegenerate e.not_collinear_ABC e.collinear_EBC e.collinear_FCA E_ne_B E_ne_C F_ne_A F_ne_C D rfl).1
  have bcd_nd : ¬ Collinear e.B e.C D := (TriangleND.intersection_not_collinear_of_nondegenerate e.not_collinear_ABC e.collinear_EBC e.collinear_FCA E_ne_B E_ne_C F_ne_A F_ne_C D rfl).2.1
  have cad_nd : ¬ Collinear e.C e.A D := (TriangleND.intersection_not_collinear_of_nondegenerate e.not_collinear_ABC e.collinear_EBC e.collinear_FCA E_ne_B E_ne_C F_ne_A F_ne_C D rfl).2.2
  sorry

end Ceva's_converse_theorem

end EuclidGeom
