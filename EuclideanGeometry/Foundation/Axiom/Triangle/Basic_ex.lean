import EuclideanGeometry.Foundation.Axiom.Triangle.Basic

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] (tr : Triangle P) (tr_nd : TriangleND P)

namespace Triangle

def perm_vertices : (Triangle P) where
  point₁ := tr.point₂
  point₂ := tr.point₃
  point₃ := tr.point₁

-- We decide not to define reverse permutation of triangles, just do composition twice.

-- Permuting three times returns to the original triangle.
theorem eq_self_of_perm_vertices_three_times : tr.perm_vertices.perm_vertices.perm_vertices = tr := rfl

-- flip vertices for triangles means to flip the second and the third vertices.

def flip_vertices : (Triangle P) where
  point₁ := tr.point₁
  point₂ := tr.point₃
  point₃ := tr.point₂

theorem eq_self_of_flip_vertices_twice : tr.flip_vertices.flip_vertices = tr := rfl

-- Not sure this is the best theorem to p
theorem eq_flip_of_perm_twice_of_perm_flip_vertices : tr.flip_vertices.perm_vertices.perm_vertices = tr.perm_vertices.flip_vertices := rfl

theorem is_inside_of_is_inside_perm_vertices (tr : Triangle P) (p : P) (inside : p LiesInt tr) : p LiesInt tr.perm_vertices := by
  sorry

theorem is_inside_of_is_inside_flip_vertices (tr : Triangle P) (p : P) (inside : p LiesInt tr) : p LiesInt tr.flip_vertices := by
  sorry

end Triangle

namespace TriangleND

def perm_vertices : (TriangleND P) := ⟨tr_nd.1.perm_vertices, flip_colinear_snd_trd.mt $ flip_colinear_fst_snd.mt tr_nd.2⟩

def flip_vertices : (TriangleND P) := ⟨tr_nd.1.flip_vertices, flip_colinear_snd_trd.mt tr_nd.2⟩

theorem eq_self_of_perm_vertices_three_times : tr_nd.perm_vertices.perm_vertices.perm_vertices = tr_nd := rfl
  --exact tr_nd.1.eq_self_of_perm_vertices_three_times

theorem eq_self_of_flip_vertices_twice : tr_nd.flip_vertices.flip_vertices = tr_nd := rfl

theorem eq_flip_of_perm_twice_of_perm_flip_vertices : tr_nd.flip_vertices.perm_vertices.perm_vertices = tr_nd.perm_vertices.flip_vertices := rfl

-- compatibility of permutation/flip of vertices with orientation of the triangle

theorem same_orient_of_perm_vertices : tr_nd.is_cclock = (tr_nd.perm_vertices.is_cclock) := by sorry

theorem reverse_orient_of_flip_vertices : tr_nd.is_cclock = ¬ tr_nd.flip_vertices.is_cclock := by sorry

theorem is_inside_of_is_inside_perm_vertices (tr_nd : Triangle P) (p : P) (inside : p LiesInt tr_nd) : p LiesInt tr_nd.perm_vertices := by sorry

theorem is_inside_of_is_inside_flip_vertices (tr_nd : Triangle P) (p : P) (inside : p LiesInt tr_nd) : p LiesInt tr_nd.flip_vertices := by sorry

end TriangleND


/-
theorem eq_self_of_flip_vertices_twice : tr.flip_vertices.flip_vertices = tr := by sorry

-- Not sure this is the best theorem to p
theorem eq_flip_of_perm_twice_of_perm_flip_vertices : tr.flip_vertices.perm_vertices.perm_vertices = tr.perm_vertices.flip_vertices := by sorry

-- compatibility of permutation/flip of vertices with orientation of the triangle

theorem same_orient_of_perm_vertices : tr_nd.is_cclock = (tr_nd.perm_vertices.is_cclock) := by sorry

theorem reverse_orient_of_flip_vertices : tr_nd.is_cclock = ¬ tr_nd.flip_vertices.is_cclock := by sorry

-- compatiblility of permutation/flip of vertices with inside triangle

theorem is_inside_of_is_inside_perm_vertices (tr : Triangle P) (p : P) (inside : p LiesInt tr) : p LiesInt tr.perm_vertices := by sorry

theorem is_inside_of_is_inside_flip_vertices (tr : Triangle P) (p : P) (inside : p LiesInt tr) : p LiesInt tr.flip_vertices := by sorry
-/

/- In the following theorems, we show that the points on the interior of different edges of triangle are not equal.-/

namespace Triangle

/-
theorem ne_vertex_of_lies_int_fst_edge (tr : Triangle P) {A : P} (h : A LiesInt tr.edge₁) : A ≠ tr.point₁ ∧  A ≠ tr.point₂ ∧ A ≠ tr.point₃ := sorry

theorem ne_vertex_of_lies_int_snd_edge (tr : Triangle P) {A : P} (h : A LiesInt tr.edge₂) : A ≠ tr.point₁ ∧  A ≠ tr.point₂ ∧ A ≠ tr.point₃ := sorry

theorem ne_vertex_of_lies_int_trd_edge (tr : Triangle P) {A : P} (h : A LiesInt tr.edge₃) : A ≠ tr.point₁ ∧  A ≠ tr.point₂ ∧ A ≠ tr.point₃ := sorry
-/

theorem lie_on_snd_and_trd_edge_of_fst_vertex (tr : Triangle P) : tr.point₁ LiesOn tr.edge₂ ∧ tr.point₁ LiesOn tr.edge₃ := sorry

theorem lie_on_trd_and_fst_edge_of_snd_vertex (tr : Triangle P) : tr.point₁ LiesOn tr.edge₂ ∧ tr.point₁ LiesOn tr.edge₃ := sorry

theorem lie_on_fst_and_snd_edge_of_trd_vertex (tr : Triangle P) : tr.point₁ LiesOn tr.edge₂ ∧ tr.point₁ LiesOn tr.edge₃ := sorry

end Triangle

namespace TriangleND

theorem ne_vertex_of_lies_int_fst_edge (tr_nd : TriangleND P) {A : P} (h : A LiesInt tr_nd.edge₁) : A ≠ tr_nd.point₁ ∧  A ≠ tr_nd.point₂ ∧ A ≠ tr_nd.point₃ := sorry

theorem ne_vertex_of_lies_int_snd_edge (tr_nd : TriangleND P) {A : P} (h : A LiesInt tr_nd.edge₂) : A ≠ tr_nd.point₁ ∧  A ≠ tr_nd.point₂ ∧ A ≠ tr_nd.point₃ := sorry

theorem ne_vertex_of_lies_int_trd_edge (tr_nd : TriangleND P) {A : P} (h : A LiesInt tr_nd.edge₃) : A ≠ tr_nd.point₁ ∧  A ≠ tr_nd.point₂ ∧ A ≠ tr_nd.point₃ := sorry

theorem lie_on_snd_and_trd_edge_of_fst_vertex (tr_nd : Triangle P) : tr_nd.point₁ LiesOn tr_nd.edge₂ ∧ tr_nd.point₁ LiesOn tr_nd.edge₃ := by sorry

theorem lie_on_trd_and_fst_edge_of_snd_vertex (tr_nd : Triangle P) : tr_nd.point₁ LiesOn tr_nd.edge₂ ∧ tr_nd.point₁ LiesOn tr_nd.edge₃ := sorry

theorem lie_on_fst_and_snd_edge_of_trd_vertex (tr_nd : Triangle P) : tr_nd.point₁ LiesOn tr_nd.edge₂ ∧ tr_nd.point₁ LiesOn tr_nd.edge₃ := sorry

/- Given a nondegenerate triangle, any point that lies in the interior of the first edge does not lie on the second or the third edge. -/

theorem not_lie_on_snd_and_trd_of_int_fst (trind : TriangleND P){A : P} (h: A LiesInt trind.1.edge₁) : (¬ A LiesOn trind.1.edge₂) ∧ (¬ A LiesOn trind.1.edge₃) := sorry

theorem not_lie_on_trd_and_fst_of_int_snd (trind : TriangleND P) {A : P} (h: A LiesInt trind.1.edge₂) : (¬ A LiesOn trind.1.edge₃) ∧ (¬ A LiesOn trind.1.edge₁) := sorry

theorem not_lie_on_fst_and_snd_of_int_trd (trind : TriangleND P){A : P} (h: A LiesInt trind.1.edge₃) : (¬ A LiesOn trind.1.edge₁) ∧ (¬ A LiesOn trind.1.edge₂) := sorry


end TriangleND

namespace Triangle

theorem edge_eq_edge_of_flip_vertices (tr : Triangle P) : tr.edge₁.length = tr.flip_vertices.edge₁.length ∧ tr.edge₂.length = tr.flip_vertices.edge₃.length ∧ tr.edge₃.length = tr.flip_vertices.edge₂.length := by sorry

theorem edge_eq_edge_of_perm_vertices (tr : Triangle P) : tr.edge₁.length = tr.perm_vertices.edge₂.length ∧ tr.edge₂.length = tr.perm_vertices.edge₃.length ∧ tr.edge₃.length = tr.perm_vertices.edge₁.length := by sorry

theorem nd_iff_nd_of_perm_vertices: tr.IsND ↔ tr.perm_vertices.IsND := by sorry

end Triangle

namespace TriangleND

theorem edge_eq_edge_of_flip_vertices (tr_nd : TriangleND P) : tr_nd.edge₁.length = tr_nd.flip_vertices.edge₁.length ∧ tr_nd.edge₂.length = tr_nd.flip_vertices.edge₃.length ∧ tr_nd.edge₃.length = tr_nd.flip_vertices.edge₂.length := by sorry

theorem edge_eq_edge_of_perm_vertices (tr_nd : TriangleND P) : tr_nd.edge₁.length = tr_nd.perm_vertices.edge₂.length ∧ tr_nd.edge₂.length = tr_nd.perm_vertices.edge₃.length ∧ tr_nd.edge₃.length = tr_nd.perm_vertices.edge₁.length := by sorry

theorem angle_eq_neg_angle_of_flip_vertices (tr_nd : TriangleND P) : tr_nd.angle₁.value = - tr_nd.flip_vertices.angle₁.value ∧ tr_nd.angle₂.value = -tr_nd.flip_vertices.angle₃.value ∧ tr_nd.angle₃.value = -tr_nd.flip_vertices.angle₂.value := by sorry

theorem angle_eq_angle_of_perm_vertices (tr_nd : TriangleND P) : tr_nd.angle₁.value = tr_nd.perm_vertices.angle₂.value ∧ tr_nd.angle₂.value = tr_nd.perm_vertices.angle₃.value ∧ tr_nd.angle₃.value = tr_nd.perm_vertices.angle₁.value := by sorry

end TriangleND

namespace TriangleND

section cclock_and_odist
/-
Using this section with "odist" and permutation of TriangleND , we are able to convert odist_sign between lines.
This method together with "same_side" and "opposite_side",(which would be add later)
can probably solve all the problems we can fore-see currently about
the uniqueness of the graph and how to use it to determine the orientation.
-/
variable (tr_nd : TriangleND P)

theorem iscclock_iff_liesonleft₃ (tr_nd : TriangleND P) : tr_nd.is_cclock = tr_nd.1.3 LiesOnLeft tr_nd.edge_nd₃ := by
  unfold is_cclock
  unfold IsOnLeftSide
  have h : (0 < tr_nd.oarea) = (0 < odist tr_nd.1.3 tr_nd.edge_nd₃) := by
    have : EuclidGeom.oarea tr_nd.1.1 tr_nd.1.2 tr_nd.1.3 = tr_nd.edge₃.length * odist tr_nd.1.3 tr_nd.edge_nd₃ /2 := by
      apply oarea_eq_length_mul_odist_div_two
    unfold oarea
    unfold Triangle.oarea
    have pos : tr_nd.edge_nd₃.length > 0 := by
      apply EuclidGeom.length_pos
    simp only [this, eq_iff_iff]
    symm
    constructor
    · intro p
      positivity
    · intro p
      apply pos_of_mul_pos_left (b := tr_nd.edge₃.length/2)
      · have simp : odist tr_nd.1.3 tr_nd.edge_nd₃ * (tr_nd.edge₃.length / 2) = tr_nd.edge₃.length * odist tr_nd.1.3 tr_nd.edge_nd₃ / 2  := by ring
        rw [simp]
        exact p
      · positivity
  exact h
theorem iscclock_iff_liesonleft₁ (tr_nd : TriangleND P) : tr_nd.is_cclock = tr_nd.1.1 LiesOnLeft tr_nd.edge_nd₁ := by
  have h : tr_nd.is_cclock = (tr_nd.perm_vertices.is_cclock) := by
    apply same_orient_of_perm_vertices
  simp only [h]
  apply iscclock_iff_liesonleft₃
theorem iscclock_iff_liesonleft₂ (tr_nd : TriangleND P) : tr_nd.is_cclock = tr_nd.1.2 LiesOnLeft tr_nd.edge_nd₂ := by
  have h : tr_nd.is_cclock = (tr_nd.perm_vertices.is_cclock) := by
    apply same_orient_of_perm_vertices
  simp only [h]
  apply iscclock_iff_liesonleft₁

theorem eq_cclock_of_IsOnSameSide (A B C D : P) [hne : PtNe B A] (h : IsOnSameSide C D (RAY A B)) : (TRI_nd A B C (not_colinear_of_IsOnSameSide A B C D h).1).is_cclock = (TRI_nd A B D (not_colinear_of_IsOnSameSide A B C D h).2).is_cclock := by
  have c : (TRI_nd A B C (not_colinear_of_IsOnSameSide A B C D h).1).is_cclock = C LiesOnLeft (SEG_nd A B) := by
    apply iscclock_iff_liesonleft₃
  have d : (TRI_nd A B D (not_colinear_of_IsOnSameSide A B C D h).2).is_cclock = D LiesOnLeft (SEG_nd A B) := by
    apply iscclock_iff_liesonleft₃
  have h0 : C LiesOnLeft (SEG_nd A B) = D LiesOnLeft (SEG_nd A B) := by
    apply LiesOnLeft_iff_LiesOnLeft_of_IsOnSameSide
    exact h
  simp only [c, h0, d]

theorem anti_cclock_of_IsOnOppositeSide (A B C D : P) [hne : PtNe B A] (h : IsOnOppositeSide C D (SEG_nd A B)) : (TRI_nd A B C (not_colinear_of_IsOnOppositeSide A B C D h).1).is_cclock → ¬ (TRI_nd A B D (not_colinear_of_IsOnOppositeSide A B C D h).2).is_cclock := by
  have c : (TRI_nd A B C (not_colinear_of_IsOnOppositeSide A B C D h).1).is_cclock = C LiesOnLeft (SEG_nd A B) := by
    apply iscclock_iff_liesonleft₃
  have d : (TRI_nd A B D (not_colinear_of_IsOnOppositeSide A B C D h).2).is_cclock = D LiesOnLeft (SEG_nd A B) := by
    apply iscclock_iff_liesonleft₃
  simp only [c,d]
  have h0 : C LiesOnLeft SEG_nd A B = D LiesOnLeft (SEG_nd A B).reverse := by
    calc
      _= C LiesOnLeft (SEG_nd A B).toDirLine := by rfl
      _= D LiesOnLeft (SEG_nd A B).toDirLine.reverse := by
        apply LiesOnLeft_iff_LiesOnLeft_rev_of_IsOnOppositeSide
        exact h
      _= D LiesOnLeft (SEG_nd A B).reverse.toDirLine := by
        congr
        exact EuclidGeom.SegND.toDirLine_rev_eq_rev_toDirLine
      _= D LiesOnLeft (SEG_nd A B).reverse := by rfl
  simp only [h0]
  unfold IsOnLeftSide
  intro P
  have : odist D (SEG_nd A B).reverse = - odist D (SEG_nd A B) := by
    apply odist_reverse_eq_neg_odist
  rw [this] at P
  linarith



end cclock_and_odist

end TriangleND

end EuclidGeom
