import EuclideanGeometry.Foundation.Axiom.Position.Orientation

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem liesonleft_iff_liesonright_reverse {A : P} {l : DirLine P} : A LiesOnLeft l ↔ A LiesOnRight l.reverse := by
  have : odist A l.reverse = -odist A l := by
    apply odist_reverse_eq_neg_odist A l
  unfold IsOnLeftSide
  unfold IsOnRightSide
  constructor
  · intro P
    simp only [this]
    linarith
  · intro P
    simp only [this] at P
    linarith

--simple corollary of "not_colinear_of_LiesOnLeft_or_LiesOnRight"
lemma liesonleft_ne_pts {A B C : P} [hne : PtNe B A] (h : C LiesOnLeft (DLIN A B)) : (C ≠ A) ∧ (C ≠ B) := by
  have h': C LiesOnLeft (RAY A B) := by exact h
  have : ¬ colinear A B C := by
    apply not_colinear_of_LiesOnLeft_or_LiesOnRight
    simp only [h', true_or]
  have c_ne_a : C ≠ A := (ne_of_not_colinear this).2.1.symm
  have c_ne_b : C ≠ B := (ne_of_not_colinear this).1
  simp only [ne_eq, c_ne_a, not_false_eq_true, c_ne_b, and_self]

theorem liesonleft_angle_ispos {A B C : P} [hne : PtNe B A] (h : C LiesOnLeft (DLIN A B)) : (∠ A C B (liesonleft_ne_pts h).1.symm (liesonleft_ne_pts h).2.symm).IsPos := sorry --better to be discussed after triangle

lemma liesonright_ne_pts {A B C : P} [hne : PtNe B A] (h : C LiesOnRight (DLIN A B)) : (C ≠ A) ∧ (C ≠ B) := by
  have h': C LiesOnRight (RAY A B) := by exact h
  have : ¬ colinear A B C := by
    apply not_colinear_of_LiesOnLeft_or_LiesOnRight
    simp only [h', or_true]
  have c_ne_a : C ≠ A := (ne_of_not_colinear this).2.1.symm
  have c_ne_b : C ≠ B := (ne_of_not_colinear this).1
  simp only [ne_eq, c_ne_a, not_false_eq_true, c_ne_b, and_self]

theorem liesonright_angle_isneg {A B C : P} [hne : PtNe B A] (h : C LiesOnRight (DLIN A B)) : (∠ A C B (liesonright_ne_pts h).1.symm (liesonright_ne_pts h).2.symm).IsNeg := sorry --better to be discussed after triangle

theorem DirLine.lieson_or_liesonleft_or_liesonright (A : P) (l : DirLine P) : (A LiesOn l) ∨ (A LiesOnLeft l) ∨ (A LiesOnRight l) := sorry --proven in main file

--Guan Nailin
theorem eq_toDir_of_parallel_and_same_side {A B C D : P} {h : A ≠ B} {h₁ : C ≠ A} {h₂ : D ≠ B} {para : (SEG_nd A C h₁) ∥ (SEG_nd B D h₂)} {side : IsOnSameSide C D (SEG_nd A B h.symm)} : (SEG_nd A C h₁).toDir = (SEG_nd B D h₂).toDir := by
  have Proj : (SEG_nd A C h₁).toProj = (SEG_nd B D h₂).toProj := by
    exact para
  have eq_or_neg : ((SEG_nd A C h₁).toDir = (SEG_nd B D h₂).toDir) ∨ ((SEG_nd A C h₁).toDir = -(SEG_nd B D h₂).toDir) := by
    sorry
  rcases eq_or_neg with eq|neg
  · exact eq
  · sorry
--Guan Nailin
theorem neg_toDir_of_parallel_and_opposite_side {A B C D : P} {h : A ≠ B} {h₁ : C ≠ A} {h₂ : D ≠ B} {para : (SEG_nd A C h₁) ∥ (SEG_nd B D h₂)} {side : IsOnOppositeSide C D (SEG_nd A B h.symm)} : (SEG_nd A C h₁).toDir = -(SEG_nd B D h₂).toDir := by
  have Proj : (SEG_nd A C h₁).toProj = (SEG_nd B D h₂).toProj := by
    exact para
  have eq_or_neg : ((SEG_nd A C h₁).toDir = (SEG_nd B D h₂).toDir) ∨ ((SEG_nd A C h₁).toDir = -(SEG_nd B D h₂).toDir) := by
    sorry
  rcases eq_or_neg with eq|neg
  · sorry
  · exact neg

end EuclidGeom
