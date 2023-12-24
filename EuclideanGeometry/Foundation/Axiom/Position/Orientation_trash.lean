import EuclideanGeometry.Foundation.Axiom.Position.Orientation

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

lemma liesonleft_ne_pts {A B C : P} [hne : PtNe B A] (h : C LiesOnLeft (DLIN A B)) : (C ≠ A) ∧ (C ≠ B) := sorry

theorem liesonleft_angle_ispos {A B C : P} [hne : PtNe B A] (h : C LiesOnLeft (DLIN A B)) : (∠ A C B (liesonleft_ne_pts h).1.symm (liesonleft_ne_pts h).2.symm).IsPos := sorry

lemma liesonright_ne_pts {A B C : P} [hne : PtNe B A] (h : C LiesOnRight (DLIN A B)) : (C ≠ A) ∧ (C ≠ B) := sorry

theorem liesonright_angle_isneg {A B C : P} [hne : PtNe B A] (h : C LiesOnRight (DLIN A B)) : (∠ A C B (liesonright_ne_pts h).1.symm (liesonright_ne_pts h).2.symm).IsNeg := sorry

theorem liesonleft_iff_liesonright_reverse {A : P} {l : DirLine P} : A LiesOnLeft l ↔ A LiesOnRight l.reverse := sorry

theorem DirLine.lieson_or_liesonleft_or_liesonright (A : P) (l : DirLine P) : (A LiesOn l) ∨ (A LiesOnLeft l) ∨ (A LiesOnRight l) := sorry
--Guan Nailin
theorem eq_toDir_of_parallel_and_same_side {A B C D : P} {h : A ≠ B} {h₁ : C ≠ A} {h₂ : D ≠ B} {para : (SEG_nd A C h₁) ∥ (SEG_nd B D h₂)} {side : odist_sign C (SEG_nd A B h.symm) = odist_sign D (SEG_nd A B h.symm)} : (SEG_nd A C h₁).toDir = (SEG_nd B D h₂).toDir := by sorry
--Guan Nailin
theorem neg_toDir_of_parallel_and_opposite_side {A B C D : P} {h : A ≠ B} {h₁ : C ≠ A} {h₂ : D ≠ B} {para : (SEG_nd A C h₁) ∥ (SEG_nd B D h₂)} {side : odist_sign C (SEG_nd A B h.symm) = -odist_sign D (SEG_nd A B h.symm)} : (SEG_nd A C h₁).toDir = -(SEG_nd B D h₂).toDir := by sorry

end EuclidGeom
