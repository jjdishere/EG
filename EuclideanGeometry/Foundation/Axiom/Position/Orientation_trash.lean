import EuclideanGeometry.Foundation.Axiom.Position.Orientation

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

lemma liesonleft_ne_pts {A B C : P} (hne : B ≠ A) (h : C LiesOnLeft (DLIN A B hne)) : (C ≠ A) ∧ (C ≠ B) := sorry

theorem liesonleft_angle_ispos {A B C : P} (hne : B ≠ A) (h : C LiesOnLeft (DLIN A B hne)) : (∠ A C B (liesonleft_ne_pts hne h).1.symm (liesonleft_ne_pts hne h).2.symm).IsPos := sorry

lemma liesonright_ne_pts {A B C : P} (hne : B ≠ A) (h : C LiesOnRight (DLIN A B hne)) : (C ≠ A) ∧ (C ≠ B) := sorry

theorem liesonright_angle_isneg {A B C : P} (hne : B ≠ A) (h : C LiesOnRight (DLIN A B hne)) : (∠ A C B (liesonright_ne_pts hne h).1.symm (liesonright_ne_pts hne h).2.symm).IsNeg := sorry

theorem liesonleft_iff_liesonright_reverse {A : P} {l : DirLine P} : A LiesOnLeft l ↔ A LiesOnRight l.reverse := sorry

theorem DirLine.lieson_or_liesonleft_or_liesonright (A : P) (l : DirLine P) : (A LiesOn l) ∨ (A LiesOnLeft l) ∨ (A LiesOnRight l) := sorry

end EuclidGeom
