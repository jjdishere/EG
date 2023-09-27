import EuclideanGeometry.Foundation.Index

noncomputable section


namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]



namespace Exercise_XT_8_1_11
/- Let $\triangle ABC$ be a triangle. Let $X_1$, $Y_1$, and $Z_1$ be points on the extensions of $BC$, $CA$, $AB$, respectively. Let $X_2$, $Y_2$, and $Z_2$ be points on the extensions of $CB$, $AC$, $BA$, respectively.

Prove that $\angle AY_1Z_2 + \angle BZ_1X_2 + \angle CX_1Y_2 + \angle Y_1Z_2A + \angle Z_1X_2B + \angle X_1Y_2C = 2 \cdot \pi$.
-/ 

-- Let $\triangle ABC$ be a nondegenerate triangle.
variable {A B C : P} {hnd : ¬ colinear A B C}

lemma c_ne_b : C ≠ B := sorry
lemma b_ne_a : B ≠ A := sorry
lemma a_ne_c : A ≠ C := sorry

variable {X₁ Y₁ Z₁ : P} {hx₁ : X₁ LiesInt (SEG_nd B C c_ne_b).extension} {hy₁ : Y₁ LiesInt (SEG_nd C A a_ne_c).extension} {hz₁ : Z₁ LiesInt (SEG_nd A B b_ne_a).extension}

variable {X₂ Y₂ Z₂ : P} {hx₂ : X₂ LiesInt (SEG_nd C B c_ne_b.symm).extension} {hy₂ : Y₂ LiesInt (SEG_nd A C a_ne_c.symm).extension} {hz₂ : Z₂ LiesInt (SEG_nd B A b_ne_a.symm).extension}

lemma c_ne_x1 : C ≠ X₁ := sorry
lemma b_ne_x2 : B ≠ X₂:= sorry
lemma a_ne_y1 : A ≠ Y₁ := sorry
lemma c_ne_y2 : C ≠ Y₂ := sorry
lemma b_ne_z1 : B ≠ Z₁ := sorry
lemma a_ne_z2 : A ≠ Z₂ := sorry
lemma x1_ne_y2 : X₁ ≠ Y₂ := sorry
lemma y1_ne_z2 : Y₁ ≠ Z₂ := sorry
lemma z1_ne_x2 : Z₁ ≠ X₂ := sorry

theorem XT_8_1_11 : ∠ A Y₁ Z₂ a_ne_y1 y1_ne_z2.symm + ∠ B Z₁ X₂ b_ne_z1 z1_ne_x2.symm + ∠ C X₁ Y₂ c_ne_x1 x1_ne_y2.symm + ∠ Y₁ Z₂ A y1_ne_z2 a_ne_z2 + ∠ Z₁ X₂ B z1_ne_x2 b_ne_x2 + ∠ X₁ Y₂ C x1_ne_y2 c_ne_y2  = 2 * π := sorry

end Exercise_XT_8_1_11
end EuclidGeom

