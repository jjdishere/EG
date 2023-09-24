import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

section compatibility
-- `eq_toProj theorems should be relocate to file parallel using parallel`.
variable (A B : P) (h : B ≠ A) (ray : Ray P) (seg_nd : Seg_nd P)

section pt_pt

theorem line_of_pt_pt_eq_rev : LIN A B h = LIN B A h.symm := sorry

theorem fst_pt_lies_on_line_of_pt_pt {A B : P} (h : B ≠ A) : A LiesOn LIN A B h := Or.inl (Ray.source_lies_on (RAY A B h))

theorem snd_pt_lies_on_line_of_pt_pt {A B : P} (h : B ≠ A) : B LiesOn LIN A B h := sorry

-- The first point and the second point in Line.mk_pt_pt LiesOn the line it make.

theorem pt_lies_on_line_of_pt_pt_of_ne {A B : P} (h: B ≠ A) : A LiesOn LIN A B h ∧ B LiesOn LIN A B h := by
  constructor
  exact fst_pt_lies_on_line_of_pt_pt h
  exact snd_pt_lies_on_line_of_pt_pt h

/- two point determines a line -/

theorem eq_line_of_pt_pt_of_ne {A B : P} {l : Line P} (h : B ≠ A) (ha : A LiesOn l) (hb : B LiesOn l) : LIN A B h = l := by
  revert l
  unfold Line
  rw [Quotient.forall (s := same_extn_line.setoid)]
  intro ray ha hb
  unfold Line.mk_pt_pt
  rw [Quotient.eq]
  unfold lies_on Line.instCarrierLine Carrier.carrier Line.carrier at ha hb
  simp only at ha hb
  rw [@Quotient.lift_mk _ _ same_extn_line.setoid _ _ _] at ha hb
  show same_extn_line (RAY A B h) ray
  sorry

theorem eq_of_pt_pt_lies_on_of_ne {A B : P} (h : B ≠ A) {l₁ l₂ : Line P}(hA₁ : A LiesOn l₁) (hB₁ : B LiesOn l₁) (hA₂ : A LiesOn l₂) (hB₂ : B LiesOn l₂) : l₁ = l₂ := sorry

end pt_pt

section pt_proj

theorem pt_lies_on_of_mk_pt_proj (proj : Proj) : A LiesOn Line.mk_pt_proj A proj := sorry

theorem proj_eq_of_mk_pt_proj (proj : Proj) : (Line.mk_pt_proj A proj).toProj = proj := sorry

end pt_proj

section coercion

-- The line defined from a nontrivial segment is equal to the line defined from the ray associated this nontrivial segment

theorem Seg_nd.toLine_eq_toRay_toLine (seg_nd : Seg_nd P) : seg_nd.toLine = (seg_nd.toRay).toLine := rfl

theorem line_of_pt_pt_eq_ray_toLine {A B : P} (h : B ≠ A) : LIN A B h = Ray.toLine (RAY A B h) := rfl

theorem line_of_pt_pt_eq_seg_nd_toLine {A B : P} (h : B ≠ A) : LIN A B h = Seg_nd.toLine ⟨SEG A B, h⟩ := rfl

theorem Ray.source_lies_on_toLine (l : Ray P) : l.source LiesOn l.toLine := sorry

theorem Seg_nd.source_lies_on_toLine (s : Seg_nd P) : s.1.source LiesOn s.toLine := sorry

theorem Seg_nd.target_lies_on_toLine (s : Seg_nd P) : s.1.target LiesOn s.toLine := sorry

theorem Ray.toLine_eq_rev_toLine : ray.toLine = ray.reverse.toLine := sorry

theorem Seg_nd.toLine_eq_rev_toLine : seg_nd.toLine = seg_nd.reverse.toLine := sorry

theorem toLine_eq_extn_toLine : seg_nd.toLine = seg_nd.extension.toLine := sorry

theorem lies_on_extn_or_rev_extn_iff_lies_on_toLine_of_not_lies_on {A : P} (seg_nd : Seg_nd P) (h : ¬ A LiesInt seg_nd.1) : A LiesOn seg_nd.toLine ↔ (A LiesOn seg_nd.extension) ∨ (A LiesOn seg_nd.reverse.extension) := sorry

/- Two lines are equal iff they have the same carrier -/

theorem lies_on_iff_lies_on_iff_line_eq_line (l₁ l₂ : Line P) : (∀ A : P, A LiesOn l₁ ↔ A LiesOn l₂) ↔ l₁ = l₂ := by
  constructor
  · intro hiff
    revert l₁ l₂
    unfold Line
    rw [Quotient.forall (s := same_extn_line.setoid)]
    intro r₁
    rw [Quotient.forall (s := same_extn_line.setoid)]
    intro r₂
    intro h
    unfold lies_on Line.instCarrierLine Carrier.carrier Line.carrier at h
    simp only at h
    rw [@Quotient.lift_mk _ _ same_extn_line.setoid _ _ _, @Quotient.lift_mk _ _ same_extn_line.setoid _ _ _] at h
    rw [Quotient.eq]
    show same_extn_line r₁ r₂
    sorry
  · intro e
    rw [e]
    simp only [forall_const]

-- If a point lies on a ray, then it lies on the line associated to the ray.
theorem Ray.lies_on_toLine_of_lie_on {A : P} {r : Ray P} (h : A LiesOn r) : A LiesOn (r.toLine) := sorry

theorem Seg_nd.lies_on_toLine_of_lie_on {A : P} {s : Seg_nd P} (h : A LiesOn s.1) : A LiesOn (s.toLine) := sorry

theorem line_toProj_eq_seg_nd_toProj_of_lies_on {A B : P} {l : Line P} (ha : A LiesOn l) (hb : B LiesOn l) (hab : B ≠ A) : Seg_nd.toProj ⟨SEG A B, hab⟩ = l.toProj := sorry

theorem Ray.toProj_eq_toLine_toProj (ray : Ray P) : ray.toProj = ray.toLine.toProj := rfl

theorem Seg_nd.toProj_eq_toLine_toProj (seg_nd : Seg_nd P) : seg_nd.toProj = seg_nd.toLine.toProj := rfl

theorem lies_on_iff_eq_toProj {A B : P} {l : Line P} (h : B ≠ A) (hA : A LiesOn l) : B LiesOn l ↔ (SEG_nd A B h).toProj = l.toProj := sorry

end coercion

section colinear

theorem lies_on_line_of_pt_pt_iff_colinear {A B : P} (h : B ≠ A) : ∀ X : P, (X LiesOn (LIN A B h)) ↔ colinear A B X := by
  intro X
  constructor
  intro hx
  apply (LIN A B h).linear
  exact fst_pt_lies_on_line_of_pt_pt h
  exact snd_pt_lies_on_line_of_pt_pt h
  exact hx
  intro c
  apply (LIN A B h).maximal
  exact fst_pt_lies_on_line_of_pt_pt h
  exact snd_pt_lies_on_line_of_pt_pt h
  exact h
  exact c

-- This is also a typical proof that shows how to use linear, maximal, nontriv of a line. Please write it shorter in future.

theorem lies_on_iff_colinear_of_ne_lies_on_lies_on {A B : P} {l : Line P} (h : B ≠ A) (ha : A LiesOn l) (hb : B LiesOn l) : ∀ C : P, (C LiesOn l) ↔ colinear A B C := by
  intro C
  constructor
  intro hc
  apply l.linear
  exact ha
  exact hb
  exact hc
  intro c
  apply l.maximal
  exact ha
  exact hb
  exact h
  exact c

theorem colinear_iff_exist_line_lies_on (A B C : P) : colinear A B C ↔ ∃ l : Line P, (A LiesOn l) ∧ (B LiesOn l) ∧ (C LiesOn l) := by
  sorry

end colinear

end compatibility

section Archimedean_property

-- there are two distinct points on a line

theorem exists_ne_pt_pt_lies_on_of_line (A : P) (l : Line P) : ∃ B : P, B LiesOn l ∧ B ≠ A := by
  rcases l.nontriv with ⟨X, ⟨Y, _⟩⟩
  by_cases A = X
  · use Y
    rw [h]
    tauto
  · use X
    tauto

theorem lies_on_of_Seg_nd_toProj_eq_toProj {A B : P} {l : Line P} (ha : A LiesOn l) (hab : B ≠ A) (hp : Seg_nd.toProj ⟨SEG A B, hab⟩ = l.toProj) : B LiesOn l := by
  rcases exists_ne_pt_pt_lies_on_of_line A l with ⟨X, h⟩
  let g := line_toProj_eq_seg_nd_toProj_of_lies_on ha h.1 h.2
  rw [← hp] at g
  unfold Seg_nd.toProj Seg_nd.toVec_nd at g
  simp only [ne_eq] at g
  have c : colinear A X B := by
    rw [← iff_true (colinear A X B), ← eq_iff_iff]
    unfold colinear colinear_of_nd
    simp [g]
    by_cases (B = X ∨ A = B ∨ X = A)
    · simp only [h, dite_eq_ite]
    · simp only [h, dite_eq_ite]
  exact (lies_on_iff_colinear_of_ne_lies_on_lies_on h.2 ha h.1 B).2 c

theorem Seg_nd_toProj_eq_toProj_iff_lies_on {A B : P} {l : Line P} (ha : A LiesOn l) (hab : B ≠ A) : B LiesOn l ↔ (Seg_nd.toProj ⟨SEG A B, hab⟩ = l.toProj) := by
  constructor
  exact fun a => line_toProj_eq_seg_nd_toProj_of_lies_on ha a hab
  exact fun a => lies_on_of_Seg_nd_toProj_eq_toProj ha hab a

-- Given distinct A B on a line, there exist C s.t. C LiesOn AB (a cor of Archimedean_property in Seg) and there exist D s.t. B LiesOn AD
theorem Line.exist_pt_beyond_pt {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) (h : B ≠ A) : (∃ C D : P, (C LiesOn l) ∧ (D LiesOn l) ∧ (A LiesInt (SEG C B)) ∧ (B LiesInt (SEG A D))) := sorry

end Archimedean_property


section NewTheorems

theorem Seg_nd.lies_on_toline_of_lies_on_extn {X : P} {segnd : Seg_nd P} (lieson : X LiesOn segnd.extension) : X LiesOn segnd.toLine := by sorry

end NewTheorems

end EuclidGeom