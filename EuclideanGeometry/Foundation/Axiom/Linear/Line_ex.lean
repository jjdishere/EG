import EuclideanGeometry.Foundation.Axiom.Linear.Line'
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P] 

section compatibility

variable (A B : P) (h : B ≠ A) (ray : Ray P) (seg_nd : Seg_nd P)

section pt_pt

theorem line_of_pt_pt_eq_rev : LIN A B h = LIN B A h.symm := by
  unfold Line.mk_pt_pt
  rw [Quotient.eq]
  show same_extn_line (RAY A B h) (RAY B A h.symm)
  let v₁ : Vec_nd := ⟨VEC A B, (ne_iff_vec_ne_zero _ _).mp h⟩
  let v₂ : Vec_nd := ⟨VEC B A, (ne_iff_vec_ne_zero _ _).mp h.symm⟩
  let nv₁ : ℝ := Vec_nd.norm v₁
  have eq : v₁.1 = (-1 : ℝ) • v₂.1 := by
    simp
    rw [neg_vec]
  constructor
  · unfold Ray.toProj Ray.toDir
    apply (Dir.eq_toProj_iff _ _).mpr
    right
    unfold Ray.mk_pt_pt
    simp
    show Vec_nd.normalize v₁ = -Vec_nd.normalize v₂
    symm
    have : (-1 : ℝ) < 0 := by norm_num
    apply neg_normalize_eq_normalize_smul_neg v₂ v₁ eq this
  left
  show B LiesOn (RAY A B h)
  unfold lies_on Carrier.carrier Ray.instCarrierRay
  simp
  unfold Ray.carrier Ray.IsOn Dir.toVec Ray.toDir
  simp
  have nvpos : 0 < nv₁ := norm_pos_iff.2 v₁.2
  set norv : Vec := (↑nv₁)⁻¹ • v₁.1 with norv_def
  use nv₁
  constructor
  · linarith
  show v₁.1 = nv₁ * norv
  rw [mul_comm, norv_def]
  simp; symm
  rw [mul_assoc, inv_mul_eq_iff_eq_mul₀, mul_comm]
  simp
  show nv₁ ≠ 0
  linarith

theorem fst_pt_lies_on_line_of_pt_pt {A B : P} (h : B ≠ A) : A LiesOn LIN A B h := Or.inl (Ray.source_lies_on (RAY A B h))

theorem snd_pt_lies_on_line_of_pt_pt {A B : P} (h : B ≠ A) : B LiesOn LIN A B h := by
  rw [line_of_pt_pt_eq_rev]
  exact fst_pt_lies_on_line_of_pt_pt h.symm

theorem pt_lies_on_line_of_pt_pt_of_ne {A B : P} (h: B ≠ A) : A LiesOn LIN A B h ∧ B LiesOn LIN A B h := by
  constructor
  exact fst_pt_lies_on_line_of_pt_pt h
  exact snd_pt_lies_on_line_of_pt_pt h

/- two point determines a line -/

theorem eq_line_of_pt_pt_of_ne {A B : P} {l : Line P} (h : B ≠ A) (ha : A LiesOn l) (hb : B LiesOn l) : LIN A B h = l := by
  revert l
  unfold Line
  rw [forall_quotient_iff (r := same_extn_line.setoid)]
  intro ray ha hb
  unfold Line.mk_pt_pt
  rw [Quotient.eq]
  unfold lies_on Line.instCarrierLine Carrier.carrier Line.carrier at ha hb
  simp only at ha hb
  rw [@Quotient.lift_mk _ _ same_extn_line.setoid _ _ _] at ha hb
  show same_extn_line (RAY A B h) ray
  set S : P := Ray.source with s_def
  let v : Vec_nd := ⟨VEC A B, (ne_iff_vec_ne_zero _ _).mp h⟩
  let vr : Vec_nd := ray.2.toVec_nd
  have vrDir : Vec_nd.normalize vr = ray.2 := by apply Dir.dir_toVec_nd_normalize_eq_self ray.2
  have vrDir' : vr = ray.2.1 := by rfl
  cases ha with
  | inl ha =>
    cases hb with
    | inl hb =>
      unfold Ray.carrier Ray.IsOn Dir.toVec Ray.toDir at ha
      simp at ha
      rcases ha with ⟨ta, tapos, aeq⟩
      rw [← s_def] at aeq
      unfold Ray.carrier Ray.IsOn Dir.toVec Ray.toDir at hb
      simp at hb
      rcases hb with ⟨tb, tbpos, beq⟩
      rw [← s_def] at beq
      by_cases hh : ta ≥ tb
      · have eq : v.1 = (tb - ta) • vr.1 := by
          simp
          rw [sub_mul]
          show VEC A B = tb * ray.2.1 - ta * ray.2.1
          have : VEC S A + VEC A B = VEC S B := by apply vec_add_vec
          have : VEC A B = VEC S B - VEC S A := by simp
          rw [this, aeq, beq]
          rfl
        have blta : tb < ta := by
          apply lt_iff_le_and_ne.mpr
          use hh
          intro aeqb
          rw [aeqb] at eq
          simp at eq
          have : B = A := by apply (eq_iff_vec_eq_zero A B).mpr eq
          contradiction
        constructor
        · unfold Ray.toProj Ray.toDir
          apply (Dir.eq_toProj_iff _ _).mpr
          right
          unfold Ray.mk_pt_pt
          simp
          show Vec_nd.normalize v = -ray.2
          rw [← vrDir]
          symm
          apply neg_normalize_eq_normalize_smul_neg vr v eq
          linarith
        left
        show S LiesOn (RAY A B h)
        unfold lies_on Carrier.carrier Ray.instCarrierRay Ray.carrier Ray.IsOn
        simp
        use ta, tapos
        show VEC A S = ta * (RAY A B h).2.1
        have : (RAY A B h).2.1 = (-1) * vr := by
          rw [vrDir']
          simp
          sorry
        rw [this, ← mul_assoc, vrDir']
        have : VEC A S = -ta * ray.2.1 := by
          calc
            VEC A S = -VEC S A := by rw [neg_vec]
            _ = -ta * ray.2.1 := by
              rw [aeq]; simp; left; rfl
        rw [this]
        simp
      sorry
    | inr hb =>
      sorry
  | inr ha => sorry

theorem eq_of_pt_pt_lies_on_of_ne {A B : P} (h : B ≠ A) {l₁ l₂ : Line P}(hA₁ : A LiesOn l₁) (hB₁ : B LiesOn l₁) (hA₂ : A LiesOn l₂) (hB₂ : B LiesOn l₂) : l₁ = l₂ := by
  have : LIN A B h = l₁ := by apply eq_line_of_pt_pt_of_ne h hA₁ hB₁
  rw [← this]
  exact eq_line_of_pt_pt_of_ne h hA₂ hB₂

end pt_pt

section coercion

-- The line defined from a nontrivial segment is equal to the line defined from the ray associated this nontrivial segment

theorem Seg_nd.toLine_eq_toRay_toLine (seg_nd : Seg_nd P) : seg_nd.toLine = (seg_nd.toRay).toLine := rfl

theorem line_of_pt_pt_eq_ray_toLine {A B : P} (h : B ≠ A) : LIN A B h = Ray.toLine (RAY A B h) := rfl

theorem line_of_pt_pt_eq_seg_nd_toLine {A B : P} (h : B ≠ A) : LIN A B h = Seg_nd.toLine ⟨SEG A B, h⟩ := rfl

theorem Ray.source_lies_on_toLine (l : Ray P) : l.source LiesOn l.toLine := by
  apply (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev l.source l).mpr
  left
  apply Ray.source_lies_on

theorem Seg_nd.source_lies_on_toLine (s : Seg_nd P) : s.1.source LiesOn s.toLine := by
  rw [Seg_nd.toLine_eq_toRay_toLine]
  have : s.1.source = s.toRay.source := rfl
  rw [this]
  apply Ray.source_lies_on_toLine

theorem Seg_nd.target_lies_on_toLine (s : Seg_nd P) : s.1.target LiesOn s.toLine := by
  rw [Seg_nd.toLine_eq_toRay_toLine]
  apply (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev s.1.target s.toRay).mpr
  left
  let A : P := s.1.source
  let B : P := s.1.target
  let nv : ℝ := Vec_nd.norm s.toVec_nd
  have nvpos : 0 < nv := norm_pos_iff.2 s.toVec_nd.2
  unfold lies_on Carrier.carrier Ray.instCarrierRay Ray.carrier Ray.IsOn
  simp
  use nv
  constructor
  · linarith
  show VEC A B = nv * s.toDir.1
  unfold Dir.toVec Seg_nd.toDir Vec_nd.normalize
  simp
  show VEC A B = ↑nv * ((↑nv)⁻¹ * s.toVec_nd.1)
  have : VEC A B = s.toVec_nd.1 := rfl
  rw [this, mul_comm]
  symm
  rw [mul_assoc, inv_mul_eq_iff_eq_mul₀, mul_comm]
  simp
  exact norm_ne_zero_iff.2 s.toVec_nd.2

theorem Ray.toLine_eq_rev_toLine : ray.toLine = ray.reverse.toLine := by
  unfold Ray.toLine
  rw [Quotient.eq]
  constructor
  · symm
    apply Ray.toProj_of_rev_eq_toProj
  right
  apply Ray.source_lies_on

theorem Seg_nd.toLine_eq_rev_toLine : seg_nd.toLine = seg_nd.reverse.toLine := by
  let A : P := seg_nd.1.source
  let B : P := seg_nd.1.target
  have h : B ≠ A := seg_nd.2
  have eq1 : seg_nd.toRay = RAY A B h := rfl
  have eq2 : seg_nd.reverse.toRay = RAY B A h.symm := rfl
  unfold Seg_nd.toLine
  rw [eq1, eq2]
  show (LIN A B h) = (LIN B A h.symm)
  apply line_of_pt_pt_eq_rev

theorem toLine_eq_extn_toLine : seg_nd.toLine = seg_nd.extension.toLine := by
  sorry

theorem lies_on_extn_or_rev_extn_iff_lies_on_toLine_of_not_lies_on {A : P} (seg_nd : Seg_nd P) (h : ¬ A LiesInt seg_nd.1) : A LiesOn seg_nd.toLine ↔ (A LiesOn seg_nd.extension) ∨ (A LiesOn seg_nd.reverse.extension) := sorry

/- Two lines are equal iff they have the same carrier -/

theorem lies_on_iff_lies_on_iff_line_eq_line (l₁ l₂ : Line P) : (∀ A : P, A LiesOn l₁ ↔ A LiesOn l₂) ↔ l₁ = l₂ := by
  constructor
  · intro hiff
    revert l₁ l₂
    unfold Line
    rw [forall_quotient_iff (r := same_extn_line.setoid)]
    intro r₁
    rw [forall_quotient_iff (r := same_extn_line.setoid)]
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
theorem Ray.lies_on_toLine_of_lie_on {A : P} {r : Ray P} (h : A LiesOn r) : A LiesOn (r.toLine) := by
  constructor
  exact h

theorem Seg_nd.lies_on_toLine_of_lie_on {A : P} {s : Seg_nd P} (h : A LiesOn s.1) : A LiesOn (s.toLine) := by
  constructor
  show A LiesOn s.toRay
  exact Seg_nd.lies_on_toRay_of_lies_on _ A h

theorem line_toProj_eq_seg_nd_toProj_of_lies_on {A B : P} {l : Line P} (ha : A LiesOn l) (hb : B LiesOn l) (hab : B ≠ A) : Seg_nd.toProj ⟨SEG A B, hab⟩ = l.toProj := by
  have : LIN A B hab = l := by apply eq_line_of_pt_pt_of_ne _ ha hb
  revert l
  unfold Line
  rw [forall_quotient_iff (r := same_extn_line.setoid)]
  intro r _ _ eq
  unfold Line.mk_pt_pt at eq
  rw [Quotient.eq] at eq
  rcases eq with ⟨eq₁, _⟩
  have : Seg_nd.toProj ⟨SEG A B, hab⟩ = Ray.toProj (RAY A B hab) := by rfl
  rw [this]
  have : Ray.toProj r = Line.toProj (Quotient.mk same_extn_line.setoid r) := by rfl
  rw [← this, eq₁]

theorem Ray.toProj_eq_toLine_toProj (ray : Ray P) : ray.toProj = ray.toLine.toProj := rfl

theorem Seg_nd.toProj_eq_toLine_toProj (seg_nd : Seg_nd P) : seg_nd.toProj = seg_nd.toLine.toProj := rfl

theorem lies_on_iff_eq_toProj {A B : P} {l : Line P} (h : B ≠ A) (hA : A LiesOn l) : B LiesOn l ↔ (SEG_nd A B h).toProj = l.toProj := by
  constructor
  · intro hB
    apply line_toProj_eq_seg_nd_toProj_of_lies_on hA hB
  intro eq
  have hh : (SEG_nd A B h).toLine = l := by
    revert l
    unfold Line
    rw [forall_quotient_iff (r := same_extn_line.setoid)]
    intro r ha eq
    unfold Seg_nd.toLine
    rw [Quotient.eq]
    symm
    show same_extn_line r (RAY A B h)
    constructor
    · have : Seg_nd.toProj (SEG_nd A B h) = Ray.toProj (RAY A B h) := rfl
      rw [← this, eq]
      rfl
    exact ha
  rw [← hh]
  have : B LiesOn (SEG_nd A B h).1 := by apply Seg.target_lies_on
  apply Seg_nd.lies_on_toLine_of_lie_on this

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
  constructor
  · by_cases h : B ≠ A
    · intro c
      use (LIN A B h), fst_pt_lies_on_line_of_pt_pt h, snd_pt_lies_on_line_of_pt_pt h
      rw [lies_on_line_of_pt_pt_iff_colinear]
      exact c
    simp at h
    by_cases hh : C ≠ B
    · intro _
      use (LIN B C hh)
      rw [← h]
      simp
      exact ⟨fst_pt_lies_on_line_of_pt_pt hh, snd_pt_lies_on_line_of_pt_pt hh⟩
    simp at hh
    intro _
    rw [hh, h]
    simp
    have : ∃ D : P, D ≠ A := by
      let v : Vec := 1
      have : v ≠ 0 := by simp
      use v +ᵥ A
      intro eq
      rw [vadd_eq_self_iff_vec_eq_zero] at eq
      exact this eq
    rcases this with ⟨D, neq⟩
    use LIN A D neq, fst_pt_lies_on_line_of_pt_pt neq
  rintro ⟨l, ha, hb, hc⟩
  by_cases h : B ≠ A
  · apply (lies_on_iff_colinear_of_ne_lies_on_lies_on h ha hb _).mp
    exact hc
  simp at h
  rw [h, colinear]
  simp

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
theorem Line.exist_pt_beyond_pt {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) (h : B ≠ A) : (∃ C D : P, (C LiesOn l) ∧ (D LiesOn l) ∧ (A LiesInt (SEG C B)) ∧ (B LiesInt (SEG A D))) := by
  set v₁ : Vec_nd := ⟨VEC A B, (ne_iff_vec_ne_zero _ _).1 h⟩ with v₁_def
  set v₂ : Vec_nd := ⟨VEC B A, (ne_iff_vec_ne_zero _ _).1 h.symm⟩ with v₂_def
  set C : P := v₂.1 +ᵥ A with C_def
  set D : P := v₁.1 +ᵥ B with D_def
  use C, D
  have hc : C LiesOn LIN B A h.symm := by
    apply (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev C (RAY B A h.symm)).mpr
    left
    unfold lies_on Carrier.carrier Ray.instCarrierRay Ray.carrier Ray.IsOn Dir.toVec Ray.toDir Ray.mk_pt_pt
    simp
    use 2 * (Vec_nd.norm v₂)
    constructor
    · have nvpos : 0 < Vec_nd.norm v₂ := norm_pos_iff.2 v₂.2
      linarith
    have : VEC B (VEC B A +ᵥ A) = 2 * (VEC B A) := by
      have : VEC B A = VEC A C := by
        unfold Vec.mk_pt_pt
        rw [C_def]
        simp
        rfl
      rw [two_mul]
      nth_rw 1 [this]
      nth_rw 2 [this]
      rw [vec_add_vec]
      simp
    rw [this, ← v₂_def, Vec_nd.normalize]
    simp
    let nv : ℝ := Vec_nd.norm v₂
    have : VEC B A = (↑nv) * ((↑nv)⁻¹ * VEC B A) := by
      symm
      rw [mul_comm, mul_assoc, inv_mul_eq_iff_eq_mul₀, mul_comm]
      simp
      exact norm_ne_zero_iff.2 v₂.2
    nth_rw 1 [this]
    rw [mul_assoc]
    simp
  have : LIN B A h.symm = l := by apply eq_line_of_pt_pt_of_ne h.symm hB hA
  constructor
  rw [← this]
  exact hc
  have hd : D LiesOn LIN A B h := by
    apply (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev D (RAY A B h)).mpr
    left
    unfold lies_on Carrier.carrier Ray.instCarrierRay Ray.carrier Ray.IsOn Dir.toVec Ray.toDir Ray.mk_pt_pt
    simp
    use 2 * (Vec_nd.norm v₁)
    constructor
    · have nvpos : 0 < Vec_nd.norm v₁ := norm_pos_iff.2 v₁.2
      linarith
    have : VEC A (VEC A B +ᵥ B) = 2 * (VEC A B) := by
      have : VEC A B = VEC B D := by
        unfold Vec.mk_pt_pt
        rw [D_def]
        simp
        rfl
      rw [two_mul]
      nth_rw 1 [this]
      nth_rw 2 [this]
      rw [vec_add_vec]
      simp
    rw [this, ← v₁_def, Vec_nd.normalize]
    simp
    let nv : ℝ := Vec_nd.norm v₁
    have : VEC A B = (↑nv) * ((↑nv)⁻¹ * VEC A B) := by
      symm
      rw [mul_comm, mul_assoc, inv_mul_eq_iff_eq_mul₀, mul_comm]
      simp
      exact norm_ne_zero_iff.2 v₁.2
    nth_rw 1 [this]
    rw [mul_assoc]
    simp
  have : LIN A B h = l := by apply eq_line_of_pt_pt_of_ne h hA hB
  constructor
  rw [← this]
  exact hd
  constructor
  · unfold lies_int Interior.interior Seg.instInteriorSeg Seg.interior Seg.IsInt Seg.IsOn
    simp
    constructor
    use 1 / 2
    constructor; linarith
    constructor; linarith
    have : VEC B A +ᵥ A = C := by
      have : VEC B A = VEC A C := by
        unfold Vec.mk_pt_pt
        rw [C_def]
        simp
        rfl
      rw [this]
      simp
    rw [this]
    have : VEC C B = 2 * VEC C A := by
      have : VEC C A = VEC A B := by
        rw [← neg_vec, ← neg_vec B A]
        unfold Vec.mk_pt_pt
        rw [C_def]
        simp
        rw [neg_vec]
        rfl
      rw [two_mul]
      nth_rw 2 [this]
      rw [vec_add_vec]
    rw [this]
    simp
    constructor
    intro eq
    symm at eq
    rw [vadd_eq_self_iff_vec_eq_zero] at eq
    apply h; symm
    apply (eq_iff_vec_eq_zero _ _).mpr eq
    exact h.symm
  unfold lies_int Interior.interior Seg.instInteriorSeg Seg.interior Seg.IsInt Seg.IsOn
  simp
  constructor
  · use 1 / 2
    constructor; linarith
    constructor; linarith
    have : VEC A B +ᵥ B = D := by
      have : VEC A B = VEC B D := by
        unfold Vec.mk_pt_pt
        rw [D_def]
        simp
        rfl
      rw [this]
      simp
    rw [this]
    have : VEC A D = 2 * VEC A B := by
      have : VEC B D = VEC A B := by
        unfold Vec.mk_pt_pt
        rw [D_def]
        simp
        rfl
      rw [two_mul]
      nth_rw 2 [← this]
      rw [vec_add_vec]
    rw [this]
    simp
  constructor
  exact h
  intro eq
  symm at eq
  rw [vadd_eq_self_iff_vec_eq_zero] at eq
  apply h
  apply (eq_iff_vec_eq_zero _ _).mpr eq

end Archimedean_property

end EuclidGeom