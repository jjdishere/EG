import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

section compatibility
-- `eq_toProj theorems should be relocate to file parallel using parallel`.
variable (A B : P) (h : B ≠ A) (ray : Ray P) (seg_nd : Seg_nd P)

section pt_pt

theorem line_of_pt_pt_eq_rev : LIN A B h = LIN B A h.symm := 
  Quotient.eq.mpr ⟨Ray.toProj_eq_toProj_of_mk_pt_pt h, Or.inl (Ray.snd_pt_lies_on_mk_pt_pt h)⟩

theorem fst_pt_lies_on_line_of_pt_pt {A B : P} (h : B ≠ A) : A LiesOn LIN A B h := Or.inl (Ray.source_lies_on)

theorem snd_pt_lies_on_line_of_pt_pt {A B : P} (h : B ≠ A) : B LiesOn LIN A B h := by
  rw [line_of_pt_pt_eq_rev]
  exact fst_pt_lies_on_line_of_pt_pt h.symm

-- The first point and the second point in Line.mk_pt_pt LiesOn the line it make.

theorem pt_lies_on_line_of_pt_pt_of_ne {A B : P} (h: B ≠ A) : A LiesOn LIN A B h ∧ B LiesOn LIN A B h :=
  ⟨fst_pt_lies_on_line_of_pt_pt h, snd_pt_lies_on_line_of_pt_pt h⟩

/- two point determines a line -/
theorem eq_line_of_pt_pt_of_ne {A B : P} {l : Line P} (h : B ≠ A) (ha : A LiesOn l) (hb : B LiesOn l) : LIN A B h = l := by
  revert l
  rintro ⟨r⟩ ha hb
  exact Quotient.eq.mpr (same_extn_line.symm ⟨ray_toProj_eq_mk_pt_pt_toProj h ha hb, ha⟩)

-- If two lines have two distinct intersection points, then these two lines are identical.
theorem eq_of_pt_pt_lies_on_of_ne {A B : P} (h : B ≠ A) {l₁ l₂ : Line P} (hA₁ : A LiesOn l₁) (hB₁ : B LiesOn l₁) (hA₂ : A LiesOn l₂) (hB₂ : B LiesOn l₂) : l₁ = l₂ := by
  rw [← eq_line_of_pt_pt_of_ne h hA₁ hB₁]
  exact eq_line_of_pt_pt_of_ne h hA₂ hB₂

end pt_pt

section pt_proj

theorem pt_lies_on_of_mk_pt_proj (proj : Proj) : A LiesOn Line.mk_pt_proj A proj := by
  rw [← @Quotient.out_eq _ PM.con.toSetoid proj]
  exact (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev _ _).mpr (Or.inl Ray.source_lies_on)

theorem proj_eq_of_mk_pt_proj (proj : Proj) : (Line.mk_pt_proj A proj).toProj = proj := by
  rw [← @Quotient.out_eq _ PM.con.toSetoid proj]
  rfl

theorem mk_pt_proj_eq {A : P} {l : Line P} (h : A LiesOn l) : Line.mk_pt_proj A l.toProj = l := by
  revert l
  rintro ⟨r⟩ h
  exact (@Quotient.map_mk _ _ PM.con.toSetoid _ (fun x : _ ↦ Ray.mk A x) (same_extn_line_of_PM A) r.2).trans
    (Quotient.eq.mpr (same_extn_line.symm ⟨rfl, h⟩))

theorem mk_pt_proj_eq_of_eq_toProj {A : P} {l : Line P} (h : A LiesOn l) {x : Proj} 
    (hx : x = l.toProj) : Line.mk_pt_proj A x = l := by
  rw [hx]
  exact mk_pt_proj_eq h

end pt_proj

section coercion

-- The line defined from a nontrivial segment is equal to the line defined from the ray associated this nontrivial segment

theorem Seg_nd.toLine_eq_toRay_toLine (seg_nd : Seg_nd P) : seg_nd.toLine = (seg_nd.toRay).toLine := rfl

theorem line_of_pt_pt_eq_ray_toLine {A B : P} (h : B ≠ A) : LIN A B h = Ray.toLine (RAY A B h) := rfl

theorem line_of_pt_pt_eq_seg_nd_toLine {A B : P} (h : B ≠ A) : LIN A B h = Seg_nd.toLine ⟨SEG A B, h⟩ := rfl

theorem Ray.source_lies_on_toLine (l : Ray P) : l.source LiesOn l.toLine :=
  (lies_on_toLine_iff_lies_on_or_lies_on_rev source l).mpr (Or.inl source_lies_on)

theorem Seg_nd.source_lies_on_toLine (s : Seg_nd P) : s.1.source LiesOn s.toLine :=
  Ray.source_lies_on_toLine s.toRay

theorem Seg_nd.target_lies_on_toLine (s : Seg_nd P) : s.1.target LiesOn s.toLine :=
  (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev s.1.target s.toRay).mpr
    (Or.inl (lies_on_toRay_of_lies_on Seg.target_lies_on))

theorem Ray.toLine_eq_rev_toLine : ray.toLine = ray.reverse.toLine :=
  Quotient.eq.mpr ⟨toProj_of_rev_eq_toProj.symm, Or.inr source_lies_on⟩

theorem Seg_nd.toLine_eq_rev_toLine : seg_nd.toLine = seg_nd.reverse.toLine :=
  line_of_pt_pt_eq_rev seg_nd.1.source seg_nd.1.target seg_nd.2

theorem toLine_eq_extn_toLine : seg_nd.toLine = seg_nd.extension.toLine := Quotient.eq.mpr ⟨by 
  show seg_nd.toProj = seg_nd.reverse.toRay.reverse.toProj
  rw [Ray.toProj_of_rev_eq_toProj, Seg_nd.toRay_toProj_eq_toProj, Seg_nd.toProj_of_rev_eq_toProj], 
  Or.inl (Seg_nd.lies_on_toRay_of_lies_on Seg.target_lies_on)⟩

theorem lies_on_extn_or_rev_extn_iff_lies_on_toLine_of_not_lies_on {A : P} {seg_nd : Seg_nd P} (h : ¬ A LiesInt seg_nd.1) : A LiesOn seg_nd.toLine ↔ (A LiesOn seg_nd.extension) ∨ (A LiesOn seg_nd.reverse.extension) := by
  constructor
  · intro hh
    rcases (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev _ _).mp hh with h₁ | h₂
    · by_cases ax : A = seg_nd.1.source
      · rw [ax]
        exact Or.inr Ray.source_lies_on
      by_cases ay : A = seg_nd.1.target
      · rw [ay]
        exact Or.inl Ray.source_lies_on
      exact Or.casesOn (lies_on_seg_nd_or_extension_of_lies_on_toRay h₁)
        (fun h₁ ↦ (h ⟨h₁, ax,ay⟩).elim) (fun h₁ ↦ Or.inl h₁)  
    exact Or.inr h₂
  · exact fun hh ↦ Or.casesOn hh (
      fun h₁ ↦ Eq.mpr (toLine_eq_extn_toLine seg_nd ▸ Eq.refl (A LiesOn Seg_nd.toLine seg_nd))
        ((Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev A (Seg_nd.extension seg_nd)).mpr (Or.inl h₁)))
      fun h₂ ↦ (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev A (Seg_nd.toRay seg_nd)).mpr (Or.inr h₂)

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
    rcases r₁.toLine.nontriv with ⟨X, ⟨Y, ⟨Xrl₁, ⟨Yrl₁, neq⟩⟩⟩⟩
    have Xr₁ : X ∈ r₁.carrier ∪ r₁.reverse.carrier := by
      show (X LiesOn r₁) ∨ (X LiesOn r₁.reverse)
      apply (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev _ _).mp Xrl₁
    have Yr₁ : Y ∈ r₁.carrier ∪ r₁.reverse.carrier := by
      show (Y LiesOn r₁) ∨ (Y LiesOn r₁.reverse)
      apply (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev _ _).mp Yrl₁
    have Xrl₂ : X LiesOn r₂.toLine := by
      have : (X LiesOn r₂) ∨ (X LiesOn r₂.reverse) := by
        show X ∈ r₂.carrier ∪ r₂.reverse.carrier
        apply (h X).mp Xr₁
      apply (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev _ _).mpr this
    have Yrl₂ : Y LiesOn r₂.toLine := by
      have : (Y LiesOn r₂) ∨ (Y LiesOn r₂.reverse) := by
        show Y ∈ r₂.carrier ∪ r₂.reverse.carrier
        apply (h Y).mp Yr₁
      apply (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev _ _).mpr this
    have : r₁.toLine = r₂.toLine := by apply eq_of_pt_pt_lies_on_of_ne neq Xrl₁ Yrl₁ Xrl₂ Yrl₂
    unfold Ray.toLine at this
    rw [Quotient.eq] at this
    exact this
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
  exact Seg_nd.lies_on_toRay_of_lies_on h

theorem line_toProj_eq_seg_nd_toProj_of_lies_on {A B : P} {l : Line P} (ha : A LiesOn l) (hb : B LiesOn l) (hab : B ≠ A) : Seg_nd.toProj ⟨SEG A B, hab⟩ = l.toProj := by
  have : LIN A B hab = l := by apply eq_line_of_pt_pt_of_ne _ ha hb
  revert l
  unfold Line
  rw [Quotient.forall (s := same_extn_line.setoid)]
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

theorem lies_on_iff_eq_toProj_of_lies_on {A B : P} {l : Line P} (h : B ≠ A) (hA : A LiesOn l) : B LiesOn l ↔ (SEG_nd A B h).toProj = l.toProj := by
  constructor
  · intro hB
    apply line_toProj_eq_seg_nd_toProj_of_lies_on hA hB
  intro eq
  have hh : (SEG_nd A B h).toLine = l := by
    revert l
    unfold Line
    rw [Quotient.forall (s := same_extn_line.setoid)]
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

theorem lies_on_line_of_pt_pt_iff_colinear {A B : P} (h : B ≠ A) : ∀ X : P, (X LiesOn (LIN A B h)) ↔ colinear A B X := fun X ↦ 
  ⟨fun hx ↦ (LIN A B h).linear (fst_pt_lies_on_line_of_pt_pt h) (snd_pt_lies_on_line_of_pt_pt h) hx, 
  fun c ↦ (LIN A B h).maximal (fst_pt_lies_on_line_of_pt_pt h) (snd_pt_lies_on_line_of_pt_pt h) h X c⟩

-- This is also a typical proof that shows how to use linear, maximal, nontriv of a line. Please write it shorter in future.

theorem lies_on_iff_colinear_of_ne_lies_on_lies_on {A B : P} {l : Line P} (h : B ≠ A) (ha : A LiesOn l) (hb : B LiesOn l) : ∀ C : P, (C LiesOn l) ↔ colinear A B C :=
  fun C ↦ ⟨fun hc ↦ l.linear ha hb hc, fun c ↦ l.maximal ha hb h C c⟩

theorem colinear_iff_exist_line_lies_on (A B C : P) : colinear A B C ↔ ∃ l : Line P, (A LiesOn l) ∧ (B LiesOn l) ∧ (C LiesOn l) := by
  constructor
  · by_cases h : B ≠ A
    · intro c
      use (LIN A B h), fst_pt_lies_on_line_of_pt_pt h, snd_pt_lies_on_line_of_pt_pt h
      rw [lies_on_line_of_pt_pt_iff_colinear]
      exact c
    rw [ne_eq, not_not] at h 
    by_cases hh : C ≠ B
    · intro _
      use (LIN B C hh)
      rw [← h, and_self_left]
      exact ⟨fst_pt_lies_on_line_of_pt_pt hh, snd_pt_lies_on_line_of_pt_pt hh⟩
    rw [ne_eq, not_not] at hh 
    intro _
    simp only [hh, h, and_self]
    have : ∃ D : P, D ≠ A := by
      let v : Vec := 1
      have : v ≠ 0 := by simp only [ne_eq, one_ne_zero, not_false_eq_true]
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
  rw [ne_eq, not_not] at h
  simp only [h, colinear, or_true, dite_true]

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
  apply (lies_on_iff_eq_toProj_of_lies_on hab ha).mpr hp

-- Given distinct A B on a line, there exist C s.t. C LiesOn AB (a cor of Archimedean_property in Seg) and there exist D s.t. B LiesOn AD
/- need to simplify -/
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


section NewTheorems

theorem Seg_nd.lies_on_toline_of_lies_on_extn {X : P} {seg_nd : Seg_nd P} (lieson : X LiesOn seg_nd.extension) : X LiesOn seg_nd.toLine := by
  rw [Seg_nd.toLine_eq_rev_toLine]
  show X LiesOn seg_nd.reverse.toRay.toLine
  apply (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev _ _).mpr
  right
  exact lieson

end NewTheorems

end EuclidGeom