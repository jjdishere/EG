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


--**This part is completely irrelevant to Line. Indeed, we didn't prove any theorem about toProj in Line.
section pt_proj

theorem pt_lies_on_of_mk_pt_proj (proj : Proj) : A LiesOn Line.mk_pt_proj A proj := by
  rw [← @Quotient.out_eq _ PM.con.toSetoid proj]
  exact Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mpr (Or.inl Ray.source_lies_on)

theorem pt_lies_on_of_mk_pt_dir (dir : Dir) : A LiesOn Line.mk_pt_dir A dir :=
  pt_lies_on_of_mk_pt_proj A dir.toProj

theorem pt_lies_on_of_mk_pt_vec_nd (vec_nd : Vec_nd) : A LiesOn Line.mk_pt_vec_nd A vec_nd :=
  pt_lies_on_of_mk_pt_proj A vec_nd.toProj

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

theorem eq_of_same_toProj_and_pt_lies_on {A : P} {l₁ l₂: Line P} (h₁ : A LiesOn l₁) (h₂ : A LiesOn l₂) (h : l₁.toProj = l₂.toProj) : l₁ = l₂ := by 
  rw [← mk_pt_proj_eq h₁, mk_pt_proj_eq_of_eq_toProj h₂ h]

theorem exsit_line_pt_lies_on : ∃ l : Line P, A LiesOn l :=
  ⟨Line.mk_pt_vec_nd A ⟨1, one_ne_zero⟩, pt_lies_on_of_mk_pt_vec_nd A ⟨1, one_ne_zero⟩⟩

end pt_proj

section coercion

-- The line defined from a nontrivial segment is equal to the line defined from the ray associated this nontrivial segment

theorem Seg_nd.toLine_eq_toRay_toLine (seg_nd : Seg_nd P) : seg_nd.toLine = (seg_nd.toRay).toLine := rfl

theorem line_of_pt_pt_eq_ray_toLine {A B : P} (h : B ≠ A) : LIN A B h = Ray.toLine (RAY A B h) := rfl

theorem line_of_pt_pt_eq_seg_nd_toLine {A B : P} (h : B ≠ A) : LIN A B h = Seg_nd.toLine ⟨SEG A B, h⟩ := rfl

theorem Ray.source_lies_on_toLine (r : Ray P) : r.source LiesOn r.toLine := Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mpr (Or.inl source_lies_on)

theorem Seg_nd.source_lies_on_toLine (s : Seg_nd P) : s.1.source LiesOn s.toLine :=
  Ray.source_lies_on_toLine s.toRay

theorem Seg_nd.target_lies_on_toLine (s : Seg_nd P) : s.1.target LiesOn s.toLine :=
  Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mpr
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
    rcases Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mp hh with h₁ | h₂
    · by_cases ax : A = seg_nd.1.source
      · rw [ax]
        exact Or.inr Ray.source_lies_on
      by_cases ay : A = seg_nd.1.target
      · rw [ay]
        exact Or.inl Ray.source_lies_on
      exact Or.casesOn (lies_on_seg_nd_or_extension_of_lies_on_toRay h₁)
        (fun h₁ ↦ (h ⟨h₁, ax, ay⟩).elim) (fun h₁ ↦ Or.inl h₁)
    exact Or.inr h₂
  · exact fun hh ↦ Or.casesOn hh
      (fun h₁ ↦ Eq.mpr (toLine_eq_extn_toLine seg_nd ▸ Eq.refl (A LiesOn seg_nd.toLine))
        ((seg_nd.extension.lies_on_toLine_iff_lies_on_or_lies_on_rev).mpr (Or.inl h₁)))
      (fun h₂ ↦ (seg_nd.toRay.lies_on_toLine_iff_lies_on_or_lies_on_rev).mpr (Or.inr h₂))

/- Two lines are equal iff they have the same carrier -/

theorem lies_on_iff_lies_on_iff_line_eq_line (l₁ l₂ : Line P) : (∀ A : P, A LiesOn l₁ ↔ A LiesOn l₂) ↔ l₁ = l₂ := by
  constructor
  · revert l₁ l₂
    rintro ⟨r₁⟩ ⟨r₂⟩ h
    rcases r₁.toLine.nontriv with ⟨X, Y, Xrl₁, Yrl₁, neq⟩
    exact eq_of_pt_pt_lies_on_of_ne neq Xrl₁ Yrl₁ ((h X).mp Xrl₁) ((h Y).mp Yrl₁)
  · exact fun h A ↦ Iff.of_eq (congrArg (lies_on A) h)

-- If a point lies on a ray, then it lies on the line associated to the ray.
theorem Ray.lies_on_toLine_of_lie_on {A : P} {r : Ray P} (h : A LiesOn r) : A LiesOn (r.toLine) := Or.inl h

theorem Seg_nd.lies_on_toLine_of_lie_on {A : P} {s : Seg_nd P} (h : A LiesOn s.1) : A LiesOn (s.toLine) :=
  Or.inl (lies_on_toRay_of_lies_on h)

theorem line_toProj_eq_seg_nd_toProj_of_lies_on {A B : P} {l : Line P} (ha : A LiesOn l) (hb : B LiesOn l) (hab : B ≠ A) : Seg_nd.toProj ⟨SEG A B, hab⟩ = l.toProj := by
  rw [← eq_line_of_pt_pt_of_ne hab ha hb]
  rfl

theorem Ray.toProj_eq_toLine_toProj (ray : Ray P) : ray.toProj = ray.toLine.toProj := rfl

theorem Seg_nd.toProj_eq_toLine_toProj (seg_nd : Seg_nd P) : seg_nd.toProj = seg_nd.toLine.toProj := rfl

theorem lies_on_iff_eq_toProj_of_lies_on {A B : P} {l : Line P} (h : B ≠ A) (hA : A LiesOn l) : B LiesOn l ↔ (SEG_nd A B h).toProj = l.toProj := by
  refine' ⟨fun hB ↦ line_toProj_eq_seg_nd_toProj_of_lies_on hA hB h, fun eq ↦ _⟩
  rw [← eq_of_same_toProj_and_pt_lies_on (Seg_nd.lies_on_toLine_of_lie_on (@Seg.source_lies_on _ _ (SEG_nd A B h).1)) hA eq]
  exact Seg_nd.lies_on_toLine_of_lie_on Seg.target_lies_on

end coercion

section colinear

theorem lies_on_line_of_pt_pt_iff_colinear {A B : P} (h : B ≠ A) (X : P) : (X LiesOn (LIN A B h)) ↔ colinear A B X := 
  ⟨fun hx ↦ (LIN A B h).linear (fst_pt_lies_on_line_of_pt_pt h) (snd_pt_lies_on_line_of_pt_pt h) hx, 
  fun c ↦ (LIN A B h).maximal (fst_pt_lies_on_line_of_pt_pt h) (snd_pt_lies_on_line_of_pt_pt h) h c⟩

-- This is also a typical proof that shows how to use linear, maximal, nontriv of a line. Please write it shorter in future.

theorem lies_on_iff_colinear_of_ne_lies_on_lies_on {A B : P} {l : Line P} (h : B ≠ A) (ha : A LiesOn l) (hb : B LiesOn l) (C : P) : (C LiesOn l) ↔ colinear A B C :=
  ⟨fun hc ↦ l.linear ha hb hc, fun c ↦ l.maximal ha hb h c⟩

theorem colinear_iff_exist_line_lies_on (A B C : P) : colinear A B C ↔ ∃ l : Line P, (A LiesOn l) ∧ (B LiesOn l) ∧ (C LiesOn l) := by
  constructor
  · intro c
    by_cases h : B ≠ A
    · exact ⟨(LIN A B h), fst_pt_lies_on_line_of_pt_pt h, snd_pt_lies_on_line_of_pt_pt h,
        (lies_on_line_of_pt_pt_iff_colinear h C).mpr c⟩
    rw [ne_eq, not_not] at h 
    by_cases hh : C ≠ B
    · use LIN B C hh
      rw [← h, and_self_left]
      exact ⟨fst_pt_lies_on_line_of_pt_pt hh, snd_pt_lies_on_line_of_pt_pt hh⟩
    rw [ne_eq, not_not] at hh
    simp only [hh, h, and_self, exsit_line_pt_lies_on A]
  · intro ⟨l, ha, hb, hc⟩
    if h : B = A then simp only [h, colinear, or_true, dite_true]
    else exact (lies_on_iff_colinear_of_ne_lies_on_lies_on h ha hb C).mp hc 

end colinear

end compatibility

section Archimedean_property

open Classical

-- there are two distinct points on a line

theorem exists_ne_pt_pt_lies_on_of_line (A : P) (l : Line P) : ∃ B : P, B LiesOn l ∧ B ≠ A := by
  rcases l.nontriv with ⟨X, Y, hx, hy, ne⟩
  exact if h : A = X then ⟨Y, hy, ne.trans_eq h.symm⟩ else ⟨X, hx, ne_comm.mp h⟩

theorem lies_on_of_Seg_nd_toProj_eq_toProj {A B : P} {l : Line P} (ha : A LiesOn l) (hab : B ≠ A) (hp : Seg_nd.toProj ⟨SEG A B, hab⟩ = l.toProj) : B LiesOn l := 
  (lies_on_iff_eq_toProj_of_lies_on hab ha).mpr hp

theorem vec_vadd_pt_lies_on_line {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) (h : B ≠ A) : (VEC A B) +ᵥ B LiesOn l := by
  rw [← eq_line_of_pt_pt_of_ne h hA hB]
  refine' Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mpr 
    (Or.inl ⟨2 * ‖VEC A B‖, mul_nonneg zero_le_two (norm_nonneg (VEC A B)), _⟩)
  have eq : VEC A (VEC A B +ᵥ B) = 2 * (VEC A B) := (vadd_vsub_assoc _ B A).trans (two_mul _).symm
  simp only [Ray.mk_pt_pt, eq, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, 
    mul_assoc, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
  exact (Vec_nd.norm_smul_normalize_eq_self ⟨VEC A B, (ne_iff_vec_ne_zero A B).1 h⟩).symm

theorem Line.exist_pt_beyond_pt_right {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) (h : B ≠ A) : ∃ C : P, C LiesOn l ∧ B LiesInt (SEG A C) := 
  ⟨VEC A B +ᵥ B, vec_vadd_pt_lies_on_line hA hB h, (SEG_nd A B h).target_lies_int_seg_source_vec_vadd_target⟩

theorem Line.exist_pt_beyond_pt_left {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) (h : B ≠ A) : ∃ C : P, C LiesOn l ∧ A LiesInt (SEG C B) := by
  rcases exist_pt_beyond_pt_right hB hA h.symm with ⟨C, cl, acb⟩
  exact ⟨C, cl, Seg.lies_int_iff_lies_int_rev.mp acb⟩

end Archimedean_property


section NewTheorems

theorem Seg_nd.lies_on_toline_of_lies_on_extn {X : P} {seg_nd : Seg_nd P} (lieson : X LiesOn seg_nd.extension) : X LiesOn seg_nd.toLine := by
  rw [Seg_nd.toLine_eq_rev_toLine]
  apply Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mpr (Or.inr lieson)

end NewTheorems

end EuclidGeom