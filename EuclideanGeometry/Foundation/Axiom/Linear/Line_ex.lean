import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

section compatibility
-- `eq_toProj theorems should be relocate to file parallel using parallel`.
variable (A B : P) (h : B ≠ A) (ray : Ray P) (seg_nd : Seg_nd P)

section pt_pt

theorem line_of_pt_pt_eq_rev : LIN A B h = LIN B A h.symm := by
  unfold Line.mk_pt_pt
  rw [Quotient.eq]
  show same_extn_line (RAY A B h) (RAY B A h.symm)
  constructor
  · exact Ray.toProj_eq_toProj_of_mk_pt_pt h
  left
  exact Ray.snd_pt_lies_on_mk_pt_pt h

theorem fst_pt_lies_on_line_of_pt_pt {A B : P} (h : B ≠ A) : A LiesOn LIN A B h := Or.inl (Ray.source_lies_on (RAY A B h))

theorem snd_pt_lies_on_line_of_pt_pt {A B : P} (h : B ≠ A) : B LiesOn LIN A B h := by
  rw [line_of_pt_pt_eq_rev]
  exact fst_pt_lies_on_line_of_pt_pt h.symm

-- The first point and the second point in Line.mk_pt_pt LiesOn the line it make.

theorem pt_lies_on_line_of_pt_pt_of_ne {A B : P} (h: B ≠ A) : A LiesOn LIN A B h ∧ B LiesOn LIN A B h := by
  constructor
  exact fst_pt_lies_on_line_of_pt_pt h
  exact snd_pt_lies_on_line_of_pt_pt h

/- two point determines a line -/

theorem exist_real_vec_eq_smul_of_lies_on_or_rev {A : P} {ray : Ray P} (h : A LiesOn ray ∨ A LiesOn ray.reverse) : ∃ t : ℝ, VEC ray.source A = t • ray.2.1 := by
  unfold lies_on Carrier.carrier Ray.instCarrierRay Ray.carrier Ray.IsOn at h
  simp at h
  rcases h with ⟨t, _, eq⟩ | ⟨t, _, eq⟩
  · use t, eq
  use -t
  simp; exact eq

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
  rcases exist_real_vec_eq_smul_of_lies_on_or_rev ha with ⟨ta, eqa⟩
  rcases exist_real_vec_eq_smul_of_lies_on_or_rev hb with ⟨tb, eqb⟩
  have : VEC A B = (tb - ta) • ray.2.1 := by rw [← vec_sub_vec _ A B, eqa, eqb, sub_smul]
  apply same_extn_line.symm
  constructor
  · set u : Vec_nd := ray.2.toVec_nd with u_def
    let v : Vec_nd := ⟨VEC A B, (vsub_ne_zero.mpr h)⟩
    have : v.1 = (tb - ta) • u.1 := this
    unfold Ray.toProj
    calc
      ray.2.toProj = u.toProj := by
        have hh : Vec_nd.normalize u = ray.2 := by
          rw [u_def]
          apply Dir.dir_toVec_nd_normalize_eq_self _
        unfold Vec_nd.toProj
        rw [hh]
      _ = v.toProj := by apply eq_toProj_of_smul _ _ this
      _ = (RAY A B h).2.toProj := rfl
  exact ha

-- If two lines have two distinct intersection points, then these two lines are identical.
theorem eq_of_pt_pt_lies_on_of_ne {A B : P} (h : B ≠ A) {l₁ l₂ : Line P} (hA₁ : A LiesOn l₁) (hB₁ : B LiesOn l₁) (hA₂ : A LiesOn l₂) (hB₂ : B LiesOn l₂) : l₁ = l₂ := by
  rw [← eq_line_of_pt_pt_of_ne h hA₁ hB₁]
  exact eq_line_of_pt_pt_of_ne h hA₂ hB₂

end pt_pt

section pt_proj

theorem pt_lies_on_of_mk_pt_proj (proj : Proj) : A LiesOn Line.mk_pt_proj A proj := by
  set v : Dir := (@Quotient.out _ PM.con.toSetoid proj)
  have eq : ⟦v⟧ = proj := by apply @Quotient.out_eq _ PM.con.toSetoid proj
  rw [← eq]
  unfold Line.mk_pt_proj
  rw [@Quotient.map_mk _ _ PM.con.toSetoid same_extn_line.setoid _ _ _]
  set rayA : Ray P := {source := A, toDir := v}
  show A LiesOn rayA.toLine
  apply (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev _ _).mpr
  left
  apply Ray.source_lies_on

theorem proj_eq_of_mk_pt_proj (proj : Proj) : (Line.mk_pt_proj A proj).toProj = proj := by
  set v : Dir := (@Quotient.out _ PM.con.toSetoid proj)
  have eq : ⟦v⟧ = proj := by apply @Quotient.out_eq _ PM.con.toSetoid proj
  rw [← eq]
  unfold Line.mk_pt_proj
  rw [@Quotient.map_mk _ _ PM.con.toSetoid same_extn_line.setoid _ _ _]
  unfold Line.toProj
  rw [@Quotient.lift_mk _ _ same_extn_line.setoid _ _ _]
  unfold Ray.toProj Dir.toProj Ray.toDir
  simp

end pt_proj

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
  show s.toRay.source LiesOn s.toRay.toLine
  apply Ray.source_lies_on_toLine

theorem Seg_nd.target_lies_on_toLine (s : Seg_nd P) : s.1.target LiesOn s.toLine := by
  rw [Seg_nd.toLine_eq_toRay_toLine]
  apply (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev s.1.target s.toRay).mpr
  left
  apply Seg_nd.lies_on_toRay_of_lies_on _
  show s.1.target LiesOn s.1
  apply Seg.target_lies_on

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
  let A : P := seg_nd.1.source
  let B : P := seg_nd.1.target
  have h : B ≠ A := seg_nd.2
  unfold Seg_nd.toLine Ray.toLine
  rw [Quotient.eq]
  constructor
  · unfold Ray.toProj
    rw [Seg_nd.extension]
    show seg_nd.toRay.toDir.toProj = (seg_nd.reverse.toRay).reverse.toDir.toProj
    have h₁ : (seg_nd.reverse.toRay).reverse.toProj = seg_nd.reverse.toRay.toProj := by apply Ray.toProj_of_rev_eq_toProj
    have h₂ : (seg_nd.reverse.toRay).reverse.toDir.toProj = (seg_nd.reverse.toRay).reverse.toProj := rfl
    rw [h₂, h₁]
    apply (Dir.eq_toProj_iff _ _).mpr
    right
    show (RAY A B h).toDir = -(RAY B A h.symm).toDir
    exact Ray.todir_eq_neg_todir_of_mk_pt_pt h
  left
  show B LiesOn seg_nd.toRay
  apply Seg_nd.lies_on_toRay_of_lies_on _
  apply Seg.target_lies_on

/- need to simplify -/
theorem lies_on_extn_or_rev_extn_iff_lies_on_toLine_of_not_lies_on {A : P} (seg_nd : Seg_nd P) (h : ¬ A LiesInt seg_nd.1) : A LiesOn seg_nd.toLine ↔ (A LiesOn seg_nd.extension) ∨ (A LiesOn seg_nd.reverse.extension) := by
  let X : P := seg_nd.1.source
  let Y : P := seg_nd.1.target
  let v : Vec_nd := ⟨VEC X Y, (ne_iff_vec_ne_zero _ _).mp seg_nd.2⟩
  let vr : Vec_nd := ⟨VEC Y X, (ne_iff_vec_ne_zero _ _).mp seg_nd.reverse.2⟩
  let vnr : Dir := Vec_nd.normalize v
  let nv : ℝ := Vec_nd.norm v
  constructor
  · intro hh
    have hh' : A LiesOn seg_nd.toRay.toLine := by exact hh
    rcases (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev _ _).mp hh' with h₁ | h₂
    · by_cases ax : A = X
      · right
        show A LiesOn seg_nd.toRay.reverse
        rw [ax]
        have : X = seg_nd.toRay.source := rfl
        rcases Ray.eq_source_iff_lies_on_and_lies_on_rev.1 this with ⟨_, h₂⟩
        exact h₂
      left
      unfold lies_on Carrier.carrier Ray.instCarrierRay Ray.carrier Ray.IsOn at h₁
      simp at h₁
      rcases h₁ with ⟨t, tpos, eq⟩
      have eq' : VEC X A = t * vnr.1 := by
        calc
          VEC X A = VEC seg_nd.toRay.source A := rfl
          _ = t * seg_nd.toRay.toDir.toVec := eq
      have tge1 : t ≥ nv := by
        contrapose! h
        unfold lies_int Interior.interior Seg.instInteriorSeg Seg.interior Seg.IsInt Seg.IsOn
        simp
        constructor
        · use t * nv⁻¹
          constructor
          · apply mul_nonneg_iff.mpr
            left
            use tpos
            apply inv_nonneg.mpr
            have : 0 < nv := by simp; apply norm_pos_iff.2 v.2
            linarith
          constructor
          · rw [mul_inv_le_iff, mul_one]
            linarith
            simp; apply norm_pos_iff.2 v.2
          rw [eq']
          unfold Dir.toVec
          simp; unfold Vec_nd.normalize
          simp; ring
        use ax
        contrapose! h
        rw [h] at eq'
        unfold Dir.toVec at eq'
        simp at eq'
        unfold Vec_nd.normalize at eq'
        simp at eq'
        symm at eq'
        rw [mul_comm, mul_assoc, inv_mul_eq_iff_eq_mul₀, mul_comm, mul_left_inj'] at eq'
        unfold Complex.ofReal' at eq'
        simp at eq'
        rw [eq']; rfl
        apply (ne_iff_vec_ne_zero _ _).mp seg_nd.2
        simp; apply norm_ne_zero_iff.2 v.2
      unfold lies_on Carrier.carrier Ray.instCarrierRay Ray.carrier Ray.IsOn
      simp
      use t - nv
      constructor
      linarith
      have eq1 : seg_nd.extension.toDir.toVec = (↑nv)⁻¹ * v.1 := by
        calc
          seg_nd.extension.toDir.toVec = seg_nd.reverse.toRay.reverse.toDir.toVec := rfl
          _ = -seg_nd.reverse.toRay.toDir.toVec := by
            have : seg_nd.reverse.toRay.reverse.toDir = -seg_nd.reverse.toRay.toDir := by apply Ray.toDir_of_rev_eq_neg_toDir
            rfl
          _ = -seg_nd.reverse.toDir.toVec := rfl
          _ = -(Vec_nd.normalize vr).1 := rfl
          _ = (Vec_nd.normalize v).1 := by
            have : v.1 = (-1 : ℝ) * vr.1 := by
              simp
              rw [neg_vec]
            have : -Vec_nd.normalize vr = Vec_nd.normalize v := by
              apply neg_normalize_eq_normalize_smul_neg _ _ this
              simp
            unfold Dir.toVec
            rw [← this]
            rfl
          _ = (↑nv)⁻¹ * v.1 := by
            unfold Dir.toVec Vec_nd.normalize
            simp
      have eq2 : VEC Y A = (t - nv) * ((↑nv)⁻¹ * v.1) := by
        calc
          VEC Y A = VEC X A - VEC X Y := by rw [vec_sub_vec]
          _ = t * (Vec_nd.normalize v).1 - VEC X Y := by rw [eq']
          _ = t * (Vec_nd.normalize v).1 - v.1 := rfl
          _ = t * ((↑nv)⁻¹ * v.1) - v.1 := by
            unfold Dir.toVec Vec_nd.normalize
            simp
          _ = t * ((↑nv)⁻¹ * v.1) - ((↑nv) * (↑nv)⁻¹) * v.1 := by
            have : v.1 = ((↑nv) * (↑nv)⁻¹) * v.1 := by
              rw [mul_assoc, mul_comm, mul_assoc]
              symm
              rw [inv_mul_eq_iff_eq_mul₀, mul_comm]
              simp
              exact norm_ne_zero_iff.2 v.2
            nth_rw 2 [this]
          _ = (t - nv) * ((↑nv)⁻¹ * v.1) := by ring
      calc
        VEC seg_nd.extension.source A = VEC Y A := rfl
        _ = (t - nv) * ((↑nv)⁻¹ * v.1) := eq2
        _ = (t - nv) * seg_nd.extension.toDir.toVec := by rw [eq1]
        _ = ↑(t - nv) * seg_nd.extension.toDir.toVec := by simp
    right
    show A LiesOn seg_nd.toRay.reverse
    exact h₂
  intro hh
  rcases hh with h₁ | h₂
  · rw [toLine_eq_extn_toLine]
    apply (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev _ _).mpr
    left
    exact h₁
  apply (Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev _ _).mpr
  right
  exact h₂

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
  exact Seg_nd.lies_on_toRay_of_lies_on _ A h

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