import EuclideanGeometry.Foundation.Axiom.Linear.Class

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]
/-
-- Definition
def DirObj.le {α : Type*} [DirObj α] (l : α) (A B : P)  : Prop := (0 : ℝ) ≤ inner (VEC A B) (toDir l).unitVecND

def DirObj.lt {α : Type*} [DirObj α] (l : α) (A B : P) : Prop := (0 : ℝ) < inner (VEC A B) (toDir l).unitVecND

notation A : max "≤[" l : max "]" B : max => DirObj.le l A B
notation A : max "<[" l : max "]" B : max => DirObj.lt l A B
-- Proof of Preorder
def DirObj.instPreorder {α : Type*} [DirObj α] (l : α) : Preorder P where
  le := DirObj.le l
  lt := DirObj.lt l
  le_refl := by
    rintro a; simp only; unfold le
    simp only [vec_same_eq_zero, ne_eq, Dir.coe_unitVecND, inner_zero_left, le_refl]
  le_trans := by
    rintro a b c; simp only; unfold le; rintro h1 h2
    calc
    _≤ inner (VEC a b) ↑(toDir l).unitVecND + inner (VEC b c) ↑(toDir l).unitVecND := by positivity
    _= inner (VEC a c) ↑(toDir l).unitVecND := by
      symm;
      have : (VEC a c) = (VEC a b) + (VEC b c) := by simp only [vec_add_vec]
      simp only [this]
      apply InnerProductSpace.add_left
  lt_iff_le_not_le := by
    rintro a b; simp only; unfold le; unfold lt
    constructor
    · rintro h1
      constructor
      · positivity
      · simp only [ne_eq, Dir.coe_unitVecND, not_le]
        have : (VEC b a) = (-1 : ℝ) • (VEC a b) := by simp only [neg_smul, one_smul, neg_vec]
        simp only [this]
        have : inner ((-1 : ℝ) • VEC a b) (toDir l).unitVec = (-1 : ℝ) * (inner (VEC a b) (toDir l).unitVec) := by
          exact InnerProductSpace.smul_left (VEC a b) ((toDir l).unitVec) (-1 : ℝ)
        simp only [this]
        simp only [neg_mul, one_mul, Left.neg_neg_iff, gt_iff_lt]
        positivity
    · rintro ⟨_, h2⟩
      simp only [ne_eq, Dir.coe_unitVecND, not_le] at h2
      have : (VEC b a) = (-1 : ℝ) • (VEC a b) := by simp only [neg_smul, one_smul, neg_vec]
      simp only [this] at h2
      have : inner ((-1 : ℝ) • VEC a b) (toDir l).unitVec = (-1 : ℝ) * (inner (VEC a b) (toDir l).unitVec) := by
        exact InnerProductSpace.smul_left (VEC a b) ((toDir l).unitVec) (-1 : ℝ)
      simp only [this] at h2
      simp only [neg_mul, one_mul, Left.neg_neg_iff, gt_iff_lt] at h2
      exact h2

@[aesop unsafe]
theorem lt_of_le_not_le {α : Type*} [DirObj α] (l : α) {a : P} {b : P} :
a ≤[l] b → ¬b ≤[l] a → a <[l] b :=
  @_root_.lt_of_le_not_le P (DirObj.instPreorder l) a b
-/

attribute [aesop unsafe] le_trans lt_trans le_of_lt lt_of_le_of_lt lt_of_lt_of_le eq_iff_le_not_lt lt_or_lt_iff_ne not_lt_iff_eq_or_lt
namespace DirLine
section linear_order

abbrev lelem (A : P) {l : DirLine P} (ha : A LiesOn l) : l.carrier.Elem := ⟨A, ha⟩

-- linear order and ne
theorem ne_iff_ne_as_line_elem {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) : (A ≠ B) ↔ (lelem A ha ≠ lelem B hb) := by
  simp only [ne_eq, Subtype.mk.injEq]

-- ``Position Relations to Order Relations``
-- linear order and LiesInt Seg
theorem lt_of_lies_int_and_lt₁ {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesInt (SEG A C)) (a_lt_c : lelem A ha < lelem C hc): lelem A ha < lelem B hb := by sorry
theorem lt_of_lies_int_and_lt₂ {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesInt (SEG A C)) (a_lt_c : lelem A ha < lelem C hc): lelem B hb < lelem C hc := by sorry
theorem gt_of_lies_int_and_gt₁ {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesInt (SEG A C)) (a_gt_c : lelem A ha > lelem C hc): lelem A ha > lelem B hb := by sorry
theorem gt_of_lies_int_and_gt₂ {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesInt (SEG A C)) (a_gt_c : lelem A ha > lelem C hc): lelem B hb > lelem C hc := by sorry



-- ``Order Relations to Position Relations``
-- linear order and LiesInt Seg
theorem lies_int_of_lt_and_lt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_lt_b : lelem A ha < lelem B hb) (b_lt_c : lelem B hb < lelem C hc) : B LiesInt (SEG A C) := by
  have h1 : (0 : ℝ) < ddist ha hb := (DirLine.lt_iff_zero_lt_ddist ha hb).mp a_lt_b
  have h2 : (0 : ℝ) < ddist hb hc := (DirLine.lt_iff_zero_lt_ddist hb hc).mp b_lt_c
  have h3 : ∃ t : ℝ, VEC A B = t • (Dl.toDir).unitVec := by
    apply Line.exist_real_vec_eq_smul_of_lies_on
    have : Line.mk_pt_dir A Dl.toDir = Dl.toLine := by
      calc
      _= (DirLine.mk_pt_dir A Dl.toDir).toLine := by rfl
      _=_ := by
        congr 1
        apply DirLine.mk_pt_dir_eq_of_eq_toDir
        exact ha; rfl
    simp only [this]
    apply DirLine.lies_on_iff_lies_on_toLine.mpr
    exact hb
  have h4 : ∃ t : ℝ, VEC B C = t • (Dl.toDir).unitVec := by
    apply Line.exist_real_vec_eq_smul_of_lies_on
    have : Line.mk_pt_dir B Dl.toDir = Dl.toLine := by
      calc
      _= (DirLine.mk_pt_dir B Dl.toDir).toLine := by rfl
      _=_ := by
        congr 1
        apply DirLine.mk_pt_dir_eq_of_eq_toDir
        exact hb; rfl
    simp only [this]
    apply DirLine.lies_on_iff_lies_on_toLine.mpr
    exact hc
  rcases h3 with ⟨x1, hx1⟩; rcases h4 with ⟨x2, hx2⟩;
  have h1 : (0 : ℝ) < inner (VEC A B) (Dl.toDir).unitVec := by exact h1
  have h2 : (0 : ℝ) < inner (VEC B C) (Dl.toDir).unitVec := by exact h2
  simp only [hx1] at h1; simp only [hx2] at h2
  have h1 : (0 : ℝ) < x1 := by
    calc
    (0 : ℝ)
    _< inner (x1 • Dl.toDir.unitVec) Dl.toDir.unitVec := h1
    _= x1 * inner Dl.toDir.unitVec Dl.toDir.unitVec := by
      apply InnerProductSpace.smul_left
    _= x1 := by simp only [Dir.inner_unitVec, vsub_self, AngValue.cos_zero, mul_one]
  have h2 : (0 : ℝ) < x2 := by
    calc
    (0 : ℝ)
    _< inner (x2 • Dl.toDir.unitVec) Dl.toDir.unitVec := h2
    _= x2 * inner Dl.toDir.unitVec Dl.toDir.unitVec := by
      apply InnerProductSpace.smul_left
    _= x2 := by simp only [Dir.inner_unitVec, vsub_self, AngValue.cos_zero, mul_one]
  apply Seg.lies_int_iff.mpr
  constructor
  · have : lelem A ha ≠ lelem C hc := by
      apply ne_of_lt; exact lt_trans a_lt_b b_lt_c
    apply (ne_iff_ne_as_line_elem hc ha).mpr
    exact this.symm
  · use (x1 / (x1 + x2))
    constructor
    · positivity
    · constructor
      · have : 0 < 1 - x1 / (x1 + x2) := by
          calc
          _< x2 / (x1 + x2) := by positivity
          _= _ := by field_simp
        linarith [this]
      · simp only [hx1]
        have : (SEG A C).toVec = (VEC A B) + (VEC B C) := by simp only [seg_toVec_eq_vec,
          vec_add_vec]
        simp only [this, hx1, hx2, smul_add]
        calc
        _= ((x1 / (x1 + x2)) * x1 + (x1 / (x1 + x2)) * x2) • Dl.toDir.unitVec := by
          congr 1; field_simp; ring
        _= ((x1 / (x1 + x2)) * x1) • Dl.toDir.unitVec + ((x1 / (x1 + x2)) * x2) • Dl.toDir.unitVec := by apply add_smul
        _=_ := by congr 1; apply mul_smul; apply mul_smul

theorem lies_int_of_gt_and_gt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_gt_b : (⟨A, ha⟩ : Dl.carrier.Elem) > ⟨B, hb⟩) (b_gt_c : (⟨B, hb⟩ : Dl.carrier.Elem) > ⟨C, hc⟩) : B LiesInt (SEG A C) := by
  apply Seg.lies_int_rev_iff_lies_int.mp
  apply lies_int_of_lt_and_lt hc hb ha
  exact b_gt_c
  exact a_gt_b

-- linear order and LiesOn
theorem lies_on_of_le_and_le {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_le_b : lelem A ha ≤ lelem B hb) (b_le_c : lelem B hb ≤ lelem C hc) : B LiesOn (SEG A C) := by
  have h : (A ≠ C) ∨ (A = C) := by apply ne_or_eq
  rcases h with (ne | eq)
  ·
    have h1 : (0 : ℝ) ≤ ddist ha hb := (DirLine.le_iff_zero_le_ddist ha hb).mp a_le_b
    have h2 : (0 : ℝ) ≤ ddist hb hc := (DirLine.le_iff_zero_le_ddist hb hc).mp b_le_c
    have h3 : ∃ t : ℝ, VEC A B = t • (Dl.toDir).unitVec := by
      apply Line.exist_real_vec_eq_smul_of_lies_on
      have : Line.mk_pt_dir A Dl.toDir = Dl.toLine := by
        calc
        _= (DirLine.mk_pt_dir A Dl.toDir).toLine := by rfl
        _=_ := by
          congr 1
          apply DirLine.mk_pt_dir_eq_of_eq_toDir
          exact ha; rfl
      simp only [this]
      apply DirLine.lies_on_iff_lies_on_toLine.mpr
      exact hb
    have h4 : ∃ t : ℝ, VEC B C = t • (Dl.toDir).unitVec := by
      apply Line.exist_real_vec_eq_smul_of_lies_on
      have : Line.mk_pt_dir B Dl.toDir = Dl.toLine := by
        calc
        _= (DirLine.mk_pt_dir B Dl.toDir).toLine := by rfl
        _=_ := by
          congr 1
          apply DirLine.mk_pt_dir_eq_of_eq_toDir
          exact hb; rfl
      simp only [this]
      apply DirLine.lies_on_iff_lies_on_toLine.mpr
      exact hc
  rcases h3 with ⟨x1, hx1⟩; rcases h4 with ⟨x2, hx2⟩;
  have h1 : (0 : ℝ) < inner (VEC A B) (Dl.toDir).unitVec := by exact h1
  have h2 : (0 : ℝ) < inner (VEC B C) (Dl.toDir).unitVec := by exact h2
  simp only [hx1] at h1; simp only [hx2] at h2
  have h1 : (0 : ℝ) < x1 := by
    calc
    (0 : ℝ)
    _< inner (x1 • Dl.toDir.unitVec) Dl.toDir.unitVec := h1
    _= x1 * inner Dl.toDir.unitVec Dl.toDir.unitVec := by
      apply InnerProductSpace.smul_left
    _= x1 := by simp only [Dir.inner_unitVec, vsub_self, AngValue.cos_zero, mul_one]
  have h2 : (0 : ℝ) < x2 := by
    calc
    (0 : ℝ)
    _< inner (x2 • Dl.toDir.unitVec) Dl.toDir.unitVec := h2
    _= x2 * inner Dl.toDir.unitVec Dl.toDir.unitVec := by
      apply InnerProductSpace.smul_left
    _= x2 := by simp only [Dir.inner_unitVec, vsub_self, AngValue.cos_zero, mul_one]
  apply Seg.lies_int_iff.mpr
  constructor
  · have : lelem A ha ≠ lelem C hc := by
      apply ne_of_lt; exact lt_trans a_lt_b b_lt_c
    apply (ne_iff_ne_as_line_elem hc ha).mpr
    exact this.symm
  · use (x1 / (x1 + x2))
    constructor
    · positivity
    · constructor
      · have : 0 < 1 - x1 / (x1 + x2) := by
          calc
          _< x2 / (x1 + x2) := by positivity
          _= _ := by field_simp
        linarith [this]
      · simp only [hx1]
        have : (SEG A C).toVec = (VEC A B) + (VEC B C) := by simp only [seg_toVec_eq_vec,
          vec_add_vec]
        simp only [this, hx1, hx2, smul_add]
        calc
        _= ((x1 / (x1 + x2)) * x1 + (x1 / (x1 + x2)) * x2) • Dl.toDir.unitVec := by
          congr 1; field_simp; ring
        _= ((x1 / (x1 + x2)) * x1) • Dl.toDir.unitVec + ((x1 / (x1 + x2)) * x2) • Dl.toDir.unitVec := by apply add_smul
        _=_ := by congr 1; apply mul_smul; apply mul_smul
  · have : lelem A ha = lelem C hc := by simp only [eq]
    simp only [this] at a_le_b
    have : lelem C hc = lelem B hb := eq_iff_le_not_lt.mpr ⟨a_le_b, not_lt_of_le b_le_c⟩
    have : C = B := Subtype.val_inj.mpr this
    simp only [this, eq]
    apply Seg.source_lies_on

theorem lies_on_of_ge_and_ge {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_ge_b : (⟨A, ha⟩ : Dl.carrier.Elem) ≥ ⟨B, hb⟩) (b_ge_c : (⟨B, hb⟩ : Dl.carrier.Elem) ≥ ⟨C, hc⟩) : B LiesOn (SEG A C) := by sorry










theorem le_and_le_or_ge_and_ge_of_lies_on {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesOn (SEG A C)) : (((⟨A, ha⟩ : Dl.carrier.Elem) ≤ ⟨B, hb⟩) ∧ ((⟨B, hb⟩ : Dl.carrier.Elem) ≤ ⟨C, hc⟩)) ∨ (((⟨A, ha⟩ : Dl.carrier.Elem) ≥ ⟨B, hb⟩) ∧ ((⟨B, hb⟩ : Dl.carrier.Elem) ≥ ⟨C, hc⟩)) := by sorry
-- linear order and toDir
theorem eq_toDir_of_lt {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (a_lt_b : (⟨A, ha⟩ : Dl.carrier.Elem) < ⟨B, hb⟩) : (RAY A B ((ne_iff_ne_as_line_elem ha hb).mpr (ne_of_lt a_lt_b)).symm).toDir = Dl.toDir := by sorry
theorem neg_toDir_of_gt {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (a_gt_b : (⟨A, ha⟩ : Dl.carrier.Elem) > ⟨B, hb⟩) : (RAY A B ((ne_iff_ne_as_line_elem ha hb).mpr (ne_of_gt a_gt_b)).symm).toDir = - Dl.toDir := by sorry

end linear_order
end DirLine

end EuclidGeom
