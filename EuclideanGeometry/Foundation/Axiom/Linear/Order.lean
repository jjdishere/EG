import EuclideanGeometry.Foundation.Axiom.Linear.Class
import EuclideanGeometry.Foundation.Axiom.Linear.Collinear

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]
-- `unused section`
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

namespace DirLine
section linear_order

-- # preparatory theorems
abbrev lelem (A : P) {l : DirLine P} (ha : A LiesOn l) : l.carrier.Elem := ⟨A, ha⟩
-- Collinearity -- `moved to Linear.Line`

-- linear order and ne
theorem ne_iff_ne_as_line_elem {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) : (A ≠ B) ↔ (lelem A ha ≠ lelem B hb) := by
  simp only [ne_eq, Subtype.mk.injEq]

-- linear order and vector
theorem exist_pos_smul_of_lt {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl)(a_lt_b : (lelem A ha) < (lelem B hb)) : (∃ t : ℝ, 0 < t ∧ (VEC A B) = t • (Dl.toDir).unitVec) := by
  have h1 : (0 : ℝ) < ddist ha hb := (DirLine.lt_iff_zero_lt_ddist ha hb).mp a_lt_b
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
  rcases h3 with ⟨x1, hx1⟩
  have h1 : (0 : ℝ) < inner (VEC A B) (Dl.toDir).unitVec := by exact h1
  have h1 : (0 : ℝ) < x1 := by
    calc
    (0 : ℝ)
    _< inner (x1 • Dl.toDir.unitVec) Dl.toDir.unitVec := by simp only [hx1.symm]; exact h1
    _= x1 * inner Dl.toDir.unitVec Dl.toDir.unitVec := by
      apply InnerProductSpace.smul_left
    _= x1 := by simp only [Dir.inner_unitVec, vsub_self, AngValue.cos_zero, mul_one]
  use x1

theorem exist_nonneg_smul_of_le {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl)(a_le_b : (lelem A ha) ≤ (lelem B hb)) : (∃ t : ℝ, 0 ≤ t ∧ (VEC A B) = t • (Dl.toDir).unitVec) := by
  have h1 : (0 : ℝ) ≤ ddist ha hb := (DirLine.le_iff_zero_le_ddist ha hb).mp a_le_b
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
  rcases h3 with ⟨x1, hx1⟩
  have h1 : (0 : ℝ) ≤ inner (VEC A B) (Dl.toDir).unitVec := by exact h1
  have h1 : (0 : ℝ) ≤ x1 := by
    calc
    (0 : ℝ)
    _≤  inner (x1 • Dl.toDir.unitVec) Dl.toDir.unitVec := by simp only [hx1.symm]; exact h1
    _= x1 * inner Dl.toDir.unitVec Dl.toDir.unitVec := by
      apply InnerProductSpace.smul_left
    _= x1 := by simp only [Dir.inner_unitVec, vsub_self, AngValue.cos_zero, mul_one]
  use x1

theorem lt_of_exist_pos_smul {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (h : ∃ (x : ℝ), ((0 : ℝ) < x) ∧ (VEC A B) = x • (Dl.toDir).unitVec): lelem A ha < lelem B hb := by
  rcases h with ⟨x, ⟨xpos, h⟩⟩
  by_contra h1
  have : ¬ 0 < ddist ha hb := by
    by_contra h3; absurd h1
    apply (DirLine.lt_iff_zero_lt_ddist ha hb).mpr h3
  simp only [not_lt] at this
  have : lelem B hb ≤ lelem A ha := by
    apply (DirLine.le_iff_zero_le_ddist hb ha).mpr
    calc
    _≤ - ddist ha hb := by linarith
    _= ddist hb ha := by
      unfold ddist; simp only [neg_vsub_eq_vsub_rev]
  rcases exist_nonneg_smul_of_le hb ha this with ⟨t, ⟨tnneg, ht⟩⟩
  have : (VEC A B) = - (VEC B A) := by simp only [neg_vec]
  simp only [this, ht] at h
  have : -(t • Dl.toDir.unitVec) = (-t) • Dl.toDir.unitVec := by simp only [neg_smul]
  simp only [this] at h
  have h2 : (x + t) • Dl.toDir.unitVec = (0 : Vec) := by
    calc
    _= x • Dl.toDir.unitVec + t • Dl.toDir.unitVec := by apply add_smul
    _= (-t) • Dl.toDir.unitVec + t • Dl.toDir.unitVec := by simp only [h.symm]
    _= (-t + t) • Dl.toDir.unitVec := by simp only [neg_smul, add_left_neg, zero_smul]
    _= 0 • Dl.toDir.unitVec := by simp only [add_left_neg, zero_smul]
    _= (0 : Vec) := by simp only [zero_smul]
  have : Dl.toDir.unitVec ≠ (0 : Vec) := by
    simp only [ne_eq, VecND.ne_zero, not_false_eq_true]
  have h1 : x + t = 0 := by
    by_contra h1; push_neg at h1
    absurd this
    calc
    _= ((x + t)⁻¹ * (x + t)) • Dl.toDir.unitVec := by
      field_simp
    _= (x + t)⁻¹ • ((x + t) • Dl.toDir.unitVec) := by apply mul_smul
    _= (x + t)⁻¹ • (0 : Vec) := by simp only [h2]
    _= (0 : Vec) := by simp only [smul_zero]
  linarith

theorem le_of_exist_nonneg_smul {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (h : ∃ (x : ℝ), ((0 : ℝ) ≤ x) ∧ (VEC A B) = x • (Dl.toDir).unitVec): lelem A ha ≤ lelem B hb := by
  rcases h with ⟨x, ⟨xnneg, h⟩⟩
  rcases lt_or_eq_of_le xnneg with (xpos | h0)
  apply le_of_lt
  apply lt_of_exist_pos_smul ha hb
  use x
  simp only [h0.symm, zero_smul] at h
  have : A = B := by
    apply eq_iff_vec_eq_zero.mpr
    have : (VEC B A) = - (VEC A B) := by simp only [neg_vec]
    simp only [this, h, neg_zero]
  simp only [this, le_refl]

-- LiesInt SegND.extension and LiesOn Seg
theorem lies_int_seg_nd_ext_iff_lies_int (A B C : P) [a_ne_c : PtNe A C] : B LiesInt (SEG_nd A C).extension ↔ C LiesInt (SEG A B) := by
  constructor
  · rintro h1
    rcases Ray.lies_int_iff.mp h1 with ⟨x1, ⟨x1pos, hx1⟩⟩
    rcases Ray.lies_int_iff.mp (Ray.snd_pt_lies_int_mk_pt_pt A C) with ⟨x2, ⟨x2pos, hx2⟩⟩
    apply Seg.lies_int_iff.mpr
    constructor
    · show B ≠ A
      by_contra h3; simp only [h3] at h1; absurd h1;
      apply SegND.not_lies_int_extn_of_lies_on
      show A LiesOn (SEG A C)
      apply Seg.source_lies_on
    · use x2 / (x1 + x2)
      · constructor
        · positivity
        · constructor
          · have : 0 < 1 - (x2 / (x1 + x2)) := by
              calc
              _< x1 / (x1 + x2) := by positivity
              _= 1 - (x2 / (x1 + x2)) := by field_simp
            linarith
          · symm;
            calc
            _= (x2 / (x1 + x2)) • (VEC A B) := by rfl
            _= (x2 / (x1 + x2)) • (VEC A C + VEC C B) := by congr 1; simp only [vec_add_vec]
            _= (x2 / (x1 + x2)) • (VEC A C) + (x2 / (x1 + x2)) • (VEC C B) := by apply smul_add
            _= (x2 / (x1 + x2)) • (VEC A C) + (x2 / (x1 + x2)) • x1 • (SegND.extension (SEG_nd A C)).toDir.unitVec := by congr 2;
            _= (x2 / (x1 + x2)) • (VEC A C) + (x2 / (x1 + x2)) • x1 • (RAY A C).toDir.unitVec := by rfl
            _= (x2 / (x1 + x2)) • (VEC A C) + ((x2 / (x1 + x2)) * x1) • (RAY A C).toDir.unitVec := by congr 1; symm; apply mul_smul
            _= (x2 / (x1 + x2)) • (VEC A C) + ((x1 / (x1 + x2)) * x2) • (RAY A C).toDir.unitVec := by congr 2; field_simp; ring
            _= (x2 / (x1 + x2)) • (VEC A C) + (x1 / (x1 + x2)) • x2 • (RAY A C).toDir.unitVec := by congr 1; apply mul_smul
            _= (x2 / (x1 + x2)) • (VEC A C) + (x1 / (x1 + x2)) • (VEC A C) := by
              congr 2; symm;
              show VEC (RAY A C).source C = x2 • (RAY A C).toDir.unitVec
              exact hx2
            _= (x2 / (x1 + x2) + x1 / (x1 + x2)) • (VEC A C) := by symm; apply add_smul
            _= (1 : ℝ) • (VEC A C) := by congr 1; field_simp; ring;
            _= _ := by simp only [one_smul]
  · rintro h1
    rcases Seg.lies_int_iff.mp h1 with ⟨_, ⟨x1, ⟨x1pos, ⟨x1lt1, hx1⟩⟩⟩⟩
    rcases Ray.lies_int_iff.mp (Ray.snd_pt_lies_int_mk_pt_pt A C) with ⟨x2, ⟨x2pos, hx2⟩⟩
    apply Ray.lies_int_iff.mpr
    have : 0 < 1 - x1 := by simp only [sub_pos, x1lt1]
    use ((1 - x1) / x1) * x2
    constructor
    · positivity
    · show (VEC C B) = (((1 - x1) / x1) * x2) • (RAY A C).toDir.unitVec
      symm;
      calc
      _= ((1 - x1) / x1) • x2 • (RAY A C).toDir.unitVec := by apply mul_smul
      _= ((1 - x1) / x1) • (VEC A C) := by simp only [hx2.symm]; congr 1;
      _= ((1 - x1) / x1) • x1 • (VEC A B) := by congr 1;
      _= (((1 - x1) / x1) * x1) • (VEC A B) := by symm; apply mul_smul
      _= (1 - x1) • (VEC A B) := by congr 1; field_simp
      _= (1 + (-x1)) • (VEC A B) := by congr 1;
      _= (1 : ℝ) • (VEC A B) + (-x1) • (VEC A B) := by apply add_smul
      _= (VEC A B) + (- x1 • VEC A B) := by congr 1; apply one_smul;
      _= (VEC A B) + (- (x1 • (VEC A B))) := by
        congr 1; apply neg_smul
      _= (VEC A B) - (x1 • (VEC A B)) := by symm; apply sub_eq_add_neg
      _= (VEC A B) - (VEC A C) := by
        congr 1; symm;
        show VEC (SEG A B).source C = x1 • (SEG A B).toVec
        exact hx1
      _= (VEC C B) := by simp only [vec_sub_vec]

-- LiesOn SegND.extension and LiesInt Seg
theorem lies_on_seg_nd_ext_iff_lies_on (A B C : P) [a_ne_c : PtNe A C] : B LiesOn (SEG_nd A C).extension ↔ C LiesOn (SEG A B) := by
  rcases eq_or_ne B C with (b_eq_c | b_ne_c)
  · simp only [b_eq_c]
    have h : C LiesOn (SEG_nd A C) ∧ C LiesOn SegND.extension (SEG_nd A C) := by
      apply (SegND.eq_target_iff_lies_on_lies_on_extn (A := C) (seg_nd := (SEG_nd A C))).mpr
      rfl
    simp only [h, true_iff]
    show C LiesOn (SEG_nd A C)
    exact h.1
  · constructor
    · rintro h1
      have : B LiesInt SegND.extension (SEG_nd A C) := by refine' ⟨h1, b_ne_c⟩
      apply Seg.lies_on_of_lies_int
      exact (lies_int_seg_nd_ext_iff_lies_int A B C).mp this
    · rintro h1
      have : C LiesInt (SEG A B) := by refine' ⟨h1, a_ne_c.out.symm, b_ne_c.symm⟩
      apply Ray.lies_on_of_lies_int
      exact (lies_int_seg_nd_ext_iff_lies_int A B C).mpr this

-- # Order Relations to Position Relations
-- linear order and LiesInt Seg
theorem lies_int_seg_of_lt_and_lt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_lt_b : lelem A ha < lelem B hb) (b_lt_c : lelem B hb < lelem C hc) : B LiesInt (SEG A C) := by
  rcases exist_pos_smul_of_lt ha hb a_lt_b with ⟨x1, ⟨x1pos, hx1⟩⟩
  rcases exist_pos_smul_of_lt hb hc b_lt_c with ⟨x2, ⟨x2pos, hx2⟩⟩
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

theorem lies_int_seg_of_gt_and_gt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_gt_b : (lelem A ha) > (lelem B hb)) (b_gt_c : (lelem B hb) > (lelem C hc)) : B LiesInt (SEG A C) := by
  apply Seg.lies_int_rev_iff_lies_int.mp
  apply lies_int_seg_of_lt_and_lt hc hb ha
  exact b_gt_c
  exact a_gt_b

-- linear order and LiesOn Seg
theorem lies_on_seg_of_le_and_le {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_le_b : lelem A ha ≤ lelem B hb) (b_le_c : lelem B hb ≤ lelem C hc) : B LiesOn (SEG A C) := by
  have h1 : (lelem A ha = lelem B hb) ∨ (lelem A ha < lelem B hb) := le_iff_eq_or_lt.mp a_le_b
  have h2 : (lelem B hb = lelem C hc) ∨ (lelem B hb < lelem C hc) := le_iff_eq_or_lt.mp b_le_c
  rcases h1 with (a_eq_b | a_lt_b)
  · have : A = B := Subtype.val_inj.mpr a_eq_b
    simp only [this.symm]
    apply Seg.source_lies_on
  · rcases h2 with (b_eq_c | b_lt_c)
    have : B = C := Subtype.val_inj.mpr b_eq_c
    simp only [this]
    apply Seg.target_lies_on
    · have : B LiesInt (SEG A C) := lies_int_seg_of_lt_and_lt ha hb hc a_lt_b b_lt_c
      exact Seg.lies_on_of_lies_int this

theorem lies_on_seg_of_ge_and_ge {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_ge_b : (lelem A ha) ≥ (lelem B hb)) (b_ge_c : (lelem B hb) ≥ (lelem C hc)) : B LiesOn (SEG A C) := by
  apply Seg.lies_on_rev_iff_lies_on.mp
  apply lies_on_seg_of_le_and_le hc hb ha
  exact b_ge_c
  exact a_ge_b

-- linear order and toDir
theorem eq_toDir_of_lt {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (a_lt_b : lelem A ha < lelem B hb) : (RAY A B ((ne_iff_ne_as_line_elem ha hb).mpr (ne_of_lt a_lt_b)).symm).toDir = Dl.toDir := by
  haveI B_ne_A : PtNe B A := ⟨((ne_iff_ne_as_line_elem ha hb).mpr (ne_of_lt a_lt_b)).symm⟩
  rcases exist_pos_smul_of_lt ha hb a_lt_b with ⟨x1, ⟨x1pos, hx1⟩⟩
  calc
  _= (VEC_nd A B).toDir := by rfl
  _= (Dl.toDir.unitVecND).toDir := by
    apply VecND.toDir_eq_toDir_iff.mpr
    unfold VecND.SameDir
    use x1; simp only [ne_eq, VecND.coe_mkPtPt, Dir.coe_unitVecND, hx1, and_true, x1pos]
  _=_ := by simp only [Dir.unitVecND_toDir]

theorem neg_toDir_of_gt {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (a_gt_b : lelem A ha > lelem B hb) : (RAY A B ((ne_iff_ne_as_line_elem ha hb).mpr (ne_of_gt a_gt_b)).symm).toDir = - Dl.toDir := by
  haveI B_ne_A : PtNe B A := ⟨((ne_iff_ne_as_line_elem ha hb).mpr (ne_of_gt a_gt_b)).symm⟩
  rcases exist_pos_smul_of_lt hb ha a_gt_b with ⟨x1, ⟨x1pos, hx1⟩⟩
  calc
  _= (VEC_nd A B).toDir := by rfl
  _= - (VEC_nd B A).toDir := by
    have : (VEC_nd A B) = - (VEC_nd B A) := by ext; simp only [ne_eq, VecND.coe_mkPtPt, RayVector.coe_neg, neg_vec]
    simp only [this]
    apply VecND.neg_toDir (VEC_nd B A)
  _= - (Dl.toDir.unitVecND).toDir := by
    simp only [neg_inj]
    apply VecND.toDir_eq_toDir_iff.mpr
    unfold VecND.SameDir
    use x1; simp only [ne_eq, VecND.coe_mkPtPt, Dir.coe_unitVecND, hx1, and_true, x1pos]
  _=_ := by simp only [Dir.unitVecND_toDir]

-- linear order and LiesInt ray
theorem lies_int_ray_of_lt_and_lt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_lt_b : lelem A ha < lelem B hb) (a_lt_c : lelem A ha < lelem C hc) : B LiesInt (RAY A C ((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_lt a_lt_c)).symm):= by
  haveI : PtNe C A := ⟨((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_lt a_lt_c)).symm⟩
  rcases exist_pos_smul_of_lt ha hb a_lt_b with ⟨x1, ⟨x1pos, hx1⟩⟩
  apply Ray.lies_int_iff.mpr
  use x1
  constructor
  · exact x1pos
  · have : (RAY A C).toDir = Dl.toDir := eq_toDir_of_lt ha hc a_lt_c
    simp only [this]
    exact hx1

theorem lies_int_ray_of_gt_and_gt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_gt_b : lelem A ha > lelem B hb) (a_gt_c : lelem A ha > lelem C hc) : B LiesInt (RAY A C ((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm):= by
  haveI : PtNe C A := ⟨((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm⟩
  rcases exist_pos_smul_of_lt hb ha a_gt_b with ⟨x1, ⟨x1pos, hx1⟩⟩
  apply Ray.lies_int_iff.mpr
  use x1
  constructor
  · exact x1pos
  · have : (RAY A C).toDir = - Dl.toDir := neg_toDir_of_gt ha hc a_gt_c
    simp only [this]
    have : (VEC A B) = - (VEC B A) := by simp only [ne_eq, VecND.coe_mkPtPt, RayVector.coe_neg, neg_vec]
    simp only [Dir.neg_unitVec, smul_neg]
    show (VEC A B) = - (x1 • Dl.toDir.unitVec)
    simp only [this, hx1]

-- linear order and LiesOn ray
theorem lies_on_ray_of_le_and_lt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_le_b : lelem A ha ≤ lelem B hb) (a_lt_c : lelem A ha < lelem C hc) : B LiesOn (RAY A C ((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_lt a_lt_c)).symm):= by
  haveI : PtNe C A := ⟨((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_lt a_lt_c)).symm⟩
  rcases exist_nonneg_smul_of_le ha hb a_le_b with ⟨x1, ⟨x1nneg, hx1⟩⟩
  apply Ray.lies_on_iff.mpr
  use x1
  constructor
  · exact x1nneg
  · have : (RAY A C).toDir = Dl.toDir := eq_toDir_of_lt ha hc a_lt_c
    simp only [this]
    exact hx1

theorem lies_on_ray_of_ge_and_gt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_ge_b : lelem A ha ≥ lelem B hb) (a_gt_c : lelem A ha > lelem C hc) : B LiesOn (RAY A C ((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm):= by
  haveI : PtNe C A := ⟨((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm⟩
  rcases exist_nonneg_smul_of_le hb ha a_ge_b with ⟨x1, ⟨x1nneg, hx1⟩⟩
  apply Ray.lies_on_iff.mpr
  use x1
  constructor
  · exact x1nneg
  · have : (RAY A C).toDir = - Dl.toDir := neg_toDir_of_gt ha hc a_gt_c
    simp only [this]
    have : (VEC A B) = - (VEC B A) := by simp only [ne_eq, VecND.coe_mkPtPt, RayVector.coe_neg, neg_vec]
    simp only [Dir.neg_unitVec, smul_neg]
    show (VEC A B) = - (x1 • Dl.toDir.unitVec)
    simp only [this, hx1]

-- linear order and LiesInt SegND.extension
theorem lies_int_seg_nd_ext_of_lt_and_lt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_lt_c : lelem A ha < lelem C hc) (c_lt_b : lelem C hc < lelem B hb) : B LiesInt (SEG_nd A C ((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_lt a_lt_c)).symm).extension := by
  haveI C_ne_A : PtNe C A := ⟨((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_lt a_lt_c)).symm⟩
  rcases exist_pos_smul_of_lt hc hb c_lt_b with ⟨x2, ⟨x2pos, hx2⟩⟩
  apply Ray.lies_int_iff.mpr
  use x2
  constructor
  · exact x2pos
  · simp only [SegND.extn_toDir, Dir.quotient_mk_eq, SegND.mkPtPt_toDir]
    have : (VEC_nd A C).toDir = Dl.toDir :=
      calc
      _= (RAY A C).toDir := by rfl
      _= _ := eq_toDir_of_lt ha hc a_lt_c
    simp only [this]
    exact hx2

theorem lies_int_seg_nd_ext_of_gt_and_gt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_gt_c : lelem A ha > lelem C hc) (c_gt_b : lelem C hc > lelem B hb) : B LiesInt (SEG_nd A C ((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm).extension := by
  haveI C_ne_A : PtNe C A := ⟨((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm⟩
  rcases exist_pos_smul_of_lt hb hc c_gt_b with ⟨x2, ⟨x2pos, hx2⟩⟩
  apply Ray.lies_int_iff.mpr
  use x2
  constructor
  · exact x2pos
  · simp only [SegND.extn_toDir, Dir.quotient_mk_eq, SegND.mkPtPt_toDir]
    have : (VEC_nd A C).toDir = - Dl.toDir :=
      calc
      _= (RAY A C).toDir := by rfl
      _= _ := neg_toDir_of_gt ha hc a_gt_c
    simp only [this, Dir.neg_unitVec, smul_neg]
    show (VEC C B) = - (x2 • Dl.toDir.unitVec)
    have : (VEC C B) = - (VEC B C) := by simp only [neg_vec]
    simp only [this, neg_inj, hx2]

-- linear order and LiesOn SegND.extension
theorem lies_on_seg_nd_ext_of_lt_and_le {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_lt_c : lelem A ha < lelem C hc) (c_le_b : lelem C hc ≤ lelem B hb) : B LiesOn (SEG_nd A C ((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_lt a_lt_c)).symm).extension := by
  haveI C_ne_A : PtNe C A := ⟨((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_lt a_lt_c)).symm⟩
  rcases exist_nonneg_smul_of_le hc hb c_le_b with ⟨x2, ⟨x2nneg, hx2⟩⟩
  apply Ray.lies_on_iff.mpr
  use x2
  constructor
  · exact x2nneg
  · simp only [SegND.extn_toDir, Dir.quotient_mk_eq, SegND.mkPtPt_toDir]
    have : (VEC_nd A C).toDir = Dl.toDir :=
      calc
      _= (RAY A C).toDir := by rfl
      _= _ := eq_toDir_of_lt ha hc a_lt_c
    simp only [this]
    exact hx2

theorem lies_on_seg_nd_ext_of_gt_and_ge {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_gt_c : lelem A ha > lelem C hc) (c_ge_b : lelem C hc ≥ lelem B hb) : B LiesOn (SEG_nd A C ((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm).extension := by
  haveI C_ne_A : PtNe C A := ⟨((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm⟩
  rcases exist_nonneg_smul_of_le hb hc c_ge_b with ⟨x2, ⟨x2nneg, hx2⟩⟩
  apply Ray.lies_on_iff.mpr
  use x2
  constructor
  · exact x2nneg
  · simp only [SegND.extn_toDir, Dir.quotient_mk_eq, SegND.mkPtPt_toDir]
    have : (VEC_nd A C).toDir = - Dl.toDir :=
      calc
      _= (RAY A C).toDir := by rfl
      _= _ := neg_toDir_of_gt ha hc a_gt_c
    simp only [this, Dir.neg_unitVec, smul_neg]
    show (VEC C B) = - (x2 • Dl.toDir.unitVec)
    have : (VEC C B) = - (VEC B C) := by simp only [neg_vec]
    simp only [this, neg_inj, hx2]

-- # Position Relations to Order Relations
-- linear order and LiesInt Seg
theorem lt_and_lt_of_lies_int_seg_and_le {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (hac : B LiesInt (SEG A C)) (a_le_c : lelem A ha ≤ lelem C hc) : ((lelem A ha) < (lelem B hb)) ∧ ((lelem B hb) < (lelem C hc)) := by
  have a_ne_c : A ≠ C := by
    by_contra h'
    simp only [h'] at hac
    have : C ≠ C := by exact (Seg.lies_int_iff.mp hac).1
    contradiction
  have : lelem A ha ≠ lelem C hc := by
    simp only [ne_eq, Subtype.mk.injEq, a_ne_c, not_false_eq_true]
  have : lelem A ha < lelem C hc := by
    apply lt_of_le_of_ne a_le_c this
  rcases (exist_pos_smul_of_lt ha hc this) with ⟨x1, ⟨x1pos, hx1⟩⟩
  rcases (Seg.lies_int_iff.mp hac) with ⟨_, ⟨x2, ⟨x2pos, ⟨x2lt1, hx2⟩⟩⟩⟩
  have : (SEG A C).toVec = (VEC A C) := by simp only [seg_toVec_eq_vec]
  simp only [this] at hx2
  constructor
  · apply lt_of_exist_pos_smul ha hb
    use x2 * x1
    constructor
    · positivity
    · simp only [mul_smul, hx1.symm]
      exact hx2
  · apply lt_of_exist_pos_smul hb hc
    use (1 - x2) * x1
    constructor
    · simp only [gt_iff_lt, x1pos, mul_pos_iff_of_pos_right, sub_pos, x2lt1]
    · simp only [mul_smul, hx1.symm]
      calc
      _= (VEC A C) - (VEC A B) := by simp only [vec_sub_vec]
      _= 1 • (VEC A C) - x2 • (VEC A C) := by congr 1; simp only [one_smul]
      _= 1 • (VEC A C) + (- x2) • (VEC A C) := by simp only [one_smul, neg_smul]; exact rfl
      _= (1 + (-x2)) • (VEC A C) := by symm; simp only [add_smul 1 (-x2) (VEC A C), one_smul, neg_smul]
      _= _ := by congr 1;

theorem ord_of_lies_int_seg {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (hac : B LiesInt (SEG A C)) : (((lelem A ha) < (lelem B hb)) ∧ ((lelem B hb) < (lelem C hc))) ∨ (((lelem A ha) > (lelem B hb)) ∧ ((lelem B hb) > (lelem C hc))) := by
  have : lelem A ha ≠ lelem C hc := by
    have a_ne_c : A ≠ C := by
      by_contra h'
      simp only [h'] at hac
      have : C ≠ C := by exact (Seg.lies_int_iff.mp hac).1
      contradiction
    simp only [ne_eq, Subtype.mk.injEq, a_ne_c, not_false_eq_true]
  have : (lelem A ha ≤ lelem C hc) ∨ (lelem C hc ≤ lelem A ha) := le_total (lelem A ha) (lelem C hc)
  rcases this with (a_le_c | c_le_a)
  · left
    apply lt_and_lt_of_lies_int_seg_and_le ha hb hc hac a_le_c
  · right
    have : lelem C hc < lelem B hb ∧ lelem B hb < lelem A ha := by
      apply lt_and_lt_of_lies_int_seg_and_le hc hb ha _ c_le_a
      exact Seg.lies_int_rev_iff_lies_int.mp hac
    simp only [gt_iff_lt, this, and_self]

theorem lt_iff_lt_of_lies_int_seg₁₃ {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (hac : B LiesInt (SEG A C)) : (lelem A ha) < (lelem B hb) ↔ (lelem B hb) < (lelem C hc) := by
  have : (((lelem A ha) < (lelem B hb)) ∧ ((lelem B hb) < (lelem C hc))) ∨ (((lelem A ha) > (lelem B hb)) ∧ ((lelem B hb) > (lelem C hc))) := ord_of_lies_int_seg ha hb hc hac
  constructor
  · rintro h1; by_contra h2; absurd this; push_neg
    constructor
    · simp only [h1, h2, not_false_eq_true, forall_true_left]; exact le_of_not_lt h2
    · simp only [gt_iff_lt, (not_lt_of_le (le_of_lt h1)), IsEmpty.forall_iff]
  · rintro h1; by_contra h2; absurd this; push_neg
    constructor
    · rintro h3; contradiction
    · rintro _; exact le_of_lt h1

theorem lt_iff_lt_of_lies_int_seg₁₂ {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (hac : B LiesInt (SEG A C)) : (lelem A ha) < (lelem B hb) ↔ (lelem A ha) < (lelem C hc) := by
  have : (((lelem A ha) < (lelem B hb)) ∧ ((lelem B hb) < (lelem C hc))) ∨ (((lelem A ha) > (lelem B hb)) ∧ ((lelem B hb) > (lelem C hc))) := ord_of_lies_int_seg ha hb hc hac
  constructor
  · rintro h1; by_contra h2; absurd this; push_neg
    constructor
    · rintro _; by_contra h3; absurd h2; exact lt_trans h1 (lt_of_not_le h3)
    · simp only [gt_iff_lt, not_lt_of_le (le_of_lt h1), IsEmpty.forall_iff]
  · by_contra h3; push_neg at h3
    rcases this with (hl | hr)
    · absurd hl; push_neg at hl; simp only [not_and]; rintro h4; exfalso; absurd h4; exact not_lt_of_le h3.2
    · have : lelem A ha > lelem C hc := gt_trans hr.1 hr.2
      have : ¬ lelem A ha < lelem C hc := not_lt_of_le (le_of_lt (lt_trans hr.2 hr.1))
      absurd this; exact h3.1

theorem lt_iff_lt_of_lies_int_seg₂₃ {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (hac : B LiesInt (SEG A C)) : (lelem A ha) < (lelem C hc) ↔ (lelem B hb) < (lelem C hc) := by
  simp only [(lt_iff_lt_of_lies_int_seg₁₂ ha hb hc hac).symm,
    (lt_iff_lt_of_lies_int_seg₁₃ ha hb hc hac)]

-- linear order and LiesOn seg
theorem le_and_le_of_lies_on_seg_and_le {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (hac : B LiesOn (SEG A C)) (a_le_c : lelem A ha ≤ lelem C hc) : ((lelem A ha) ≤ (lelem B hb)) ∧ ((lelem B hb) ≤ (lelem C hc)) := by
  rcases eq_or_ne B A with (heq | h1)
  simp only [heq, le_refl, a_le_c, and_self]
  rcases eq_or_ne B C with (heq | h2)
  simp only [heq, a_le_c, le_refl, and_self]
  have : B LiesInt (SEG A C) := by
    refine' ⟨hac, h1, h2⟩
  exact ⟨le_of_lt (lt_and_lt_of_lies_int_seg_and_le ha hb hc this a_le_c).1, le_of_lt (lt_and_lt_of_lies_int_seg_and_le ha hb hc this a_le_c).2⟩

theorem ord_of_lies_on_seg {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesOn (SEG A C)) : (lelem A ha ≤ lelem B hb ∧ lelem B hb ≤ lelem C hc) ∨ (lelem A ha ≥ lelem B hb ∧ lelem B hb ≥ lelem C hc) := by
  have : (lelem A ha ≤ lelem C hc) ∨ (lelem C hc ≤ lelem A ha) := le_total (lelem A ha) (lelem C hc)
  rcases this with (a_le_c | c_le_a)
  · left
    exact le_and_le_of_lies_on_seg_and_le ha hb hc h a_le_c
  · right
    have : lelem C hc ≤ lelem B hb ∧ lelem B hb ≤ lelem A ha := by
      apply le_and_le_of_lies_on_seg_and_le hc hb ha _ c_le_a
      exact Seg.lies_on_rev_iff_lies_on.mp h
    simp only [ge_iff_le, this, and_self]

theorem le_of_lies_on_seg_and_lt₃₁ {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesOn (SEG A C)) (h1 : lelem A ha < lelem B hb) : lelem B hb ≤ lelem C hc := by
  have : (lelem A ha ≤ lelem B hb ∧ lelem B hb ≤ lelem C hc) ∨ (lelem A ha ≥ lelem B hb ∧ lelem B hb ≥ lelem C hc) := ord_of_lies_on_seg ha hb hc h
  rcases this with (hl | hr)
  · exact hl.2
  · exfalso; absurd hr.1; exact not_le_of_lt h1

theorem lt_of_lies_on_seg_and_lt₂₁ {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesOn (SEG A C)) (h1 : lelem A ha < lelem B hb) : lelem A ha < lelem C hc := lt_of_lt_of_le h1 (le_of_lies_on_seg_and_lt₃₁ ha hb hc h h1)

theorem le_of_lies_on_seg_and_lt₁₃ {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesOn (SEG A C)) (h3 : lelem B hb < lelem C hc) : lelem A ha ≤ lelem B hb := by
  have : (lelem A ha ≤ lelem B hb ∧ lelem B hb ≤ lelem C hc) ∨ (lelem A ha ≥ lelem B hb ∧ lelem B hb ≥ lelem C hc) := ord_of_lies_on_seg ha hb hc h
  rcases this with (hl | hr)
  · exact hl.1
  · exfalso; absurd hr.2; exact not_le_of_lt h3

theorem lt_of_lies_on_seg_and_lt₂₃ {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesOn (SEG A C)) (h3 : lelem B hb < lelem C hc) : lelem A ha < lelem C hc := lt_of_le_of_lt (le_of_lies_on_seg_and_lt₁₃ ha hb hc h h3) h3

theorem le_of_lies_on_seg_and_le₁₂ {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesOn (SEG A C)) (h2 : lelem A ha ≤ lelem C hc) : lelem A ha ≤ lelem B hb := by
  have : (lelem A ha ≤ lelem B hb ∧ lelem B hb ≤ lelem C hc) ∨ (lelem A ha ≥ lelem B hb ∧ lelem B hb ≥ lelem C hc) := ord_of_lies_on_seg ha hb hc h
  rcases this with (hl | hr)
  · exact hl.1
  · exact le_trans h2 hr.2

theorem le_of_lies_on_seg_and_le₃₂ {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesOn (SEG A C)) (h2 : lelem A ha ≤ lelem C hc) : lelem B hb ≤ lelem C hc := by
  have : (lelem A ha ≤ lelem B hb ∧ lelem B hb ≤ lelem C hc) ∨ (lelem A ha ≥ lelem B hb ∧ lelem B hb ≥ lelem C hc) := ord_of_lies_on_seg ha hb hc h
  rcases this with (hl | hr)
  · exact hl.2
  · exact le_trans hr.1 h2

-- linear order and LiesInt ray
theorem lt_iff_lt_of_lies_int_ray {Dl : DirLine P} {A B C : P} [hh : PtNe A C] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesInt (RAY A C)) : lelem A ha < lelem C hc ↔ lelem A ha < lelem B hb := by
  rcases Ray.lies_int_iff.mp h with ⟨x2, ⟨x2pos, hx2⟩⟩
  rcases Ray.lies_int_iff.mp (Ray.snd_pt_lies_int_mk_pt_pt A C) with ⟨x1, ⟨x1pos, hx1⟩⟩
  have h1 : (VEC A C) = (x1 / x2) • (VEC A B) := by
    calc
    _= x1 • (RAY A C).toDir.unitVec := hx1
    _= ((x1 / x2) * x2) • (RAY A C).toDir.unitVec := by
      congr 1; symm; apply div_mul_cancel_of_imp
      by_contra h'; push_neg at h'; linarith
    _= (x1 / x2) • (x2 • (RAY A C).toDir.unitVec) := by apply mul_smul
    _= _ := by congr 1; symm; exact hx2
  have h2 : (VEC A B) = (x2 / x1) • (VEC A C) := by
    calc
    _= x2 • (RAY A C).toDir.unitVec := hx2
    _= ((x2 / x1) * x1) • (RAY A C).toDir.unitVec := by
      congr 1; symm; apply div_mul_cancel_of_imp
      by_contra h'; push_neg at h'; linarith
    _= (x2 / x1) • (x1 • (RAY A C).toDir.unitVec) := by apply mul_smul
    _= _ := by congr 1; symm; exact hx1
  constructor
  · rintro h1; rcases exist_pos_smul_of_lt ha hc h1 with ⟨x3, ⟨x3pos, hx3⟩⟩
    apply lt_of_exist_pos_smul; use (x2 / x1) * x3
    constructor
    · positivity
    · symm;
      calc
      _= (x2 / x1) • (x3 • Dl.toDir.unitVec) := by apply mul_smul
      _= (x2 / x1) • (VEC A C) := by simp only [hx3]
      _= _ := by symm; exact h2
  · rintro h2; rcases exist_pos_smul_of_lt ha hb h2 with ⟨x3, ⟨x3pos, hx3⟩⟩
    apply lt_of_exist_pos_smul; use (x1 / x2) * x3
    constructor
    · positivity
    · symm;
      calc
      _= (x1 / x2) • (x3 • Dl.toDir.unitVec) := by apply mul_smul
      _= (x1 / x2) • (VEC A B) := by simp only [hx3]
      _= _ := by symm; exact h1

-- linear order and LiesOn ray
theorem lt_of_lies_on_ray_and_lt {Dl : DirLine P} {A B C : P} [hh : PtNe A C] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesOn (RAY A C)) (h1 : lelem A ha < lelem B hb) : lelem A ha < lelem C hc := by
  have : lelem A ha ≠ lelem B hb := ne_of_lt h1
  have : B ≠ A := by symm; exact (ne_iff_ne_as_line_elem ha hb).mpr this
  have : B LiesInt (RAY A C) := by refine' ⟨h, this⟩
  exact (lt_iff_lt_of_lies_int_ray ha hb hc this).mpr h1

theorem le_of_lies_on_ray_and_lt {Dl : DirLine P} {A B C : P} [hh : PtNe A C] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesOn (RAY A C)) (h1 : lelem A ha < lelem C hc) : lelem A ha ≤ lelem B hb := by
  rcases eq_or_ne A B with (heq | hne)
  · simp only [heq, le_refl]
  · have : B LiesInt (RAY A C) := by refine' ⟨h, hne.symm⟩
    exact le_of_lt ((lt_iff_lt_of_lies_int_ray ha hb hc this).mp h1)

-- linear order and toDir
theorem lt_of_eq_toDir {Dl : DirLine P} {A B : P} [a_ne_b : PtNe A B] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (h : (RAY A B).toDir = Dl.toDir) : lelem A ha < lelem B hb := by
  rcases Ray.lies_int_iff.mp (Ray.snd_pt_lies_int_mk_pt_pt A B) with ⟨x1, ⟨x1pos, hx1⟩⟩
  simp only [h] at hx1
  apply lt_of_exist_pos_smul; use x1;
  constructor
  · exact x1pos
  · show VEC (RAY A B).source B = x1 • Dl.toDir.unitVec
    exact hx1

theorem gt_of_neg_toDir {Dl : DirLine P} {A B : P} [a_ne_b : PtNe A B] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (h : (RAY A B).toDir = - Dl.toDir) : lelem A ha > lelem B hb := by
  have : (RAY B A).toDir = Dl.toDir := by
    calc
    _= (SEG_nd B A).toDir := by rfl
    _= - (SEG_nd A B).toDir := by apply SegND.toDir_of_rev_eq_neg_toDir (seg_nd := (SEG_nd A B))
    _= - (RAY A B).toDir := by congr 1;
    _= - - Dl.toDir := by simp only [h]
    _= _ := by simp only [neg_neg]
  exact lt_of_eq_toDir hb ha this

-- linear order and LiesInt SegND.extension
/-
-- `to be used for tactic testing`
theorem ord_of_lies_int_seg_nd_ext {Dl : DirLine P} {A B C : P} [a_ne_b : PtNe A B] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : C LiesInt (SEG_nd A B).extension) : ((lelem A ha < lelem B hb) ∧ (lelem B hb < lelem C hc)) ∨ ((lelem A ha > lelem B hb) ∧ (lelem B hb > lelem C hc)) := by sorry

theorem lt_iff_lt_of_lies_int_seg_ne_ext₁₂ {Dl : DirLine P} {A B C : P} [a_ne_b : PtNe A B] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : C LiesInt (SEG_nd A B).extension) : lelem A ha < lelem B hb ↔ lelem A ha < lelem C hc := by sorry

theorem lt_iff_lt_of_lies_int_seg_ne_ext₁₃ {Dl : DirLine P} {A B C : P} [a_ne_b : PtNe A B] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : C LiesInt (SEG_nd A B).extension) : lelem A ha < lelem B hb ↔ lelem B hb < lelem C hc := by sorry

theorem lt_iff_lt_of_lies_int_seg_ne_ext₂₃ {Dl : DirLine P} {A B C : P} [a_ne_b : PtNe A B] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : C LiesInt (SEG_nd A B).extension) : lelem A ha < lelem C hc ↔ lelem B hb < lelem C hc := by sorry
-/

-- linear order and LiesOn SegND.extension
/-
-- `to be used for tactic testing`
theorem ord_of_lies_on_seg_nd_ext {Dl : DirLine P} {A B C : P} [a_ne_b : PtNe A B] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : C LiesOn (SEG_nd A B).extension) : ((lelem A ha < lelem B hb) ∧ (lelem B hb ≤ lelem C hc)) ∨ ((lelem A ha > lelem B hb) ∧ (lelem B hb ≥ lelem C hc)) := by sorry

theorem le_of_lies_on_seg_nd_ext_and_le₃₁ {Dl : DirLine P} {A B C : P} [a_ne_b : PtNe A B] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : C LiesOn (SEG_nd A B).extension) (h1 : lelem A ha ≤ lelem B hb) : lelem B hb ≤ lelem C hc := by sorry

theorem lt_of_lies_on_seg_nd_ext_and_le₂₁ {Dl : DirLine P} {A B C : P} [a_ne_b : PtNe A B] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : C LiesOn (SEG_nd A B).extension) (h1 : lelem A ha ≤ lelem B hb) : lelem A ha < lelem C hc := by sorry

theorem le_of_lies_on_seg_nd_ext_and_le₃₂ {Dl : DirLine P} {A B C : P} [a_ne_b : PtNe A B] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : C LiesOn (SEG_nd A B).extension) (h2 : lelem A ha ≤ lelem C hc) : lelem B hb ≤ lelem C hc := by sorry

theorem lt_of_lies_on_seg_nd_ext_and_le₁₂ {Dl : DirLine P} {A B C : P} [a_ne_b : PtNe A B] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : C LiesOn (SEG_nd A B).extension) (h2 : lelem A ha ≤ lelem C hc) : lelem A ha < lelem B hb := by sorry

theorem lt_of_lies_on_seg_nd_ext_and_lt₁₃ {Dl : DirLine P} {A B C : P} [a_ne_b : PtNe A B] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : C LiesOn (SEG_nd A B).extension) (h3 : lelem B hb < lelem C hc) : lelem A ha < lelem B hb := by sorry

theorem lt_of_lies_on_seg_nd_ext_and_lt₂₃ {Dl : DirLine P} {A B C : P} [a_ne_b : PtNe A B] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : C LiesOn (SEG_nd A B).extension) (h3 : lelem B hb < lelem C hc) : lelem A ha < lelem C hc := by sorry
-/

section Corollary
-- # Corollary
-- `Hilbert Axioms II.3`
theorem lies_on_or_lies_on_or_lies_on_of_lies_on_DirLine {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) : (A LiesOn (SEG B C)) ∨ (B LiesOn (SEG A C)) ∨ (C LiesOn (SEG A B)) := by
  rcases le_total (lelem A ha) (lelem B hb) with (a_le_b | b_le_a)
  · rcases le_total (lelem B hb) (lelem C hc) with (b_le_c | c_le_b)
    · right; left; exact lies_on_seg_of_le_and_le ha hb hc a_le_b b_le_c
    · rcases le_total (lelem A ha) (lelem C hc) with (a_le_c | c_le_a)
      · right; right; exact lies_on_seg_of_le_and_le ha hc hb a_le_c c_le_b
      · left; exact lies_on_seg_of_ge_and_ge hb ha hc a_le_b c_le_a
  · rcases le_total (lelem B hb) (lelem C hc) with (b_le_c | c_le_b)
    · rcases le_total (lelem A ha) (lelem C hc) with (a_le_c | c_le_a)
      · left; exact lies_on_seg_of_le_and_le hb ha hc b_le_a a_le_c
      · right; right; exact lies_on_seg_of_ge_and_ge ha hc hb c_le_a b_le_c
    · right; left; exact lies_on_seg_of_ge_and_ge ha hb hc b_le_a c_le_b

theorem lies_on_or_lies_on_or_lies_on_of_lies_on_Line {l : Line P} {A B C : P} (ha : A LiesOn l) (hb : B LiesOn l) (hc : C LiesOn l) : (A LiesOn (SEG B C)) ∨ (B LiesOn (SEG A C)) ∨ (C LiesOn (SEG A B)) := by
  rcases eq_or_ne A B with (a_eq_b | a_ne_b)
  · left; simp only [a_eq_b]; apply Seg.source_lies_on
  · haveI : PtNe A B := ⟨a_ne_b⟩
    have : (RAY A B).toDirLine.toLine = l := by
      calc
      _= (LIN A B) := by rfl
      _= _ := by
        apply Line.eq_of_pt_pt_lies_on_of_ne _ _ ha hb
        apply Line.fst_pt_lies_on_mk_pt_pt
        apply Line.snd_pt_lies_on_mk_pt_pt
    have h1 : A LiesOn (RAY A B).toDirLine := by
      apply DirLine.lies_on_iff_lies_on_toLine.mp
      simp only [this]; exact ha
    have h2 : B LiesOn (RAY A B).toDirLine := by
      apply DirLine.lies_on_iff_lies_on_toLine.mp
      simp only [this]; exact hb
    have h3 : C LiesOn (RAY A B).toDirLine := by
      apply DirLine.lies_on_iff_lies_on_toLine.mp
      simp only [this]; exact hc
    exact lies_on_or_lies_on_or_lies_on_of_lies_on_DirLine h1 h2 h3

theorem lies_on_or_lies_on_or_lies_on_of_collinear {A B C : P} (h : Collinear A B C) : (A LiesOn (SEG B C)) ∨ (B LiesOn (SEG A C)) ∨ (C LiesOn (SEG A B)) := by
  rcases exist_line_of_collinear h with ⟨l, ⟨ha, ⟨hb, hc⟩⟩⟩
  exact lies_on_or_lies_on_or_lies_on_of_lies_on_Line ha hb hc

theorem lies_int_or_lies_int_or_lies_int_of_lies_on_DirLine {Dl : DirLine P} {A B C : P} [hh1 : PtNe A B] [hh2 : PtNe A C] [hh3 : PtNe B C] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) : (A LiesInt (SEG B C)) ∨ (B LiesInt (SEG A C)) ∨ (C LiesInt (SEG A B)) := by
  rcases lies_on_or_lies_on_or_lies_on_of_lies_on_DirLine ha hb hc with (h1 | (h2 | h3))
  · left; refine' ⟨h1, hh1.out, hh2.out⟩
  · right; left; refine' ⟨h2, hh1.out.symm, hh3.out⟩
  · right; right; refine' ⟨h3, hh2.out.symm, hh3.out.symm⟩

theorem lies_int_or_lies_int_or_lies_int_of_lies_on_Line {l : Line P} {A B C : P} [hh1 : PtNe A B] [hh2 : PtNe A C] [hh3 : PtNe B C] (ha : A LiesOn l) (hb : B LiesOn l) (hc : C LiesOn l) : (A LiesInt (SEG B C)) ∨ (B LiesInt (SEG A C)) ∨ (C LiesInt (SEG A B)) := by
  rcases lies_on_or_lies_on_or_lies_on_of_lies_on_Line ha hb hc with (h1 | (h2 | h3))
  · left; refine' ⟨h1, hh1.out, hh2.out⟩
  · right; left; refine' ⟨h2, hh1.out.symm, hh3.out⟩
  · right; right; refine' ⟨h3, hh2.out.symm, hh3.out.symm⟩

theorem lies_int_or_lies_int_or_lies_int_of_collinear {A B C : P} [hh1 : PtNe A B] [hh2 : PtNe A C] [hh3 : PtNe B C] (h : Collinear A B C) : (A LiesInt (SEG B C)) ∨ (B LiesInt (SEG A C)) ∨ (C LiesInt (SEG A B)) := by
  rcases lies_on_or_lies_on_or_lies_on_of_collinear h with (h1 | (h2 | h3))
  · left; refine' ⟨h1, hh1.out, hh2.out⟩
  · right; left; refine' ⟨h2, hh1.out.symm, hh3.out⟩
  · right; right; refine' ⟨h3, hh2.out.symm, hh3.out.symm⟩

theorem not_lies_int_and_lies_int₁ (A B C : P) : ¬ (B LiesInt (SEG A C) ∧ C LiesInt (SEG A B)) := by
  by_contra h
  rcases Seg.lies_int_iff.mp h.1 with ⟨h1, ⟨x1, ⟨x1pos, ⟨x1lt1, hx1⟩⟩⟩⟩
  rcases Seg.lies_int_iff.mp h.2 with ⟨_, ⟨x2, ⟨_, ⟨x2lt1, hx2⟩⟩⟩⟩
  haveI : PtNe C A := ⟨h1⟩
  have : (VEC A C) = (x2 * x1) • (VEC A C) := by
    calc
    _= x2 • (VEC A B) := by
      show VEC (SEG A B).source C = x2 • (SEG A B).toVec
      exact hx2
    _= x2 • x1 • (VEC A C) := by congr 1;
    _= (x2 * x1) • (VEC A C) := by symm; apply mul_smul
  have : (x2 * x1 - 1) • (VEC A C) = 0 := by
    calc
    _= (x2 * x1) • (VEC A C) - (1 : ℝ) • (VEC A C) := by apply sub_smul
    _= (VEC A C) - (VEC A C) := by simp only [this.symm, one_smul]
    _= 0 := by simp only [sub_self]
  simp at this
  have h2 : x2 * x1 < (1 : ℝ) := by
    calc
    _< (1 : ℝ) * 1 := by
      apply mul_lt_mul x2lt1 (le_of_lt x1lt1) x1pos _
      norm_num
    _= (1 : ℝ) := by norm_num
  have h2 : x2 * x1 - 1 ≠ 0 := by linarith
  simp only [h2, false_or] at this
  have : C = A := eq_iff_vec_eq_zero.mpr this
  absurd h1; exact this

theorem not_lies_int_and_lies_int₂ (A B C : P) : ¬ (A LiesInt (SEG B C) ∧ C LiesInt (SEG A B)) := by
  by_contra h
  have : ¬ (A LiesInt (SEG B C) ∧ C LiesInt (SEG B A)) := not_lies_int_and_lies_int₁ B A C
  absurd this
  exact ⟨h.1, Seg.lies_int_rev_iff_lies_int.mpr h.2⟩

theorem not_lies_int_and_lies_int₃ (A B C : P) : ¬ (A LiesInt (SEG B C) ∧ B LiesInt (SEG A C)) := by
  by_contra h
  have : _ := not_lies_int_and_lies_int₁ C A B
  absurd this
  exact ⟨Seg.lies_int_rev_iff_lies_int.mpr h.1, Seg.lies_int_rev_iff_lies_int.mpr h.2⟩

theorem lies_int_iff_not_lies_int_and_not_lies_int_of_lies_on_DirLine₁ {Dl : DirLine P} {A B C : P} [hh1 : PtNe A B] [hh2 : PtNe A C] [hh3 : PtNe B C] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) : (A LiesInt (SEG B C)) ↔ ((¬ B LiesInt (SEG A C)) ∧ (¬ C LiesInt (SEG A B))) := by
  have hh0 : _ := lies_int_or_lies_int_or_lies_int_of_lies_on_DirLine ha hb hc
  have hh1 : _ := not_lies_int_and_lies_int₁ A B C
  have hh2 : _ := not_lies_int_and_lies_int₂ A B C
  have hh3 : _ := not_lies_int_and_lies_int₃ A B C
  tauto

theorem lies_int_iff_not_lies_int_and_not_lies_int_of_lies_on_DirLine₂ {Dl : DirLine P} {A B C : P} [hh1 : PtNe A B] [hh2 : PtNe A C] [hh3 : PtNe B C] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) : (B LiesInt (SEG A C)) ↔ ((¬ A LiesInt (SEG B C)) ∧ (¬ C LiesInt (SEG A B))) := by
  have hh0 : _ := lies_int_or_lies_int_or_lies_int_of_lies_on_DirLine ha hb hc
  have hh1 : _ := not_lies_int_and_lies_int₁ A B C
  have hh2 : _ := not_lies_int_and_lies_int₂ A B C
  have hh3 : _ := not_lies_int_and_lies_int₃ A B C
  tauto

theorem lies_int_iff_not_lies_int_and_not_lies_int_of_lies_on_DirLine₃ {Dl : DirLine P} {A B C : P} [hh1 : PtNe A B] [hh2 : PtNe A C] [hh3 : PtNe B C] (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) : (C LiesInt (SEG A B)) ↔ ((¬ A LiesInt (SEG B C)) ∧ (¬ B LiesInt (SEG A C))) := by
  have hh0 : _ := lies_int_or_lies_int_or_lies_int_of_lies_on_DirLine ha hb hc
  have hh1 : _ := not_lies_int_and_lies_int₁ A B C
  have hh2 : _ := not_lies_int_and_lies_int₂ A B C
  have hh3 : _ := not_lies_int_and_lies_int₃ A B C
  tauto

theorem lies_int_iff_not_lies_int_and_not_lies_int_of_lies_on_Line₁ {l : Line P} {A B C : P} [hh1 : PtNe A B] [hh2 : PtNe A C] [hh3 : PtNe B C] (ha : A LiesOn l) (hb : B LiesOn l) (hc : C LiesOn l) : (A LiesInt (SEG B C)) ↔ ((¬ B LiesInt (SEG A C)) ∧ (¬ C LiesInt (SEG A B))) := by
  have hh0 : _ := lies_int_or_lies_int_or_lies_int_of_lies_on_Line ha hb hc
  have hh1 : _ := not_lies_int_and_lies_int₁ A B C
  have hh2 : _ := not_lies_int_and_lies_int₂ A B C
  have hh3 : _ := not_lies_int_and_lies_int₃ A B C
  tauto

theorem lies_int_iff_not_lies_int_and_not_lies_int_of_lies_on_Line₂ {l : Line P} {A B C : P} [hh1 : PtNe A B] [hh2 : PtNe A C] [hh3 : PtNe B C] (ha : A LiesOn l) (hb : B LiesOn l) (hc : C LiesOn l) : (B LiesInt (SEG A C)) ↔ ((¬ A LiesInt (SEG B C)) ∧ (¬ C LiesInt (SEG A B))) := by
  have hh0 : _ := lies_int_or_lies_int_or_lies_int_of_lies_on_Line ha hb hc
  have hh1 : _ := not_lies_int_and_lies_int₁ A B C
  have hh2 : _ := not_lies_int_and_lies_int₂ A B C
  have hh3 : _ := not_lies_int_and_lies_int₃ A B C
  tauto

theorem lies_int_iff_not_lies_int_and_not_lies_int_of_lies_on_Line₃ {l : Line P} {A B C : P} [hh1 : PtNe A B] [hh2 : PtNe A C] [hh3 : PtNe B C] (ha : A LiesOn l) (hb : B LiesOn l) (hc : C LiesOn l) : (C LiesInt (SEG A B)) ↔ ((¬ A LiesInt (SEG B C)) ∧ (¬ B LiesInt (SEG A C))) := by
  have hh0 : _ := lies_int_or_lies_int_or_lies_int_of_lies_on_Line ha hb hc
  have hh1 : _ := not_lies_int_and_lies_int₁ A B C
  have hh2 : _ := not_lies_int_and_lies_int₂ A B C
  have hh3 : _ := not_lies_int_and_lies_int₃ A B C
  tauto

theorem lies_int_iff_not_lies_int_and_not_lies_int_of_collinear₁ {A B C : P} [hh1 : PtNe A B] [hh2 : PtNe A C] [hh3 : PtNe B C] (h : Collinear A B C) : (A LiesInt (SEG B C)) ↔ ((¬ B LiesInt (SEG A C)) ∧ (¬ C LiesInt (SEG A B))) := by
  have hh0 : _ := lies_int_or_lies_int_or_lies_int_of_collinear h
  have hh1 : _ := not_lies_int_and_lies_int₁ A B C
  have hh2 : _ := not_lies_int_and_lies_int₂ A B C
  have hh3 : _ := not_lies_int_and_lies_int₃ A B C
  tauto

theorem lies_int_iff_not_lies_int_and_not_lies_int_of_collinear₂ {A B C : P} [hh1 : PtNe A B] [hh2 : PtNe A C] [hh3 : PtNe B C] (h : Collinear A B C) : (B LiesInt (SEG A C)) ↔ ((¬ A LiesInt (SEG B C)) ∧ (¬ C LiesInt (SEG A B))) := by
  have hh0 : _ := lies_int_or_lies_int_or_lies_int_of_collinear h
  have hh1 : _ := not_lies_int_and_lies_int₁ A B C
  have hh2 : _ := not_lies_int_and_lies_int₂ A B C
  have hh3 : _ := not_lies_int_and_lies_int₃ A B C
  tauto

theorem lies_int_iff_not_lies_int_and_not_lies_int_of_collinear₃ {A B C : P} [hh1 : PtNe A B] [hh2 : PtNe A C] [hh3 : PtNe B C] (h : Collinear A B C) : (C LiesInt (SEG A B)) ↔ ((¬ A LiesInt (SEG B C)) ∧ (¬ B LiesInt (SEG A C))) := by
  have hh0 : _ := lies_int_or_lies_int_or_lies_int_of_collinear h
  have hh1 : _ := not_lies_int_and_lies_int₁ A B C
  have hh2 : _ := not_lies_int_and_lies_int₂ A B C
  have hh3 : _ := not_lies_int_and_lies_int₃ A B C
  tauto

end Corollary

end linear_order
end DirLine

end EuclidGeom
