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

-- # theorems to introduce
-- for arbitrary three pts, there's one LiesInt the SEG of the rest two.
-- Pos_to_Ord LiesOn Seg
-- Pos_to_Ord LiesInt ray
-- Pos_to_Ord LiesOn ray
-- Pos_to_Ord LiesInt seg.ext
-- Pos_to_Ord LiesOn seg.ext

namespace DirLine
section linear_order
-- # preparatory theorems
abbrev lelem (A : P) {l : DirLine P} (ha : A LiesOn l) : l.carrier.Elem := ⟨A, ha⟩
-- linear order and ne
theorem ne_iff_ne_as_line_elem {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) : (A ≠ B) ↔ (lelem A ha ≠ lelem B hb) := by
  simp only [ne_eq, Subtype.mk.injEq]

-- linear order and vector
theorem HAHAHA_of_lt {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl)(a_lt_b : (lelem A ha) < (lelem B hb)) : (∃ t : ℝ, 0 < t ∧ (VEC A B) = t • (Dl.toDir).unitVec) := by
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

theorem HAHAHA_of_le {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl)(a_le_b : (lelem A ha) ≤ (lelem B hb)) : (∃ t : ℝ, 0 ≤ t ∧ (VEC A B) = t • (Dl.toDir).unitVec) := by
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

theorem lt_of_HAHAHA {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (h : ∃ (x : ℝ), ((0 : ℝ) < x) ∧ (VEC A B) = x • (Dl.toDir).unitVec): lelem A ha < lelem B hb := by
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
  rcases HAHAHA_of_le hb ha this with ⟨t, ⟨tnneg, ht⟩⟩
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

theorem le_of_HAHAHA {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (h : ∃ (x : ℝ), ((0 : ℝ) ≤ x) ∧ (VEC A B) = x • (Dl.toDir).unitVec): lelem A ha ≤ lelem B hb := by
  rcases h with ⟨x, ⟨xnneg, h⟩⟩
  rcases lt_or_eq_of_le xnneg with (xpos | h0)
  apply le_of_lt
  apply lt_of_HAHAHA ha hb
  use x
  simp only [h0.symm, zero_smul] at h
  have : A = B := by
    apply (eq_iff_vec_eq_zero B A).mpr
    have : (VEC B A) = - (VEC A B) := by simp only [neg_vec]
    simp only [this, h, neg_zero]
  simp only [this, le_refl]

-- # Order Relations to Position Relations
-- linear order and LiesInt Seg
theorem lies_int_seg_of_lt_and_lt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_lt_b : lelem A ha < lelem B hb) (b_lt_c : lelem B hb < lelem C hc) : B LiesInt (SEG A C) := by
  rcases HAHAHA_of_lt ha hb a_lt_b with ⟨x1, ⟨x1pos, hx1⟩⟩
  rcases HAHAHA_of_lt hb hc b_lt_c with ⟨x2, ⟨x2pos, hx2⟩⟩
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
  rcases HAHAHA_of_lt ha hb a_lt_b with ⟨x1, ⟨x1pos, hx1⟩⟩
  calc
  _= (VEC_nd A B).toDir := by rfl
  _= (Dl.toDir.unitVecND).toDir := by
    apply VecND.toDir_eq_toDir_iff.mpr
    unfold VecND.SameDir
    use x1; simp only [ne_eq, VecND.coe_mkPtPt, Dir.coe_unitVecND, hx1, and_true, x1pos]
  _=_ := by simp only [Dir.unitVecND_toDir]

theorem neg_toDir_of_gt {Dl : DirLine P} {A B : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (a_gt_b : lelem A ha > lelem B hb) : (RAY A B ((ne_iff_ne_as_line_elem ha hb).mpr (ne_of_gt a_gt_b)).symm).toDir = - Dl.toDir := by
  haveI B_ne_A : PtNe B A := ⟨((ne_iff_ne_as_line_elem ha hb).mpr (ne_of_gt a_gt_b)).symm⟩
  rcases HAHAHA_of_lt hb ha a_gt_b with ⟨x1, ⟨x1pos, hx1⟩⟩
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
  rcases HAHAHA_of_lt ha hb a_lt_b with ⟨x1, ⟨x1pos, hx1⟩⟩
  apply Ray.lies_int_iff.mpr
  use x1
  constructor
  · exact x1pos
  · have : (RAY A C).toDir = Dl.toDir := eq_toDir_of_lt ha hc a_lt_c
    simp only [this]
    exact hx1

theorem lies_int_ray_of_gt_and_gt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_gt_b : lelem A ha > lelem B hb) (a_gt_c : lelem A ha > lelem C hc) : B LiesInt (RAY A C ((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm):= by
  haveI : PtNe C A := ⟨((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm⟩
  rcases HAHAHA_of_lt hb ha a_gt_b with ⟨x1, ⟨x1pos, hx1⟩⟩
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
  rcases HAHAHA_of_le ha hb a_le_b with ⟨x1, ⟨x1nneg, hx1⟩⟩
  apply Ray.lies_on_iff.mpr
  use x1
  constructor
  · exact x1nneg
  · have : (RAY A C).toDir = Dl.toDir := eq_toDir_of_lt ha hc a_lt_c
    simp only [this]
    exact hx1

theorem lies_on_ray_of_ge_and_gt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_ge_b : lelem A ha ≥ lelem B hb) (a_gt_c : lelem A ha > lelem C hc) : B LiesOn (RAY A C ((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm):= by
  haveI : PtNe C A := ⟨((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm⟩
  rcases HAHAHA_of_le hb ha a_ge_b with ⟨x1, ⟨x1nneg, hx1⟩⟩
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

-- linear order and LiesInt Seg.extension
theorem lies_int_seg_ext_of_lt_and_lt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_lt_c : lelem A ha < lelem C hc) (c_lt_b : lelem C hc < lelem B hb) : B LiesInt (SEG_nd A C ((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_lt a_lt_c)).symm).extension := by
  haveI C_ne_A : PtNe C A := ⟨((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_lt a_lt_c)).symm⟩
  rcases HAHAHA_of_lt hc hb c_lt_b with ⟨x2, ⟨x2pos, hx2⟩⟩
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

theorem lies_int_seg_ext_of_gt_and_gt {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_gt_c : lelem A ha > lelem C hc) (c_gt_b : lelem C hc > lelem B hb) : B LiesInt (SEG_nd A C ((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm).extension := by
  haveI C_ne_A : PtNe C A := ⟨((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm⟩
  rcases HAHAHA_of_lt hb hc c_gt_b with ⟨x2, ⟨x2pos, hx2⟩⟩
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

-- linear order and LiesOn Seg.extension
theorem lies_on_seg_ext_of_lt_and_le {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_lt_c : lelem A ha < lelem C hc) (c_le_b : lelem C hc ≤ lelem B hb) : B LiesOn (SEG_nd A C ((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_lt a_lt_c)).symm).extension := by
  haveI C_ne_A : PtNe C A := ⟨((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_lt a_lt_c)).symm⟩
  rcases HAHAHA_of_le hc hb c_le_b with ⟨x2, ⟨x2nneg, hx2⟩⟩
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

theorem lies_on_seg_ext_of_gt_and_ge {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (a_gt_c : lelem A ha > lelem C hc) (c_ge_b : lelem C hc ≥ lelem B hb) : B LiesOn (SEG_nd A C ((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm).extension := by
  haveI C_ne_A : PtNe C A := ⟨((ne_iff_ne_as_line_elem ha hc).mpr (ne_of_gt a_gt_c)).symm⟩
  rcases HAHAHA_of_le hb hc c_ge_b with ⟨x2, ⟨x2nneg, hx2⟩⟩
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
theorem HOHOHO_of_lies_int_seg_and_le {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (hac : B LiesInt (SEG A C)) (a_le_c : lelem A ha ≤ lelem C hc) : ((lelem A ha) < (lelem B hb)) ∧ ((lelem B hb) < (lelem C hc)) := by
  have a_ne_c : A ≠ C := by
    by_contra h'
    simp only [h'] at hac
    have : C ≠ C := by exact (Seg.lies_int_iff.mp hac).1
    contradiction
  have : lelem A ha ≠ lelem C hc := by
    simp only [ne_eq, Subtype.mk.injEq, a_ne_c, not_false_eq_true]
  have : lelem A ha < lelem C hc := by
    apply lt_of_le_of_ne a_le_c this
  rcases (HAHAHA_of_lt ha hc this) with ⟨x1, ⟨x1pos, hx1⟩⟩
  rcases (Seg.lies_int_iff.mp hac) with ⟨_, ⟨x2, ⟨x2pos, ⟨x2lt1, hx2⟩⟩⟩⟩
  have : (SEG A C).toVec = (VEC A C) := by simp only [seg_toVec_eq_vec]
  simp only [this] at hx2
  constructor
  · apply lt_of_HAHAHA ha hb
    use x2 * x1
    constructor
    · positivity
    · simp only [mul_smul, hx1.symm]
      exact hx2
  · apply lt_of_HAHAHA hb hc
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
    apply HOHOHO_of_lies_int_seg_and_le ha hb hc hac a_le_c
  · right
    have : lelem C hc < lelem B hb ∧ lelem B hb < lelem A ha := by
      apply HOHOHO_of_lies_int_seg_and_le hc hb ha _ c_le_a
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
theorem HOHOHO_of_lies_on_seg_and_le {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (hac : B LiesOn (SEG A C)) (a_le_c : lelem A ha ≤ lelem C hc) : ((lelem A ha) ≤ (lelem B hb)) ∧ ((lelem B hb) ≤ (lelem C hc)) := by
  rcases eq_or_ne B A with (heq | h1)
  simp only [heq, le_refl, a_le_c, and_self]
  rcases eq_or_ne B C with (heq | h2)
  simp only [heq, a_le_c, le_refl, and_self]
  have : B LiesInt (SEG A C) := by
    refine' ⟨hac, h1, h2⟩
  exact ⟨le_of_lt (HOHOHO_of_lies_int_seg_and_le ha hb hc this a_le_c).1, le_of_lt (HOHOHO_of_lies_int_seg_and_le ha hb hc this a_le_c).2⟩

theorem ord_of_lies_on_seg {Dl : DirLine P} {A B C : P} (ha : A LiesOn Dl) (hb : B LiesOn Dl) (hc : C LiesOn Dl) (h : B LiesOn (SEG A C)) : (lelem A ha ≤ lelem B hb ∧ lelem B hb ≤ lelem C hc) ∨ (lelem A ha ≥ lelem B hb ∧ lelem B hb ≥ lelem C hc) := by
  have : (lelem A ha ≤ lelem C hc) ∨ (lelem C hc ≤ lelem A ha) := le_total (lelem A ha) (lelem C hc)
  rcases this with (a_le_c | c_le_a)
  · left
    exact HOHOHO_of_lies_on_seg_and_le ha hb hc h a_le_c
  · right
    have : lelem C hc ≤ lelem B hb ∧ lelem B hb ≤ lelem A ha := by
      apply HOHOHO_of_lies_on_seg_and_le hc hb ha _ c_le_a
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

-- linear order and lies int ray
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
  · rintro h1; rcases HAHAHA_of_lt ha hc h1 with ⟨x3, ⟨x3pos, hx3⟩⟩
    apply lt_of_HAHAHA; use (x2 / x1) * x3
    constructor
    · positivity
    · symm;
      calc
      _= (x2 / x1) • (x3 • Dl.toDir.unitVec) := by apply mul_smul
      _= (x2 / x1) • (VEC A C) := by simp only [hx3]
      _= _ := by symm; exact h2
  · rintro h2; rcases HAHAHA_of_lt ha hb h2 with ⟨x3, ⟨x3pos, hx3⟩⟩
    apply lt_of_HAHAHA; use (x1 / x2) * x3
    constructor
    · positivity
    · symm;
      calc
      _= (x1 / x2) • (x3 • Dl.toDir.unitVec) := by apply mul_smul
      _= (x1 / x2) • (VEC A B) := by simp only [hx3]
      _= _ := by symm; exact h1

-- linear order and lies on ray
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

-- linear order and LiesInt Seg.ext
-- linear order and LiesOn Seg.ext
end linear_order
end DirLine

end EuclidGeom
