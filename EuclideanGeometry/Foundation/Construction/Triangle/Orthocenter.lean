import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
/-!

-/
noncomputable section
namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

-- defining three heights
def Height_Line₁ (tr : TriangleND P) : Line P :=
  perp_line tr.1.1 (LIN tr.1.2 tr.1.3)

def Height_Line₂ (tr : TriangleND P) : Line P :=
  perp_line tr.1.2 (LIN tr.1.3 tr.1.1)

def Height_Line₃ (tr : TriangleND P) : Line P :=
  perp_line tr.1.3 (LIN tr.1.1 tr.1.2)

-- defining orthocenter via inner product
structure Is_Orthocenter (tr : TriangleND P) (H : P) : Prop where
  perp1 : inner (VEC tr.1.1 H) (VEC tr.1.2 tr.1.3) = (0 : ℝ)
  perp2 : inner (VEC tr.1.2 H) (VEC tr.1.3 tr.1.1) = (0 : ℝ)
  perp3 : inner (VEC tr.1.3 H) (VEC tr.1.1 tr.1.2) = (0 : ℝ)

-- a point satisfying any two conditions in the above definition is bound to satisfy the third one. This is particularly handy in proving three heights intersect in one point.
theorem orthocenter_exists (tr : TriangleND P) (H : P)
  (h₁ : inner (VEC tr.point₁ H) (VEC tr.point₂ tr.point₃) = (0 : ℝ))
  (h₂ : inner (VEC tr.point₂ H) (VEC tr.point₃ tr.point₁) = (0 : ℝ))
  : inner (VEC tr.point₃ H) (VEC tr.point₁ tr.point₂) = (0 : ℝ) := by
  set A := tr.point₁
  set B := tr.point₂
  set C := tr.point₃
  rw [← vec_sub_vec C, inner_sub_left, sub_eq_zero] at h₁ h₂
  rw [← vec_sub_vec C A B, inner_sub_right, sub_eq_zero, ← neg_vec B C, inner_neg_right, h₁, h₂, real_inner_comm, ← inner_neg_left, neg_vec]

/-in the following section, we will prove that:
  1: three heights intersect in one point, i.e. the intersection of two heights lies on the third one.
  2: such intersection satisfies our definition above, i.e. the intersection is indeed an orthocenter.
  3: orthocenter is unique for every triangle.
  by such, we can state that the orthocenter we constructed is exactly the orthocenter we want.-/

-- for the first goal, we need to start by giving the intersection of two heights. Therefore need to prove that any two heights in a regular triangle do intersect.

-- associating directions of lines with thoes of vectors'
lemma proj_eq_for_line_and_vec (A B : P) (h : B ≠ A) :
  toProj (LIN A B h) = (VEC_nd A B h) := by rfl

-- two lines in a non-degenerated triangle are not parallel
theorem not_para_if_nd (tr : TriangleND P) :
    ¬ LIN tr.1.1 tr.1.2 ∥ LIN tr.1.3 tr.1.1 := by
  let AB := LIN tr.1.1 tr.1.2
  let CA := LIN tr.1.3 tr.1.1
  show ¬ toProj AB = toProj CA
  by_contra h1
  have h2 : ¬ Collinear tr.1.1 tr.1.2 tr.1.3 := tr.2
  have h3 := ne_of_not_collinear h2
  have h4 : ¬ ((tr.1.3 = tr.1.2) ∨ (tr.1.1 = tr.1.3) ∨ (tr.1.2 = tr.1.1)) := by tauto
  contrapose! h2
  dsimp [Collinear]; rw [dif_neg h4]; dsimp [collinear_of_nd]
  have hab : toProj AB = (VEC_nd tr.1.1 tr.1.2).toProj := proj_eq_for_line_and_vec tr.1.1 tr.1.2 h3.2.2
  have hca : toProj CA = (VEC_nd tr.1.3 tr.1.1).toProj := proj_eq_for_line_and_vec tr.1.3 tr.1.1 h3.2.1
  have : (VEC_nd tr.1.1 tr.1.3).toProj = (VEC_nd tr.1.3 tr.1.1).toProj := by
    rw [VecND.toProj_eq_toProj_iff₀]; use -1
    rw [← VecND.neg_vecND, RayVector.coe_neg]; simp
  rw [hab, hca, ← this] at h1
  exact h1

theorem two_perp_not_para
  (l₁ l₂ l₃ l₄ : Line P) (h₁ : ¬ (l₁ ∥ l₂)) (h₂ : l₃ ⟂ l₁) (h₃ : l₄ ⟂ l₂) :
    ¬ (l₃ ∥ l₄) := by
  by_contra h
  have := h₂.symm
  have := perp_of_perp_parallel this h
  have := parallel_of_perp_perp this h₃
  contradiction

-- two heights in a regular triangle are not parallel
theorem Height₁₂_not_para (tr : TriangleND P) :
    ¬(Height_Line₁ tr ∥ Height_Line₂ tr) := by
  apply two_perp_not_para (LIN tr.1.2 tr.1.3) (LIN tr.1.1 tr.1.3)
  · have : (LIN tr.1.2 tr.1.3) = (LIN tr.1.3 tr.1.2) := by apply Line.line_of_pt_pt_eq_rev
    rw[this]
    apply not_para_if_nd (tr.flip_vertices.perm_vertices)
  · apply perp_line_perp tr.1.1
  · have : (LIN tr.1.1 tr.1.3) = (LIN tr.1.3 tr.1.1) := Line.line_of_pt_pt_eq_rev
    rw [this]; unfold Height_Line₂
    apply perp_line_perp tr.1.2

theorem Height₂₃_not_para (tr : TriangleND P) :
    ¬(Height_Line₂ tr ∥ Height_Line₃ tr) := by
  apply Height₁₂_not_para tr.perm_vertices

-- now we construct a orthocenter by its traditional meaning, that is, intersection of heights. Apparently we can only state an intersection of two heights now, but we will get to the third height later.
def Orthocenter (tr : TriangleND P) := (Line.inx (Height_Line₁ tr) (Height_Line₂ tr) (Height₁₂_not_para tr))

def aux_inter_is_Orthocenter (tr : TriangleND P) :
    ⟪VEC tr.1.1 (Orthocenter tr), VEC tr.1.2 tr.1.3⟫_ℝ = 0 := by
  -- the following code is illy wrote, I haven't found a better alteration
  have ocenter_lies_on_h1: Orthocenter tr LiesOn Height_Line₁ tr :=
    Line.inx_lies_on_fst (Height₁₂_not_para tr)
  have tr1_lieson_h1 : tr.1.1 LiesOn Height_Line₁ tr := by
    unfold Height_Line₁ perp_line; apply Line.pt_lies_on_of_mk_pt_proj
  -- to prove ⟪VEC tr.1.1 (Orthocenter tr), VEC tr.1.2 tr.1.3⟫_ℝ = 0, we either show that one vector is zero, or prove perpendicularity of two vectors
  by_cases eq : Orthocenter tr = tr.1.1
  · rw [eq, eq_iff_vec_eq_zero.1, inner_zero_left]; rfl
  · have : (VEC_nd tr.1.1 (Orthocenter tr) eq) ⟂ (VEC_nd tr.1.2 tr.1.3) := by
      have : PtNe tr.1.1 (Orthocenter tr) := by
        push_neg at eq; exact { out := id (Ne.symm eq) }
      have line_eq_height : (LIN tr.1.1 (Orthocenter tr) eq) = (Height_Line₁ tr) :=
        (Line.eq_of_pt_pt_lies_on_of_ne
          (tr1_lieson_h1) (ocenter_lies_on_h1)
          (Line.fst_pt_lies_on_mk_pt_pt) (Line.snd_pt_lies_on_mk_pt_pt)).symm
      have vec1_eq_line1:
        (VEC_nd tr.1.1 (Orthocenter tr) eq) = toProj (Height_Line₁ tr) := by
        rw [← proj_eq_for_line_and_vec tr.1.1 (Orthocenter tr) eq, line_eq_height]
      rw [VecND.toDir_toProj] at vec1_eq_line1
      exact vec1_eq_line1
    apply (inner_product_eq_zero_of_perp
      (VEC_nd tr.1.1 (Orthocenter tr) eq) (VEC_nd tr.1.2 tr.1.3) this)

def aux_inter_is_Orthocenter_perm (tr : TriangleND P) : ⟪VEC tr.1.2 (Orthocenter tr), VEC tr.1.3 tr.1.1⟫_ℝ = 0 := by
  have ocenter_lies_on_h2: Orthocenter tr LiesOn Height_Line₂ tr :=
    Line.inx_lies_on_snd (Height₁₂_not_para tr)
  have tr2_lieson_h2 : tr.1.2 LiesOn Height_Line₂ tr := by
    unfold Height_Line₂ perp_line; apply Line.pt_lies_on_of_mk_pt_proj
  by_cases eq : Orthocenter tr = tr.1.2
  · rw [eq, eq_iff_vec_eq_zero.1, inner_zero_left]; rfl
  · have : (VEC_nd tr.1.2 (Orthocenter tr) eq) ⟂ (VEC_nd tr.1.3 tr.1.1) := by
      have : PtNe tr.1.2 (Orthocenter tr) := by
        push_neg at eq; exact { out := id (Ne.symm eq) }
      have line_eq_height : (LIN tr.1.2 (Orthocenter tr) eq) = (Height_Line₂ tr) :=
        (Line.eq_of_pt_pt_lies_on_of_ne
          (tr2_lieson_h2) (ocenter_lies_on_h2)
          (Line.fst_pt_lies_on_mk_pt_pt) (Line.snd_pt_lies_on_mk_pt_pt)).symm
      have vec2_eq_line2:
        (VEC_nd tr.1.2 (Orthocenter tr) eq) = toProj (Height_Line₂ tr) := by
        rw [← proj_eq_for_line_and_vec tr.1.2 (Orthocenter tr) eq, line_eq_height]
      rw [VecND.toDir_toProj] at vec2_eq_line2
      exact vec2_eq_line2
    apply (inner_product_eq_zero_of_perp
      (VEC_nd tr.1.2 (Orthocenter tr) eq) (VEC_nd tr.1.3 tr.1.1) this)
-- "aux_inter_is_Orthocenter" and "aux_inter_is_Orthocenter_perm" are almost identical. This is annoying. perm_vertices can't be applied here since we haven't prove that orthocenter remains still under permutation.

-- now we prove that the intersection of two heights is an orthocenter as defined early
def inter_is_Orthocenter (tr : TriangleND P) : Is_Orthocenter tr $ Orthocenter tr where
  perp1 := aux_inter_is_Orthocenter tr
  perp2 := aux_inter_is_Orthocenter_perm tr
  perp3 := by
      by_cases eq : Orthocenter tr = tr.1.3
      · rw [eq, eq_iff_vec_eq_zero.1, inner_zero_left]; rfl
      · apply orthocenter_exists tr (Orthocenter tr) (aux_inter_is_Orthocenter tr) (aux_inter_is_Orthocenter_perm tr)

-- we then prove that such orthocenter is the intersection of all three heights
lemma lies_on_perp
  (p₁ p₂ : P) (l₁ : Line P) (nd : p₁ ≠ p₂) (vert : (LIN p₁ p₂ nd.symm) ⟂ l₁) :
    p₂ LiesOn perp_line p₁ l₁ := by
  unfold perp_line; unfold Perpendicular at vert
  have : l₁.toProj.perp = (toProj l₁).perp := rfl
  rw [this, ← vert]
  have : Line.mk_pt_proj p₁ (toProj (LIN p₁ p₂ nd.symm)) = LIN p₁ p₂ nd.symm := rfl
  rw [this]
  have : PtNe p₂ p₁ := by exact { out := id (Ne.symm nd) }
  apply Line.snd_pt_lies_on_mk_pt_pt

theorem Orthocenter_on_all_height (tr : TriangleND P) :
  Orthocenter tr LiesOn (Height_Line₁ tr) ∧
  Orthocenter tr LiesOn (Height_Line₂ tr) ∧
  Orthocenter tr LiesOn (Height_Line₃ tr) := by
  constructor
  · exact Line.inx_lies_on_fst (Height₁₂_not_para tr)
  · constructor
    · exact Line.inx_lies_on_snd (Height₁₂_not_para tr)
    · by_cases eq : Orthocenter tr = tr.1.3
      · rw [eq]; unfold Height_Line₃ perp_line
        apply Line.pt_lies_on_of_mk_pt_proj
      · have :
        (LIN tr.1.3 (Orthocenter tr) eq) ⟂ (LIN tr.1.1 tr.1.2) :=
          perp_of_inner_product_eq_zero
            (VEC_nd tr.1.3 (Orthocenter tr) eq) (VEC_nd tr.1.1 tr.1.2)
            (inter_is_Orthocenter tr).perp3
        unfold Height_Line₃
        apply lies_on_perp tr.1.3 (Orthocenter tr) (LIN tr.1.1 tr.1.2) (Ne.symm eq) this

-- then we prove certain properties orthocenter has.

-- orthocenter remains still under permutation
theorem perm_orthocenter {tr : TriangleND P} :
    Orthocenter tr.perm_vertices = Orthocenter tr := sorry

-- the uniqueness of orthocenter
theorem Orthocenter_iff_Is_Orthocenter (tr : TriangleND P) (H : P) :
  Is_Orthocenter tr H ↔ H = Orthocenter tr := sorry

end EuclidGeom
