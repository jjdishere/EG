import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex

noncomputable section

namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

namespace Angle

section AngleValue

/- theorem when angle > 0, IsInt means lies left of start ray + right of end ray; when angle < 0, ...  -/

end AngleValue

section angle_sum

/-
@[pp_dot]
protected def add (ang₁ ang₂ : Angle P) (hs : ang₁.source = ang₂.source) (hd : ang₁.dir₂ = ang₂.dir₁) : Angle P where
  source := ang₁.source
  dir₁ := ang₁.dir₁
  dir₂ := ang₂.dir₂
 -/

instance instAddSemigroup : AddSemigroup (Angle P) where
  add ang₁ ang₂ := {
    source := ang₁.source
    dir₁ := ang₁.dir₁
    dir₂ := ang₂.dir₂
  }
  add_assoc _ _ _ := rfl

variable {ang₁ ang₂ : Angle P}

theorem add_source_eq_source_left : (ang₁ + ang₂).source = ang₁.source := rfl

theorem add_source_eq_source_right (h : ang₁.source = ang₂.source) : (ang₁ + ang₂).source = ang₂.source := h

@[simp]
theorem add_dir₁ : (ang₁ + ang₂).dir₁ = ang₁.dir₁ := rfl

@[simp]
theorem add_dir₂ : (ang₁ + ang₂).dir₂ = ang₂.dir₂ := rfl

@[simp]
theorem add_proj₁ : (ang₁ + ang₂).proj₁ = ang₁.proj₁ := rfl

@[simp]
theorem add_proj₂ : (ang₁ + ang₂).proj₂ = ang₂.proj₂ := rfl

@[simp]
theorem add_start_ray : (ang₁ + ang₂).start_ray = ang₁.start_ray := rfl

theorem add_end_ray (h : ang₁.source = ang₂.source) : (ang₁ + ang₂).end_ray = ang₂.end_ray :=
  (ang₁ + ang₂).end_ray.ext ang₂.end_ray h rfl

@[simp]
theorem add_start_dirLine : (ang₁ + ang₂).start_dirLine = ang₁.start_dirLine := rfl

theorem add_end_dirLine (h : ang₁.source = ang₂.source) : (ang₁ + ang₂).end_dirLine = ang₂.end_dirLine :=
  congrArg Ray.toDirLine (add_end_ray h)

theorem add_value_eq_value_add_of_dir_eq (h : ang₁.dir₂ = ang₂.dir₁) : (ang₁ + ang₂).value = ang₁.value + ang₂.value := by
  show ang₂.dir₂ -ᵥ ang₁.dir₁ = ang₁.dir₂ -ᵥ ang₁.dir₁ + (ang₂.dir₂ -ᵥ ang₂.dir₁)
  rw [h, add_comm]
  exact (vsub_add_vsub_cancel ang₂.dir₂ ang₂.dir₁ ang₁.dir₁).symm

theorem add_dvalue_eq_dvalue_add_of_proj_eq (h : ang₁.proj₂ = ang₂.proj₁) : (ang₁ + ang₂).dvalue = ang₁.dvalue + ang₂.dvalue := by
  show ang₂.proj₂ -ᵥ ang₁.proj₁ = ang₁.proj₂ -ᵥ ang₁.proj₁ + (ang₂.proj₂ -ᵥ ang₂.proj₁)
  rw [h, add_comm]
  exact (vsub_add_vsub_cancel ang₂.proj₂ ang₂.proj₁ ang₁.proj₁).symm

theorem value_add_eq_add_value (O A B C : P) [PtNe A O] [PtNe B O] [PtNe C O] : ∠ A O C + ∠ C O B = ∠ A O B :=
  (@add_value_eq_value_add_of_dir_eq P _ (ANG A O C) (ANG C O B) rfl).symm

theorem dvalue_add_eq_add_dvalue (O A B C : P) [PtNe A O] [PtNe B O] [PtNe C O] : ∡ A O C + ∡ C O B = ∡ A O B :=
  (@add_dvalue_eq_dvalue_add_of_proj_eq P _ (ANG A O C) (ANG C O B) rfl).symm

theorem value_sub_right_eq_sub_value (O A B C : P) [PtNe A O] [PtNe B O] [PtNe C O] : ∠ A O C - ∠ B O C = ∠ A O B :=
  sub_eq_of_eq_add (value_add_eq_add_value O A C B).symm

theorem dvalue_sub_right_eq_sub_dvalue (O A B C : P) [PtNe A O] [PtNe B O] [PtNe C O] : ∡ A O C - ∡ B O C = ∡ A O B :=
  sub_eq_of_eq_add (dvalue_add_eq_add_dvalue O A C B).symm

theorem value_sub_left_eq_sub_value (O A B C : P) [PtNe A O] [PtNe B O] [PtNe C O] : ∠ C O B - ∠ C O A = ∠ A O B :=
  (eq_sub_of_add_eq' (value_add_eq_add_value O C B A)).symm

theorem dvalue_sub_left_eq_sub_dvalue (O A B C : P) [PtNe A O] [PtNe B O] [PtNe C O] : ∡ C O B - ∡ C O A = ∡ A O B :=
  (eq_sub_of_add_eq' (dvalue_add_eq_add_dvalue O C B A)).symm

end angle_sum

section angle_sub

instance instSub : Sub (Angle P) where
  sub ang₁ ang₂ := {
    source := ang₁.source
    dir₁ := ang₁.dir₁
    dir₂ := ang₂.dir₁
  }

theorem sub_eq_add_rev (ang₁ ang₂ : Angle P) : ang₁ - ang₂ = ang₁ + ang₂.reverse := rfl

variable {ang₁ ang₂ : Angle P}

theorem sub_source_eq_source_left : (ang₁ - ang₂).source = ang₁.source := rfl

theorem sub_source_eq_source_right (h : ang₁.source = ang₂.source) : (ang₁ - ang₂).source = ang₂.source := h

@[simp]
theorem sub_dir₁ : (ang₁ - ang₂).dir₁ = ang₁.dir₁ := rfl

@[simp]
theorem sub_dir₂ : (ang₁ - ang₂).dir₂ = ang₂.dir₁ := rfl

@[simp]
theorem sub_proj₁ : (ang₁ - ang₂).proj₁ = ang₁.proj₁ := rfl

@[simp]
theorem sub_proj₂ : (ang₁ - ang₂).proj₂ = ang₂.proj₁ := rfl

@[simp]
theorem sub_start_ray : (ang₁ - ang₂).start_ray = ang₁.start_ray := rfl

theorem sub_end_ray (h : ang₁.source = ang₂.source) : (ang₁ - ang₂).end_ray = ang₂.start_ray :=
  (ang₁ - ang₂).end_ray.ext ang₂.start_ray h rfl

@[simp]
theorem sub_start_dirLine : (ang₁ - ang₂).start_dirLine = ang₁.start_dirLine := rfl

theorem sub_end_dirLine (h : ang₁.source = ang₂.source) : (ang₁ - ang₂).end_dirLine = ang₂.start_dirLine :=
  congrArg Ray.toDirLine (sub_end_ray h)

theorem sub_value_eq_value_sub_of_dir_eq (h : ang₁.dir₂ = ang₂.dir₂) : (ang₁ - ang₂).value = ang₁.value - ang₂.value := by
  show ang₂.dir₁ -ᵥ ang₁.dir₁ = ang₁.dir₂ -ᵥ ang₁.dir₁ - (ang₂.dir₂ -ᵥ ang₂.dir₁)
  rw [h]
  exact (vsub_sub_vsub_cancel_left ang₂.dir₁ ang₁.dir₁ ang₂.dir₂).symm

theorem sub_dvalue_eq_dvalue_sub_of_proj_eq (h : ang₁.proj₂ = ang₂.proj₂) : (ang₁ - ang₂).dvalue = ang₁.dvalue - ang₂.dvalue := by
  show ang₂.proj₁ -ᵥ ang₁.proj₁ = ang₁.proj₂ -ᵥ ang₁.proj₁ - (ang₂.proj₂ -ᵥ ang₂.proj₁)
  rw [h]
  exact (vsub_sub_vsub_cancel_left ang₂.proj₁ ang₁.proj₁ ang₂.proj₂).symm

end angle_sub

section perp_foot

variable {ang : Angle P}

theorem dvalue_eq_pi_div_two_at_perp_foot {A O B : P} [_h : PtNe A O] {l : Line P} (ha : A LiesOn l) (ho : O = perp_foot B l) (hb : ¬ B LiesOn l) : haveI : PtNe B O := ⟨((pt_ne_iff_not_lies_on_of_eq_perp_foot ho).mpr hb).symm⟩; ∡ A O B = ∡[π / 2] := by
  haveI _hbo : PtNe B O := ⟨((pt_ne_iff_not_lies_on_of_eq_perp_foot ho).mpr hb).symm⟩
  haveI : PtNe A (perp_foot B l) := by
    rw [← ho]
    exact _h
  apply line_pt_pt_perp_iff_dvalue_eq_pi_div_two.mp
  rw [Line.line_of_pt_pt_eq_rev (_h := _hbo)]
  simp only [ho, Line.eq_line_of_pt_pt_of_ne (perp_foot_lies_on_line B l) ha]
  exact (line_of_self_perp_foot_perp_line_of_not_lies_on hb).symm

theorem isRt_at_perp_foot {A O B : P} [_h : PtNe A O] {l : Line P} (ha : A LiesOn l) (ho : O = perp_foot B l) (hb : ¬ B LiesOn l) : haveI : PtNe B O := ⟨((pt_ne_iff_not_lies_on_of_eq_perp_foot ho).mpr hb).symm⟩; (ANG A O B).IsRt :=
  AngValue.isRt_iff_coe.mpr (dvalue_eq_pi_div_two_at_perp_foot ha ho hb)

theorem perp_foot_lies_int_start_ray_iff_isAcu {A O B : P} [PtNe A O] [PtNe B O] : (perp_foot B (LIN O A)) LiesInt (RAY O A) ↔ (ANG A O B).IsAcu := by
  refine' ((RAY O A).lies_int_iff_pos_of_vec_eq_smul_toDir
    (vec_pt_perp_foot_eq_ddist_smul_toDir_unitVec O B (@DirLine.fst_pt_lies_on_mk_pt_pt P _ O A _))).trans
      (Iff.trans _ (inner_pos_iff_isAcu A O B))
  show 0 < inner (VEC O B) (‖VEC O A‖⁻¹ • (VEC O A)) ↔ 0 < inner (VEC O A) (VEC O B)
  rw [real_inner_smul_right, real_inner_comm]
  exact mul_pos_iff_of_pos_left (inv_pos.mpr (VEC_nd O A).norm_pos)

theorem perp_foot_eq_source_iff_isRt {A O B : P} [PtNe A O] [PtNe B O] : (perp_foot B (LIN O A)) = O ↔ (ANG A O B).IsRt := by
  refine' ((RAY O A).eq_source_iff_eq_zero_of_vec_eq_smul_toDir
    (vec_pt_perp_foot_eq_ddist_smul_toDir_unitVec O B (@DirLine.fst_pt_lies_on_mk_pt_pt P _ O A _))).trans
      (Iff.trans _ (inner_eq_zero_iff_isRt A O B))
  show inner (VEC O B) (‖VEC O A‖⁻¹ • (VEC O A)) = 0 ↔ inner (VEC O A) (VEC O B) = 0
  rw [real_inner_smul_right, real_inner_comm]
  exact smul_eq_zero_iff_right (ne_of_gt (inv_pos.mpr (VEC_nd O A).norm_pos))

theorem perp_foot_lies_int_start_ray_reverse_iff_isObt {A O B : P} [PtNe A O] [PtNe B O] : (perp_foot B (LIN O A)) LiesInt (RAY O A).reverse ↔ (ANG A O B).IsObt := by
  refine' ((RAY O A).lies_int_rev_iff_neg_of_vec_eq_smul_toDir
    (vec_pt_perp_foot_eq_ddist_smul_toDir_unitVec O B (@DirLine.fst_pt_lies_on_mk_pt_pt P _ O A _))).trans
      (Iff.trans _ (inner_neg_iff_isObt A O B))
  show inner (VEC O B) (‖VEC O A‖⁻¹ • (VEC O A)) < 0 ↔ inner (VEC O A) (VEC O B) < 0
  rw [real_inner_smul_right, real_inner_comm]
  exact smul_neg_iff_of_pos_left (inv_pos.mpr (VEC_nd O A).norm_pos)

end perp_foot

end Angle

/- If there exists a point on a line lying on an angle, then the line must intersect at least
one side of the angle. -/

end EuclidGeom
