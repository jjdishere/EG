import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex

noncomputable section

namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

namespace Angle

section AngleValue

/- theorem when angle > 0, IsInt means lies left of start ray + right of end ray; when angle < 0, ...  -/

end AngleValue

section angle_sum

-- Can use congrArg @Ray.source P _) h to turn h into the sources of two terms being equal.
theorem source_eq_source_of_adj {ang₁ ang₂: Angle P} (h : ang₁.end_ray = ang₂.start_ray) : ang₁.start_ray.source = ang₂.end_ray.source := sorry

def sum_adj {ang₁ ang₂: Angle P} (h : ang₁.end_ray = ang₂.start_ray) : Angle P :=
  Angle.mk_two_ray_of_eq_source ang₁.start_ray ang₂.end_ray (source_eq_source_of_adj h)

theorem ang_eq_ang_add_ang_mod_pi_of_adj_ang (ang₁ ang₂ : Angle P) (h: ang₁.end_ray = ang₂.start_ray) : (sum_adj h).value = ang₁.value + ang₂.value := sorry
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

theorem add_value_eq_value_add_of_dir_eq (h : ang₁.dir₂ = ang₂.dir₁) : (ang₁ + ang₂).value = ang₁.value + ang₂.value := by
  show ang₂.dir₂ -ᵥ ang₁.dir₁ = ang₁.dir₂ -ᵥ ang₁.dir₁ + (ang₂.dir₂ -ᵥ ang₂.dir₁)
  rw [h, add_comm]
  exact (vsub_add_vsub_cancel ang₂.dir₂ ang₂.dir₁ ang₁.dir₁).symm

theorem add_dvalue_eq_dvalue_add_of_proj_eq (h : ang₁.proj₂ = ang₂.proj₁) : (ang₁ + ang₂).dvalue = ang₁.dvalue + ang₂.dvalue := by
  show ang₂.proj₂ -ᵥ ang₁.proj₁ = ang₁.proj₂ -ᵥ ang₁.proj₁ + (ang₂.proj₂ -ᵥ ang₂.proj₁)
  rw [h, add_comm]
  exact (vsub_add_vsub_cancel ang₂.proj₂ ang₂.proj₁ ang₁.proj₁).symm

theorem add_value_eq_value_add (O A B C : P) [PtNe A O] [PtNe B O] [PtNe C O] : ∠ A O B = ∠ A O C + ∠ C O B :=
  @add_value_eq_value_add_of_dir_eq P _ (ANG A O C) (ANG C O B) rfl

theorem add_dvalue_eq_dvalue_add (O A B C : P) [PtNe A O] [PtNe B O] [PtNe C O] : ∡ A O B = ∡ A O C + ∡ C O B :=
  @add_dvalue_eq_dvalue_add_of_proj_eq P _ (ANG A O C) (ANG C O B) rfl

theorem sub_value_eq_value_sub_right (O A B C : P) [PtNe A O] [PtNe B O] [PtNe C O] : ∠ A O B = ∠ A O C - ∠ B O C :=
  eq_sub_of_add_eq (add_value_eq_value_add O A C B).symm

theorem sub_dvalue_eq_dvalue_sub_right (O A B C : P) [PtNe A O] [PtNe B O] [PtNe C O] : ∡ A O B = ∡ A O C - ∡ B O C :=
  eq_sub_of_add_eq (add_dvalue_eq_dvalue_add O A C B).symm

theorem sub_value_eq_value_sub_left (O A B C : P) [PtNe A O] [PtNe B O] [PtNe C O] : ∠ A O B = ∠ C O B - ∠ C O A :=
  eq_sub_of_add_eq' (add_value_eq_value_add O C B A).symm

theorem sub_dvalue_eq_dvalue_sub_left (O A B C : P) [PtNe A O] [PtNe B O] [PtNe C O] : ∡ A O B = ∡ C O B - ∡ C O A :=
  eq_sub_of_add_eq' (add_dvalue_eq_dvalue_add O C B A).symm

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

theorem dvalue_eq_pi_div_two_at_perp_foot {A B C : P} [_h : PtNe B C] (l : Line P) (hb : B LiesOn l) (ha : ¬ A LiesOn l) (hc : C = perp_foot A l) : haveI : PtNe A C := ⟨((pt_ne_iff_not_lies_on_of_eq_perp_foot hc).mpr ha).symm⟩; (ANG A C B).dvalue = ∡[π / 2] := by
  haveI : PtNe A C := ⟨((pt_ne_iff_not_lies_on_of_eq_perp_foot hc).mpr ha).symm⟩
  haveI : PtNe B (perp_foot A l) := by
    rw [← hc]
    exact _h
  apply line_pt_pt_perp_iff_dvalue_eq_pi_div_two.mp
  rw [Line.line_of_pt_pt_eq_rev]
  simp only [hc, Line.eq_line_of_pt_pt_of_ne (perp_foot_lies_on_line A l) hb]
  exact line_of_self_perp_foot_perp_line_of_not_lies_on ha

theorem perp_foot_lies_int_start_ray_iff_isAcu {A O B : P} [PtNe A O] [PtNe B O] : (perp_foot B (LIN O A)) LiesInt (RAY O A) ↔ (ANG A O B).IsAcu := sorry

theorem perp_foot_lies_int_start_ray_iff_isAcu_of_lies_int_end_ray {A : P} (ha : A LiesInt ang.end_ray) : perp_foot A ang.start_ray LiesInt ang.start_ray ↔ ang.IsAcu := sorry

theorem perp_foot_eq_source_iff_isRight {A O B : P} [PtNe A O] [PtNe B O] : (perp_foot B (LIN O A)) = O ↔ (ANG A O B).IsRight := sorry

theorem perp_foot_eq_source__iff_isRight_of_lies_int_end_ray {A : P} (ha : A LiesInt ang.end_ray) : perp_foot A ang.start_ray = ang.source ↔ ang.IsRight := sorry

theorem perp_foot_lies_int_start_ray_reverse_iff_isObt {A O B : P} [PtNe A O] [PtNe B O] : (perp_foot B (LIN O A)) LiesInt (RAY O A).reverse ↔ (ANG A O B).IsObt := sorry

theorem perp_foot_lies_int_start_ray_reverse_iff_isObt_of_lies_int_end_ray {A : P} (ha : A LiesInt ang.end_ray) : perp_foot A ang.start_ray.reverse LiesInt ang.start_ray ↔ ang.IsObt := sorry

end perp_foot

end Angle

/- If there exists a point on a line lying on an angle, then the line must intersect at least
one side of the angle. -/

end EuclidGeom
