import EuclideanGeometry.Foundation.Axiom.Position.Angle

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

end angle_sum

section angle_sub

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
