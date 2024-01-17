import EuclideanGeometry.Foundation.Axiom.Position.Angle

/-!
# Constructions of an angle

This document discusses the construction of an angle, their properties, and the relationships between them.

-/

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Angle

section opposite

variable {ang ang₁ ang₂ : Angle P}

@[pp_dot]
def oppo (ang : Angle P) : (Angle P) where
  source := ang.source
  dir₁ := - ang.dir₁
  dir₂ := - ang.dir₂

@[simp]
theorem oppo_source : ang.oppo.source = ang.source := rfl

@[simp]
theorem oppo_dir₁ : ang.oppo.dir₁ = - ang.dir₁ := rfl

@[simp]
theorem oppo_dir₂ : ang.oppo.dir₂ = - ang.dir₂ := rfl

@[simp]
theorem oppo_proj₁ : ang.oppo.proj₁ = ang.proj₁ :=
  ang.dir₁.toProj_neg

@[simp]
theorem oppo_proj₂ : ang.oppo.proj₂ = ang.proj₂ :=
  ang.dir₂.toProj_neg

@[simp]
theorem oppo_value_eq_value : ang.oppo.value = ang.value :=
  value_eq_of_dir_eq_neg_dir rfl rfl

@[simp]
theorem oppo_dvalue_eq_dvalue : ang.oppo.dvalue = ang.dvalue :=
  dvalue_eq_of_dir_eq_neg_dir rfl rfl

@[simp]
theorem oppo_isPos_iff_isPos : ang.oppo.IsPos ↔ ang.IsPos := sorry

@[simp]
theorem oppo_isNeg_iff_isNeg : ang.oppo.IsNeg ↔ ang.IsNeg := sorry

@[simp]
theorem oppo_isND_iff_isND : ang.oppo.IsND ↔ ang.IsND := sorry

@[simp]
theorem oppo_isAcu_iff_isAcu : ang.oppo.IsAcu ↔ ang.IsAcu := sorry

@[simp]
theorem oppo_isObt_iff_isObt : ang.oppo.IsObt ↔ ang.IsObt := sorry

@[simp]
theorem oppo_isRight_iff_isRight : ang.oppo.IsRight ↔ ang.IsRight := sorry

theorem oppo_start_ray : ang.oppo.start_ray = ang.start_ray.reverse := sorry

theorem oppo_end_ray : ang.oppo.end_ray = ang.end_ray.reverse := sorry

theorem oppo_start_dirLine : ang.oppo.start_dirLine = ang.start_dirLine.reverse := sorry

theorem oppo_end_dirLine : ang.oppo.end_dirLine = ang.end_dirLine.reverse := sorry

@[simp]
theorem oppo_oppo_eq_self : ang.oppo.oppo = ang := sorry

@[pp_dot]
def IsOppo (ang₁ ang₂ : Angle P) : Prop := ang₁ = ang₂.oppo

theorem IsOppo.symm (h : ang₁.IsOppo ang₂) : ang₂.IsOppo ang₁ := sorry

theorem value_eq_of_isOppo (h : ang₁.IsOppo ang₂) : ang₁.value = ang₂.value := sorry

theorem dir₂_eq_neg_dir₂_of_value_eq_of_dir₁_eq_neg_dir₁ (hd : ang₁.dir₁ = - ang₂.dir₁) (hv : ang₁.value = ang₂.value) : ang₁.dir₂ = - ang₂.dir₂ := sorry

theorem dir₁_eq_neg_dir₁_of_value_eq_of_dir₂_eq_neg_dir₂ (hd : ang₁.dir₂ = - ang₂.dir₂) (hv : ang₁.value = ang₂.value) : ang₁.dir₁ = - ang₂.dir₁ := sorry

theorem isOppo_of_value_eq_of_dir₁_eq_neg_dir₁_of_source_eq (hs : ang₁.source = ang₂.source) (hd : ang₁.dir₁ = - ang₂.dir₁) (hv : ang₁.value = ang₂.value) : ang₁.IsOppo ang₂ := sorry

theorem isOppo_of_value_eq_of_dir₂_eq_neg_dir₂_of_source_eq (hs : ang₁.source = ang₂.source) (hd : ang₁.dir₂ = - ang₂.dir₂) (hv : ang₁.value = ang₂.value) : ang₁.IsOppo ang₂ := sorry

end opposite

section supplementary

variable {ang ang₁ ang₂: Angle P}

@[pp_dot]
def suppl (ang : Angle P) : Angle P where
  source := ang.source
  dir₁ := ang.dir₂
  dir₂ := - ang.dir₁

@[simp]
theorem suppl_source : ang.suppl.source = ang.source := rfl

@[simp]
theorem suppl_dir₁ : ang.suppl.dir₁ = ang.dir₂ := rfl

@[simp]
theorem suppl_dir₂ : ang.suppl.dir₂ = - ang.dir₁ := rfl

@[simp]
theorem suppl_proj₁ : ang.suppl.proj₁ = ang.proj₂ := rfl

@[simp]
theorem suppl_proj₂ : ang.suppl.proj₂ = ang.proj₁ := ang.dir₁.toProj_neg

@[simp]
theorem suppl_value_add_value_eq_pi : ang.suppl.value + ang.value = π := sorry

@[simp]
theorem suppl_dvalue_eq_neg_dvalue : ang.suppl.dvalue = - ang.dvalue := sorry

@[simp]
theorem suppl_isPos_iff_isPos : ang.suppl.IsPos ↔ ang.IsPos := sorry

@[simp]
theorem suppl_isNeg_iff_isNeg : ang.suppl.IsNeg ↔ ang.IsNeg := sorry

@[simp]
theorem suppl_isND_iff_isND : ang.suppl.IsND ↔ ang.IsND := by sorry

@[simp]
theorem suppl_isAcu_iff_isObt : ang.suppl.IsAcu ↔ ang.IsObt := by sorry

@[simp]
theorem suppl_isObt_iff_isAcu : ang.suppl.IsObt ↔ ang.IsAcu := by sorry

@[simp]
theorem suppl_isRight_iff_isRight : ang.suppl.IsRight ↔ ang.IsRight := by sorry

theorem suppl_start_ray : ang.suppl.start_ray = ang.end_ray := sorry

theorem suppl_end_ray : ang.suppl.end_ray = ang.start_ray.reverse := sorry

theorem suppl_start_dirLine : ang.suppl.start_dirLine = ang.end_dirLine := sorry

theorem suppl_end_dirLine : ang.suppl.end_dirLine = ang.start_dirLine.reverse := sorry

theorem suppl_suppl_eq_oppo : ang.suppl.suppl = ang.oppo := by sorry

theorem suppl_oppo_eq_oppo_suppl : ang.suppl.oppo = ang.oppo.suppl := rfl

@[pp_dot]
def IsSuppl (ang₁ ang₂ : Angle P) : Prop := ang₁ = ang₂.suppl

theorem value_add_value_eq_pi_of_isSuppl (h : ang₁.IsSuppl ang₂) : ang₁.value + ang₂.value = π := sorry

theorem dir_eq_neg_dir_of_value_add_eq_pi_of_dir_eq (hd : ang₁.dir₁ = ang₂.dir₂) (hv : ang₁.value + ang₂.value = π) : ang₁.dir₂ = - ang₂.dir₁ := sorry

theorem dir_eq_of_value_add_eq_pi_of_dir_eq_neg_dir (hd : ang₁.dir₂ = - ang₂.dir₁) (hv : ang₁.value + ang₂.value = π) : ang₁.dir₁ = ang₂.dir₂ := sorry

theorem isSuppl_of_value_add_eq_pi_of_dir_eq_of_source_eq (hs : ang₁.source = ang₂.source) (hd : ang₁.dir₁ = ang₂.dir₂) (hv : ang₁.value + ang₂.value = π) : ang₁.IsSuppl ang₂ := sorry

theorem isSuppl_of_value_add_eq_pi_of_dir_eq_neg_dir_of_source_eq (hs : ang₁.source = ang₂.source) (hd : ang₁.dir₂ = - ang₂.dir₁) (hv : ang₁.value + ang₂.value = π) : ang₁.IsSuppl ang₂ := sorry

end supplementary

section reverse

@[pp_dot]
def reverse (ang : Angle P) : Angle P where
  source := ang.source
  dir₁ := ang.dir₂
  dir₂ := ang.dir₁

variable {ang ang₁ ang₂ : Angle P}

@[simp]
theorem rev_source : ang.reverse.source = ang.source := rfl

@[simp]
theorem rev_dir₁ : ang.reverse.dir₁ = ang.dir₂ := rfl

@[simp]
theorem rev_dir₂ : ang.reverse.dir₂ = ang.dir₁ := rfl

@[simp]
theorem rev_proj₁ : ang.reverse.proj₁ = ang.proj₂ := rfl

@[simp]
theorem rev_proj₂ : ang.reverse.proj₂ = ang.proj₁ := rfl

theorem rev_value_eq_neg_value : ang.reverse.value = - ang.value :=
  (neg_vsub_eq_vsub_rev ang.reverse.dir₁ ang.reverse.dir₂).symm

theorem rev_dvalue_eq_neg_dvalue : ang.reverse.dvalue = - ang.dvalue :=
  (neg_vsub_eq_vsub_rev ang.reverse.proj₁ ang.reverse.proj₂).symm

@[simp]
theorem rev_isPos_iff_isNeg : ang.reverse.IsPos ↔ ang.IsNeg := sorry

@[simp]
theorem rev_isNeg_iff_isPos : ang.reverse.IsNeg ↔ ang.IsPos := sorry

@[simp]
theorem rev_isND_iff_isND : ang.reverse.IsND ↔ ang.IsND := by sorry

@[simp]
theorem rev_isAcu_iff_isAcu : ang.reverse.IsAcu ↔ ang.IsAcu := by sorry

@[simp]
theorem rev_isObt_iff_isObt : ang.reverse.IsObt ↔ ang.IsObt := by sorry

@[simp]
theorem rev_isRight_iff_isRight : ang.reverse.IsRight ↔ ang.IsRight := by sorry

theorem rev_start_ray : ang.reverse.start_ray = ang.start_ray.reverse := sorry

theorem rev_end_ray : ang.reverse.end_ray = ang.end_ray.reverse := sorry

theorem rev_start_dirLine : ang.reverse.start_dirLine = ang.start_dirLine.reverse := sorry

theorem rev_end_dirLine : ang.reverse.end_dirLine = ang.end_dirLine.reverse := sorry

@[simp]
theorem rev_rev_eq_self : ang.reverse.reverse = ang := sorry

theorem rev_suppl_oppo_eq_suppl_rev : ang.reverse.suppl.oppo = ang.suppl.reverse :=
  Angle.ext ang.reverse.suppl.oppo ang.suppl.reverse rfl rfl (neg_neg ang.dir₂)

theorem suppl_rev_oppo_eq_rev_suppl : ang.suppl.reverse.oppo = ang.reverse.suppl :=
  Angle.ext ang.suppl.reverse.oppo ang.reverse.suppl rfl (neg_neg ang.dir₁) rfl

theorem rev_oppo_eq_oppo_rev : ang.reverse.oppo = ang.oppo.reverse := rfl

@[pp_dot]
def IsReverse (ang₁ ang₂ : Angle P) : Prop := ang₁ = ang₂.reverse

theorem value_eq_neg_value_isReverse (h : ang₁.IsReverse ang₂) : ang₁.value = - ang₂.value := sorry
/-
theorem dir_eq_neg_dir_of_value_add_eq_pi_of_dir_eq (hd : ang₁.dir₁ = ang₂.dir₂) (hv : ang₁.value + ang₂.value = π) : ang₁.dir₂ = - ang₂.dir₁ := sorry

theorem dir_eq_of_value_add_eq_pi_of_dir_eq_neg_dir (hd : ang₁.dir₂ = - ang₂.dir₁) (hv : ang₁.value + ang₂.value = π) : ang₁.dir₁ = ang₂.dir₂ := sorry

theorem isSuppl_of_value_add_eq_pi_of_dir_eq_of_source_eq (hs : ang₁.source = ang₂.source) (hd : ang₁.dir₁ = ang₂.dir₂) (hv : ang₁.value + ang₂.value = π) : ang₁.IsSuppl ang₂ := sorry

theorem isSuppl_of_value_add_eq_pi_of_dir_eq_neg_dir_of_source_eq (hs : ang₁.source = ang₂.source) (hd : ang₁.dir₂ = - ang₂.dir₁) (hv : ang₁.value + ang₂.value = π) : ang₁.IsSuppl ang₂ := sorry
 -/
end reverse

end Angle



section parallel

variable {P : Type _} [EuclideanPlane P]
-- should be stated use mod 2pi first, then back to pi or -pi

structure IsCorrespondingAng (ang₁ ang₂ : Angle P) : Prop where
  start_ray : ang₁.dir₁ = ang₂.dir₁
  end_ray : ang₁.end_dirLine = ang₂.end_dirLine

structure IsConsecutiveIntAng (ang₁ ang₂ : Angle P) : Prop where
  start_ray : ang₁.dir₁ = ang₂.dir₁
  end_ray : ang₁.end_dirLine = ang₂.end_dirLine.reverse

structure IsAlternateIntAng (ang₁ ang₂ : Angle P) : Prop where
  start_ray : ang₁.dir₁ = - ang₂.dir₁
  end_ray : ang₁.end_dirLine = ang₂.end_dirLine.reverse

theorem IsCorrespondingAng.symm {ang₁ ang₂ : Angle P} (h : IsCorrespondingAng ang₁ ang₂) : IsCorrespondingAng ang₂ ang₁ := sorry

theorem IsConsecutiveIntAng.symm {ang₁ ang₂ : Angle P} (h : IsConsecutiveIntAng ang₁ ang₂) : IsConsecutiveIntAng ang₂ ang₁ := sorry

theorem IsAlternateIntAng.symm {ang₁ ang₂ : Angle P} (h : IsAlternateIntAng ang₁ ang₂) : IsAlternateIntAng ang₂ ang₁ := sorry

theorem value_eq_of_isCorrespondingAng {ang₁ ang₂ : Angle P} (h : IsCorrespondingAng ang₁ ang₂) : ang₁.value = ang₂.value := sorry

theorem value_sub_eq_pi_of_isConsecutiveIntAng {ang₁ ang₂ : Angle P} (h : IsConsecutiveIntAng ang₁ ang₂) : ang₁.value = ang₂.value + π := sorry --`first mod 2π, then discuss +-? `

theorem value_eq_of_isAlternateIntAng {ang₁ ang₂ : Angle P} (h : IsAlternateIntAng ang₁ ang₂) : ang₁.value = ang₂.value := sorry

/-
-- equivlently, this will be much more lengthy
theorem value_eq_of_corresponding_angle {l₁ l₂ l : DirLine P} (h : l₁.toDir = l₂.toDir) (g : ¬ l ∥ l₁) : (Angle.mk_dirline_dirline l₁ l (Ne.symm g)).value = (Angle.mk_dirline_dirline l₂ l (Ne.symm (ne_of_ne_of_eq g (Quotient.sound (h ▸ PM.con.refl _))))).value := sorry
-/

end parallel

end EuclidGeom
