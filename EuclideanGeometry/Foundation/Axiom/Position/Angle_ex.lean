import EuclideanGeometry.Foundation.Axiom.Position.Angle

/-!
# Constructions of an angle

This document discusses the construction of an angle, their properties, and the relationships between them.

-/

noncomputable section

namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

namespace Angle

open AngValue

section opposite

variable {ang ang₁ ang₂ : Angle P}

@[pp_dot]
def oppo (ang : Angle P) : Angle P where
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
theorem oppo_isPos_iff_isPos : ang.oppo.IsPos ↔ ang.IsPos :=
  iff_of_eq (congrArg AngValue.IsPos ang.oppo_value_eq_value)

@[simp]
theorem oppo_isNeg_iff_isNeg : ang.oppo.IsNeg ↔ ang.IsNeg :=
  iff_of_eq (congrArg AngValue.IsNeg ang.oppo_value_eq_value)

@[simp]
theorem oppo_isND_iff_isND : ang.oppo.IsND ↔ ang.IsND :=
  iff_of_eq (congrArg AngValue.IsND ang.oppo_value_eq_value)

@[simp]
theorem oppo_isAcu_iff_isAcu : ang.oppo.IsAcu ↔ ang.IsAcu :=
  iff_of_eq (congrArg AngValue.IsAcu ang.oppo_value_eq_value)

@[simp]
theorem oppo_isObt_iff_isObt : ang.oppo.IsObt ↔ ang.IsObt :=
  iff_of_eq (congrArg AngValue.IsObt ang.oppo_value_eq_value)

@[simp]
theorem oppo_isRt_iff_isRt : ang.oppo.IsRt ↔ ang.IsRt :=
  iff_of_eq (congrArg AngValue.IsRt ang.oppo_value_eq_value)

theorem oppo_start_ray : ang.oppo.start_ray = ang.start_ray.reverse := rfl

theorem oppo_end_ray : ang.oppo.end_ray = ang.end_ray.reverse := rfl

theorem oppo_start_dirLine : ang.oppo.start_dirLine = ang.start_dirLine.reverse := rfl

theorem oppo_end_dirLine : ang.oppo.end_dirLine = ang.end_dirLine.reverse := rfl

@[simp]
theorem oppo_oppo_eq_self : ang.oppo.oppo = ang :=
  Angle.ext ang.oppo.oppo ang rfl (neg_neg ang.dir₁) (neg_neg ang.dir₂)

@[pp_dot]
def IsOppo (ang₁ ang₂ : Angle P) : Prop :=
  ang₁ = ang₂.oppo

theorem IsOppo.symm (h : ang₁.IsOppo ang₂) : ang₂.IsOppo ang₁ := by
  rw [h]
  exact (ang₂.oppo_oppo_eq_self).symm

theorem value_eq_of_isOppo (h : ang₁.IsOppo ang₂) : ang₁.value = ang₂.value := by
  rw [h]
  exact ang₂.oppo.value_eq_of_dir_eq_neg_dir rfl rfl

theorem dvalue_eq_of_isOppo (h : ang₁.IsOppo ang₂) : ang₁.dvalue = ang₂.dvalue := by
  rw [h]
  exact ang₂.oppo.dvalue_eq_of_dir_eq_neg_dir rfl rfl

theorem dir_eq_neg_dir_iff_of_value_eq (h : ang₁.value = ang₂.value) : ang₁.dir₁ = - ang₂.dir₁ ↔ ang₁.dir₂ = - ang₂.dir₂ := by
  apply (vadd_left_cancel_iff ang₁.value).symm.trans
  nth_rw 1 [value, vsub_vadd, h, Dir.vadd_neg, value, vsub_vadd]

theorem isOppo_of_value_eq_of_dir₁_eq_neg_dir₁_of_source_eq (hs : ang₁.source = ang₂.source) (hd : ang₁.dir₁ = - ang₂.dir₁) (hv : ang₁.value = ang₂.value) : ang₁.IsOppo ang₂ :=
  Angle.ext ang₁ ang₂.oppo hs hd ((dir_eq_neg_dir_iff_of_value_eq hv).mp hd)

theorem isOppo_of_value_eq_of_dir₂_eq_neg_dir₂_of_source_eq (hs : ang₁.source = ang₂.source) (hd : ang₁.dir₂ = - ang₂.dir₂) (hv : ang₁.value = ang₂.value) : ang₁.IsOppo ang₂ :=
  Angle.ext ang₁ ang₂.oppo hs ((dir_eq_neg_dir_iff_of_value_eq hv).mpr hd) hd

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
theorem suppl_value_add_value_eq_pi : ang.suppl.value + ang.value = π :=
  value_add_value_eq_pi_of_isSuppl' rfl rfl

@[simp]
theorem suppl_dvalue_eq_neg_dvalue : ang.suppl.dvalue = - ang.dvalue :=
  dvalue_eq_neg_dvalue_of_isSuppl' rfl rfl

@[simp]
theorem suppl_isPos_iff_isPos : ang.suppl.IsPos ↔ ang.IsPos :=
  isPos_iff_isPos_of_add_eq_pi ang.suppl_value_add_value_eq_pi

@[simp]
theorem suppl_isNeg_iff_isNeg : ang.suppl.IsNeg ↔ ang.IsNeg :=
  isNeg_iff_isNeg_of_add_eq_pi ang.suppl_value_add_value_eq_pi

@[simp]
theorem suppl_isND_iff_isND : ang.suppl.IsND ↔ ang.IsND :=
  isND_iff_isND_of_add_eq_pi ang.suppl_value_add_value_eq_pi

@[simp]
theorem suppl_isAcu_iff_isObt : ang.suppl.IsAcu ↔ ang.IsObt :=
  isAcu_iff_isObt_of_add_eq_pi ang.suppl_value_add_value_eq_pi

@[simp]
theorem suppl_isObt_iff_isAcu : ang.suppl.IsObt ↔ ang.IsAcu :=
  isObt_iff_isAcu_of_add_eq_pi ang.suppl_value_add_value_eq_pi

@[simp]
theorem suppl_isRt_iff_isRt : ang.suppl.IsRt ↔ ang.IsRt :=
  isRt_iff_isRt_of_add_eq_pi ang.suppl_value_add_value_eq_pi

theorem suppl_start_ray : ang.suppl.start_ray = ang.end_ray := rfl

theorem suppl_end_ray : ang.suppl.end_ray = ang.start_ray.reverse := rfl

theorem suppl_start_dirLine : ang.suppl.start_dirLine = ang.end_dirLine := rfl

theorem suppl_end_dirLine : ang.suppl.end_dirLine = ang.start_dirLine.reverse := rfl

theorem suppl_suppl_eq_oppo : ang.suppl.suppl = ang.oppo := rfl

theorem suppl_oppo_eq_oppo_suppl : ang.suppl.oppo = ang.oppo.suppl := rfl

@[pp_dot]
def IsSuppl (ang₁ ang₂ : Angle P) : Prop :=
  ang₁ = ang₂.suppl

theorem value_add_value_eq_pi_of_isSuppl (h : ang₁.IsSuppl ang₂) : ang₁.value + ang₂.value = π := by
  rw [h]
  exact ang₂.suppl_value_add_value_eq_pi

theorem dvalue_eq_neg_dvalue_of_isSuppl (h : ang₁.IsSuppl ang₂) : ang₁.dvalue = - ang₂.value := by
  rw [h]
  exact ang₂.suppl_dvalue_eq_neg_dvalue

theorem dir_eq_rev_dir_iff_of_value_add_eq_pi (h : ang₁.value + ang₂.value = π) : ang₁.dir₁ = ang₂.dir₂ ↔ ang₁.dir₂ = - ang₂.dir₁ := by
  have h : ang₁.dir₂ -ᵥ ang₁.dir₁ = ∠[Real.pi] - (ang₂.dir₂ -ᵥ ang₂.dir₁) := eq_sub_of_add_eq h
  apply (vadd_left_cancel_iff (ang₁.dir₂ -ᵥ ang₁.dir₁)).symm.trans
  rw [vsub_vadd, h, sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_vadd, vsub_vadd, Dir.pi_vadd]

theorem isSuppl_of_value_add_eq_pi_of_dir_eq_of_source_eq (hs : ang₁.source = ang₂.source) (hd : ang₁.dir₁ = ang₂.dir₂) (hv : ang₁.value + ang₂.value = π) : ang₁.IsSuppl ang₂ :=
  Angle.ext ang₁ ang₂.suppl hs hd ((dir_eq_rev_dir_iff_of_value_add_eq_pi hv).mp hd)

theorem isSuppl_of_value_add_eq_pi_of_dir_eq_neg_dir_of_source_eq (hs : ang₁.source = ang₂.source) (hd : ang₁.dir₂ = - ang₂.dir₁) (hv : ang₁.value + ang₂.value = π) : ang₁.IsSuppl ang₂ :=
  Angle.ext ang₁ ang₂.suppl hs ((dir_eq_rev_dir_iff_of_value_add_eq_pi hv).mpr hd) hd

end supplementary

section reverse

@[pp_dot]
def reverse (ang : Angle P) : Angle P where
  source := ang.source
  dir₁ := ang.dir₂
  dir₂ := ang.dir₁

instance instInvolutiveNeg : InvolutiveNeg (Angle P) where
  neg := reverse
  neg_neg _ := rfl

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
theorem rev_isPos_iff_isNeg : ang.reverse.IsPos ↔ ang.IsNeg := by
  unfold IsPos
  rw [rev_value_eq_neg_value]
  exact neg_isPos_iff_isNeg

@[simp]
theorem rev_isNeg_iff_isPos : ang.reverse.IsNeg ↔ ang.IsPos := by
  unfold IsNeg
  rw [rev_value_eq_neg_value]
  exact neg_isNeg_iff_isPos

@[simp]
theorem rev_isND_iff_isND : ang.reverse.IsND ↔ ang.IsND := by
  unfold IsND
  rw [rev_value_eq_neg_value]
  exact neg_isND_iff_isND

@[simp]
theorem rev_isAcu_iff_isAcu : ang.reverse.IsAcu ↔ ang.IsAcu := by
  unfold IsAcu
  rw [rev_value_eq_neg_value]
  exact neg_isAcu_iff_isAcu

@[simp]
theorem rev_isObt_iff_isObt : ang.reverse.IsObt ↔ ang.IsObt := by
  unfold IsObt
  rw [rev_value_eq_neg_value]
  exact neg_isObt_iff_isObt

@[simp]
theorem rev_isRt_iff_isRt : ang.reverse.IsRt ↔ ang.IsRt := by
  unfold IsRt
  rw [rev_value_eq_neg_value]
  exact neg_isRt_iff_isRt

theorem rev_start_ray : ang.reverse.start_ray = ang.end_ray := rfl

theorem rev_end_ray : ang.reverse.end_ray = ang.start_ray := rfl

theorem rev_start_dirLine : ang.reverse.start_dirLine = ang.end_dirLine := rfl

theorem rev_end_dirLine : ang.reverse.end_dirLine = ang.start_dirLine := rfl

@[simp]
theorem rev_rev_eq_self : ang.reverse.reverse = ang := rfl

theorem rev_suppl_oppo_eq_suppl_rev : ang.reverse.suppl.oppo = ang.suppl.reverse :=
  Angle.ext ang.reverse.suppl.oppo ang.suppl.reverse rfl rfl (neg_neg ang.dir₂)

theorem suppl_rev_oppo_eq_rev_suppl : ang.suppl.reverse.oppo = ang.reverse.suppl :=
  Angle.ext ang.suppl.reverse.oppo ang.reverse.suppl rfl (neg_neg ang.dir₁) rfl

theorem rev_oppo_eq_oppo_rev : ang.reverse.oppo = ang.oppo.reverse := rfl

@[pp_dot]
def IsReverse (ang₁ ang₂ : Angle P) : Prop :=
  ang₁ = ang₂.reverse

theorem value_eq_neg_value_isReverse (h : ang₁.IsReverse ang₂) : ang₁.value = - ang₂.value := by
  rw [h]
  exact ang₂.rev_value_eq_neg_value

theorem dvalue_eq_neg_dvalue_isReverse (h : ang₁.IsReverse ang₂) : ang₁.dvalue = - ang₂.dvalue := by
  rw [h]
  exact ang₂.rev_dvalue_eq_neg_dvalue

theorem dir_eq_rev_dir_iff_of_value_eq_neg_value (h : ang₁.value = - ang₂.value) : ang₁.dir₁ = ang₂.dir₂ ↔ ang₁.dir₂ = ang₂.dir₁ := by
  apply (vadd_left_cancel_iff ang₁.value).symm.trans
  nth_rw 1 [value, vsub_vadd, h, value, neg_vsub_eq_vsub_rev, vsub_vadd]

theorem isReverse_of_value_eq_neg_value_of_dir₁_eq_of_source_eq (hs : ang₁.source = ang₂.source) (hd : ang₁.dir₁ = ang₂.dir₂) (hv : ang₁.value = - ang₂.value) : ang₁.IsReverse ang₂ :=
  Angle.ext ang₁ ang₂.reverse hs hd ((dir_eq_rev_dir_iff_of_value_eq_neg_value hv).mp hd)

theorem isReverse_of_value_eq_neg_value_of_dir₂_eq_of_source_eq (hs : ang₁.source = ang₂.source) (hd : ang₁.dir₂ = ang₂.dir₁) (hv : ang₁.value = - ang₂.value) : ang₁.IsReverse ang₂ :=
  Angle.ext ang₁ ang₂.reverse hs ((dir_eq_rev_dir_iff_of_value_eq_neg_value hv).mpr hd) hd

end reverse

end Angle



open Angle

section Parallel

variable {P : Type*} [EuclideanPlane P]
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

attribute [pp_dot] IsCorrespondingAng.start_ray IsCorrespondingAng.end_ray
attribute [pp_dot] IsConsecutiveIntAng.start_ray IsConsecutiveIntAng.end_ray
attribute [pp_dot] IsAlternateIntAng.start_ray IsAlternateIntAng.end_ray

theorem IsCorrespondingAng.symm {ang₁ ang₂ : Angle P} (h : IsCorrespondingAng ang₁ ang₂) : IsCorrespondingAng ang₂ ang₁ :=
  ⟨h.1.symm, h.2.symm⟩

theorem IsConsecutiveIntAng.symm {ang₁ ang₂ : Angle P} (h : IsConsecutiveIntAng ang₁ ang₂) : IsConsecutiveIntAng ang₂ ang₁ :=
  ⟨h.1.symm, by
    rw [h.2]
    exact (ang₂.end_dirLine.rev_rev_eq_self).symm⟩

theorem IsAlternateIntAng.symm {ang₁ ang₂ : Angle P} (h : IsAlternateIntAng ang₁ ang₂) : IsAlternateIntAng ang₂ ang₁ :=
  ⟨(neg_eq_iff_eq_neg.mpr h.1).symm, by
    rw [h.2]
    exact (ang₂.end_dirLine.rev_rev_eq_self).symm⟩

theorem value_eq_of_isCorrespondingAng {ang₁ ang₂ : Angle P} (h : IsCorrespondingAng ang₁ ang₂) : ang₁.value = ang₂.value :=
  value_eq_of_dir_eq h.1 (congrArg DirLine.toDir h.2)

theorem dvalue_eq_of_isCorrespondingAng {ang₁ ang₂ : Angle P} (h : IsCorrespondingAng ang₁ ang₂) : ang₁.dvalue = ang₂.dvalue :=
  dvalue_eq_of_dir_eq h.1 (congrArg DirLine.toDir h.2)

theorem value_eq_value_add_pi_of_isConsecutiveIntAng {ang₁ ang₂ : Angle P} (h : IsConsecutiveIntAng ang₁ ang₂) : ang₁.value = ang₂.value + π :=
  value_eq_value_add_pi_of_dir_eq_neg_dir_of_dir_eq h.1 (congrArg DirLine.toDir h.2)

theorem dvalue_eq_of_isConsecutiveIntAng {ang₁ ang₂ : Angle P} (h : IsConsecutiveIntAng ang₁ ang₂) : ang₁.dvalue = ang₂.dvalue :=
  dvalue_eq_dvalue_of_dir_eq_neg_dir_of_dir_eq h.1 (congrArg DirLine.toDir h.2)

theorem value_eq_of_isAlternateIntAng {ang₁ ang₂ : Angle P} (h : IsAlternateIntAng ang₁ ang₂) : ang₁.value = ang₂.value :=
  value_eq_of_dir_eq_neg_dir h.1 (congrArg DirLine.toDir h.2)

theorem dvalue_eq_of_isAlternateIntAng {ang₁ ang₂ : Angle P} (h : IsAlternateIntAng ang₁ ang₂) : ang₁.dvalue = ang₂.dvalue :=
  dvalue_eq_of_dir_eq_neg_dir h.1 (congrArg DirLine.toDir h.2)

/-
-- equivlently, this will be much more lengthy
theorem value_eq_of_corresponding_angle {l₁ l₂ l : DirLine P} (h : l₁.toDir = l₂.toDir) (g : ¬ l ∥ l₁) : (Angle.mk_dirline_dirline l₁ l (Ne.symm g)).value = (Angle.mk_dirline_dirline l₂ l (Ne.symm (ne_of_ne_of_eq g (Quotient.sound (h ▸ PM.con.refl _))))).value := sorry
-/

end Parallel

end EuclidGeom
