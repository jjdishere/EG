import EuclideanGeometry.Foundation.Axiom.Position.Angle

/-!
# Constructions of an angle

This document discusses the construction of an angle, their properties, and the relationships between them.

-/

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Angle



-- Define the supplementary angle to be the angle
variable (ang : Angle P)

--Maybe the name is too long
@[pp_dot]
def suppl : Angle P where
  source := ang.source
  dir₁ := ang.dir₁
  dir₂ := - ang.dir₂

-- If two oriented angles share a same side, then they are supplementary oriented angles if and only if the sum of two angles is π or -π   `Do I use {ang1} or (ang1)?

theorem reverse_ray_iff_sum_of_angle_eq_pi {ang1 : Angle P} {ang2 : Angle P} (h: ang1.end_ray = ang2.start_ray) : ang1.end_ray = ang2.start_ray.reverse ↔ ang1.value + ang2.value = π ∨ ang1.value + ang2.value = -π := by sorry

theorem right_of_suppl_of_right (h : ang.IsRight) :  ang.suppl.IsRight := by sorry

theorem acute_of_suplp_of_obtuse (h : ang.IsObt) : ang.suppl.IsAcu := by sorry

theorem obtuse_of_suppl_of_acute (h : ang.IsAcu) : ang.suppl.IsObt := by sorry

theorem IsND_of_suppl_of_IsND (nontriv : ang.IsND) : ang.suppl.IsND := by sorry

@[pp_dot]
def oppo :(Angle P) where
  source := ang.source
  dir₁ := - ang.dir₁
  dir₂ := - ang.dir₂

theorem oppo_eq_supp_of_supp : ang.suppl.suppl = ang := by sorry

theorem IsND_of_oppo_of_IsND (nontriv : ang.IsND) : ang.oppo.IsND := by sorry

end Angle

section parallel
variable {P : Type _} [EuclideanPlane P]
-- should be stated use mod 2pi first, then back to pi or -pi

def IsOppoAng (ang₁ ang₂ : Angle P) : Prop := ang₁ = ang₂.oppo

structure IsCorrespondingAng (ang₁ ang₂ : Angle P) : Prop where
  start_ray : ang₁.dir₁ = ang₂.dir₁
  end_ray : ang₁.end_dirLine = ang₂.end_dirLine

structure IsConsecutiveIntAng (ang₁ ang₂ : Angle P) : Prop where
  start_ray : ang₁.dir₁ = ang₂.dir₁
  end_ray : ang₁.end_dirLine = ang₂.end_dirLine.reverse

structure IsAlternateIntAng (ang₁ ang₂ : Angle P) : Prop where
  start_ray : ang₁.dir₁ = - ang₂.dir₁
  end_ray : ang₁.end_dirLine = ang₂.end_dirLine.reverse

theorem IsOppoAng.symm {ang₁ ang₂ : Angle P} : IsOppoAng ang₁ ang₂ → IsOppoAng ang₂ ang₁ := sorry

theorem IsCorrespondingAng.symm {ang₁ ang₂ : Angle P} : IsCorrespondingAng ang₁ ang₂ → IsCorrespondingAng ang₂ ang₁ := sorry

theorem IsConsecutiveIntAng.symm {ang₁ ang₂ : Angle P} : IsConsecutiveIntAng ang₁ ang₂ → IsConsecutiveIntAng ang₂ ang₁ := sorry

theorem IsAlternateIntAng.symm {ang₁ ang₂ : Angle P} : IsAlternateIntAng ang₁ ang₂ → IsAlternateIntAng ang₂ ang₁ := sorry

theorem value_eq_of_isoppoang {ang₁ ang₂ : Angle P} (h : IsOppoAng ang₁ ang₂) : ang₁.value = ang₂.value := sorry

theorem value_eq_of_iscorrespondingang {ang₁ ang₂ : Angle P} (h : IsCorrespondingAng ang₁ ang₂) : ang₁.value = ang₂.value := sorry

theorem value_sub_eq_pi_of_isconsecutiveintang {ang₁ ang₂ : Angle P} (h : IsConsecutiveIntAng ang₁ ang₂) : ang₁.value - ang₂.value = π := sorry --`first mod 2π, then discuss +-? `

theorem value_eq_of_isalternateintang {ang₁ ang₂ : Angle P} (h : IsAlternateIntAng ang₁ ang₂) : ang₁.value = ang₂.value := sorry

/-
-- equivlently, this will be much more lengthy
theorem value_eq_of_corresponding_angle {l₁ l₂ l : DirLine P} (h : l₁.toDir = l₂.toDir) (g : ¬ l ∥ l₁) : (Angle.mk_dirline_dirline l₁ l (Ne.symm g)).value = (Angle.mk_dirline_dirline l₂ l (Ne.symm (ne_of_ne_of_eq g (Quotient.sound (h ▸ PM.con.refl _))))).value := sorry
-/

end parallel

namespace Angle

@[pp_dot]
def reverse (ang : Angle P) : Angle P where
  source := ang.source
  dir₁ := ang.dir₂
  dir₂ := ang.dir₁

theorem rev_value_eq_neg_value {ang : Angle P} : ang.reverse.value = - ang.value :=
  (neg_vsub_eq_vsub_rev ang.reverse.dir₁ ang.reverse.dir₂).symm

end Angle

end EuclidGeom
