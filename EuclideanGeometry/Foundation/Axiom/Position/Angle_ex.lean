import EuclideanGeometry.Foundation.Axiom.Position.Angle


noncomputable section

namespace EuclidGeom

namespace Angle

/- whether an angle is acute/right/obtuse. -/

def IsRightAngle {P : Type _} [EuclideanPlane P] (ang : Angle P) : Prop := sorry


def IsAcuteAngle {P : Type _} [EuclideanPlane P] (ang : Angle P) : Prop := sorry


def IsObtuseAngle {P : Type _} [EuclideanPlane P] (ang : Angle P) : Prop := sorry


--`This section should be rewrite`
/- Supplementary angles -/

-- Define the supplementary angle to be the angle
variable {P : Type _} [EuclideanPlane P] (ang : Angle P)

def supplementary : Angle P where
  start_ray := ang.end_ray
  end_ray := ang.start_ray.reverse
  source_eq_source := sorry

-- If two oriented angles share a same side, then they are supplementary oriented angles if and only if the sum of two angles is π or -π   `Do I use {ang1} or (ang1)?

theorem reverse_ray_iff_sum_of_angle_eq_pi {ang1 : Angle P} {ang2 : Angle P} (h: ang1.end_ray = ang2.start_ray) : ang1.end_ray = ang2.start_ray.reverse ↔ ang1.value + ang2.value = π ∨ ang1.value + ang2.value = -π := by sorry

theorem right_of_supp_of_right (rt : IsRightAngle ang) :  IsRightAngle ang.supplementary := by sorry

theorem acute_of_supp_of_obtuse (rt : IsObtuseAngle ang) :  IsRightAngle ang.supplementary := by sorry

theorem obtuse_of_supp_of_acute (rt : IsAcuteAngle ang) :  IsRightAngle ang.supplementary := by sorry

theorem IsND_of_supp_of_IsND (nontriv : ang.IsND) : ang.supplementary.IsND := by sorry

def opposite :(Angle P) where
  start_ray := ang.start_ray.reverse
  end_ray := ang.end_ray.reverse
  source_eq_source := sorry

theorem opposite_eq_supp_of_supp : ang.supplementary.supplementary = ang := by sorry

theorem  IsND_of_oppo_of_IsND (nontriv : ang.IsND) : ang.opposite.IsND := by sorry

end Angle

section parallel
variable {P : Type _} [EuclideanPlane P]
-- should be stated use mod 2pi first, then back to pi or -pi

theorem ang_eq_ang_of_toDir_eq_toDir {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = ang₂.start_ray.toDir) (he : ang₁.end_ray.toDir = ang₂.end_ray.toDir) : ang₁.value = ang₂.value := sorry

theorem start_ray_toDir_eq_toDir_of_ang_eq_ang {ang₁ ang₂ : Angle P} (hs : ang₁.end_ray.toDir = ang₂.end_ray.toDir) (h : ang₁.value = ang₂.value) : ang₁.start_ray.toDir = ang₂.start_ray.toDir := sorry

theorem end_ray_toDir_eq_toDir_of_ang_eq_ang {ang₁ ang₂ : Angle P} (hs : ang₁.start_ray.toDir = ang₂.start_ray.toDir) (h : ang₁.value = ang₂.value) : ang₁.end_ray.toDir = ang₂.end_ray.toDir := sorry

-- theorem discuss all possible case of end/start.toDir = +- end/start.toDir
-- `do we need construction of OppositeAng?`

structure IsOppositeAng (ang₁ ang₂ : Angle P) : Prop where
  start_ray : ang₁.start_ray = ang₂.start_ray.reverse
  end_ray : ang₁.end_ray = ang₂.end_ray.reverse

structure IsCorrespondingAng (ang₁ ang₂ : Angle P) : Prop where
  start_ray : ang₁.start_ray.toDir = ang₂.start_ray.toDir
  end_ray : ang₁.end_ray.toDirLine = ang₂.end_ray.toDirLine

structure IsConsecutiveIntAng (ang₁ ang₂ : Angle P) : Prop where
  start_ray : ang₁.start_ray.toDir = ang₂.start_ray.toDir
  end_ray : ang₁.end_ray.toDirLine = ang₂.end_ray.toDirLine.reverse

structure IsAlternateIntAng (ang₁ ang₂ : Angle P) : Prop where
  start_ray : ang₁.start_ray.toDir = - ang₂.start_ray.toDir
  end_ray : ang₁.end_ray.toDirLine = ang₂.end_ray.toDirLine.reverse

theorem IsOppositeAng.symm {ang₁ ang₂ : Angle P} : IsOppositeAng ang₁ ang₂ → IsOppositeAng ang₂ ang₁ := sorry

theorem IsCorrespondingAng.symm {ang₁ ang₂ : Angle P} : IsCorrespondingAng ang₁ ang₂ → IsCorrespondingAng ang₂ ang₁ := sorry

theorem IsConsecutiveIntAng.symm {ang₁ ang₂ : Angle P} : IsConsecutiveIntAng ang₁ ang₂ → IsConsecutiveIntAng ang₂ ang₁ := sorry

theorem IsAlternateIntAng.symm {ang₁ ang₂ : Angle P} : IsAlternateIntAng ang₁ ang₂ → IsAlternateIntAng ang₂ ang₁ := sorry

theorem eq_value_of_isoppositeang {ang₁ ang₂ : Angle P} (h : IsOppositeAng ang₁ ang₂) : ang₁.value = ang₂.value := sorry

theorem eq_value_of_iscorrespondingang {ang₁ ang₂ : Angle P} (h : IsCorrespondingAng ang₁ ang₂) : ang₁.value = ang₂.value := sorry

theorem value_sub_eq_pi_of_isconsecutiveintang {ang₁ ang₂ : Angle P} (h : IsConsecutiveIntAng ang₁ ang₂) : ang₁.value - ang₂.value = π := sorry --`first mod 2π, then discuss +-? `

theorem eq_value_of_isalternateintang {ang₁ ang₂ : Angle P} (h : IsAlternateIntAng ang₁ ang₂) : ang₁.value = ang₂.value := sorry

/-
-- equivlently, this will be much more lengthy
theorem eq_value_of_corresponding_angle {l₁ l₂ l : DirLine P} (h : l₁.toDir = l₂.toDir) (g : ¬ l ∥ l₁) : (Angle.mk_dirline_dirline l₁ l (Ne.symm g)).value = (Angle.mk_dirline_dirline l₂ l (Ne.symm (ne_of_ne_of_eq g (Quotient.sound (h ▸ PM.con.refl _))))).value := sorry
-/

end parallel

namespace Angle

variable {P : Type _} [EuclideanPlane P] (ang : Angle P)


end Angle


end EuclidGeom
