import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex
import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Convex
import EuclideanGeometry.Foundation.Axiom.Linear.Colinear

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]



section AngleValue


/- theorem - π < angle.value, angle.value ≤ π,  -/
theorem val_gt_neg_pi (ang : Angle P) : -π < ang.value := sorry

theorem val_le_pi (ang : Angle P) : ang.value < π := sorry

/- theorem when angle > 0, IsInt means lies left of start ray + right of end ray; when angle < 0, ...  -/

theorem undefined : sorry := sorry

end AngleValue

section AngleSum

namespace Angle

theorem source_start_ray_eq_source_end_ray (ang : Angle P) : ang.start_ray.source = ang.end_ray.source := sorry


-- Can use congrArg @Ray.source P _) h to turn h into the sources of two terms being equal.
theorem source_eq_source_of_adj {ang₁ ang₂: Angle P} (h : ang₁.end_ray = ang₂.start_ray) : ang₁.start_ray.source = ang₂.end_ray.source := sorry

def sum_adj {ang₁ ang₂: Angle P} (h :ang₁.end_ray = ang₂.start_ray) : Angle P := Angle.mk ang₁.start_ray ang₂.end_ray (source_eq_source_of_adj h)

theorem ang_eq_ang_add_ang_mod_pi_of_adj_ang (ang₁ ang₂ : Angle P) (h: ang₁.end_ray = ang₂.start_ray) : (sum_adj h).value = ang₁.value + ang₂.value ∨ (sum_adj h).value = ang₁.value + ang₂.value + π ∨ (sum_adj h).value = ang₁.value + ang₂.value - π := sorry

end Angle

end AngleSum

section colinear

theorem colinear_of_zero_angle {A O B : P} {h₁ : A ≠ O} {h₂ : B ≠ O} : ∠ A O B h₁ h₂ = 0 → colinear O A B := by sorry

end colinear

section parallel
-- `Do we need a construction and predicate of such angles? theorems can be stated without constructions` `Maybe yes, otherwise there is too many lengthy proofs in statement`
-- Is Corresponding angles : start ray same dir, end ray same
-- Is Consecutive interior angles : start ray same dir, end ray reverse

-- equivlently, this should be named as eq_value_of_eq_dir_of_start_ray_eq_end_ray
theorem eq_value_of_corresponding_angle {l₁ l₂ l : DirLine P} (h : l₁.toDir = l₂.toDir) (g : ¬ l ∥ l₁) : (Angle.mk_dirline_dirline l₁ l (Ne.symm g)).value = (Angle.mk_dirline_dirline l₂ l (Ne.symm (ne_of_ne_of_eq g (Quotient.sound (h ▸ PM.con.refl _))))).value := sorry

end parallel

end EuclidGeom
