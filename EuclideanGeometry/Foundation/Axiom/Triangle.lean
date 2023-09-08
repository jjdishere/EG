import EuclideanGeometry.Foundation.Axiom.Position

noncomputable section
namespace EuclidGeom

open Classical

/- Class of generalized triangles -/
class Triangle (P : Type _) [EuclideanPlane P] where 
  point₁ : P
  point₂ : P
  point₃ : P

variable {P : Type _} [EuclideanPlane P]

namespace Triangle

--implies  1 left of 23, 2 left of 31

-- not is_cclock implies 1 right of 23, ..., ...

def edge₁ (tr : Triangle P) : Seg P := Seg.mk tr.2 tr.3

def edge₂ (tr : Triangle P) : Seg P := Seg.mk tr.3 tr.1

def edge₃ (tr : Triangle P) : Seg P := Seg.mk tr.1 tr.2

def area (tr : Triangle P) : ℝ := sorry 

def is_nontriv (tr : Triangle P) : Prop := ¬ colinear tr.1 tr.2 tr.3

end Triangle

section nondeg

namespace Triangle
variable (tr : Triangle P) (nontriv : tr.is_nontriv)

def nontriv₁ := (ne_of_not_colinear nontriv).1

def nontriv₂ := (ne_of_not_colinear nontriv).2.1

def nontriv₃ := (ne_of_not_colinear nontriv).2.2

/- Only nondegenerate triangles can talk about orientation -/
def is_cclock : Prop := tr.3 LiesOnLeft (Ray.mk_pt_pt tr.1 tr.2 (tr.nontriv₃ nontriv))

def oangle₁ : OAngle P := OAngle.mk_pt_pt_pt _ _ _ (tr.nontriv₃ nontriv) (tr.nontriv₂ nontriv).symm

def oangle₂ : OAngle P := OAngle.mk_pt_pt_pt _ _ _ (tr.nontriv₁ nontriv) (tr.nontriv₃ nontriv).symm

def oangle₃ : OAngle P := OAngle.mk_pt_pt_pt _ _ _ (tr.nontriv₂ nontriv) (tr.nontriv₁ nontriv).symm

def angle₁ : ℝ := (tr.oangle₁ nontriv).value

def angle₂ : ℝ := (tr.oangle₂ nontriv).value

def angle₃ : ℝ := (tr.oangle₃ nontriv).value

end Triangle

end nondeg

namespace Triangle

def IsInside  (A : P) (tr : Triangle P) : Prop := by 
  by_cases colinear tr.1 tr.2 tr.3
  · exact False
  · exact (if tr.is_cclock h then A LiesOnLeft tr.edge₁.toRay_of_nontriv (tr.nontriv₁ h) ∧ A LiesOnLeft tr.edge₂.toRay_of_nontriv (tr.nontriv₂ h) ∧ A LiesOnLeft tr.edge₃.toRay_of_nontriv (tr.nontriv₃ h) else A LiesOnRight tr.edge₁.toRay_of_nontriv (tr.nontriv₁ h)∧ A LiesOnRight tr.edge₂.toRay_of_nontriv (tr.nontriv₂ h) ∧ A LiesOnRight tr.edge₃.toRay_of_nontriv (tr.nontriv₃ h))

end Triangle

scoped infix : 50 "IsInsideTriangle" => Triangle.IsInside

namespace Triangle

variable (tr : Triangle P)

theorem angle_sum_eq_pi_of_cclock (nontriv : tr.is_nontriv) (cclock : tr.is_cclock nontriv): tr.angle₁ nontriv + tr.angle₂ nontriv + tr.angle₃ nontriv = π := sorry 

theorem angle_sum_eq_neg_pi_of_clock (nontriv : tr.is_nontriv) (clock : ¬ tr.is_cclock nontriv): tr.angle₁ nontriv + tr.angle₂ nontriv + tr.angle₃ nontriv = - π := sorry 

theorem angle_pos_of_cclock (nontriv : tr.is_nontriv) (cclock : tr.is_cclock nontriv) : 0 < tr.angle₁ nontriv ∧ 0 < tr.angle₂ nontriv ∧ 0 < tr.angle₃ nontriv := by sorry

theorem angle_neg_of_clock (nontriv : tr.is_nontriv) (clock : ¬ tr.is_cclock nontriv) : tr.angle₁ nontriv < 0 ∧ tr.angle₂ nontriv < 0 ∧ tr.angle₃ nontriv < 0  := by sorry

theorem cclock_of_pos_angle (nontriv : tr.is_nontriv) (h : 0 < tr.angle₁ nontriv ∨ 0 < tr.angle₂ nontriv ∨ 0 < tr.angle₃ nontriv) : tr.is_cclock nontriv := sorry

theorem clock_of_neg_angle (nontriv : tr.is_nontriv) (h : tr.angle₁ nontriv < 0 ∨ tr.angle₂ nontriv < 0 ∨ tr.angle₃ nontriv < 0) : tr.is_cclock nontriv := sorry


theorem triangle_ineq : tr.edge₁.length + tr.edge₂.length ≥ tr.edge₃.length := sorry

theorem triangle_ineq' (nontriv : tr.is_nontriv) : tr.edge₁.length + tr.edge₂.length > tr.edge₃.length := sorry

theorem trivial_of_edge_sum_eq_edge : tr.edge₁.length + tr.edge₂.length = tr.edge₃.length → ¬ tr.is_nontriv  := sorry

theorem nontrivial_of_edge_sum_ne_edge : tr.edge₁.length + tr.edge₂.length ≠ tr.edge₃.length → tr.is_nontriv  := sorry -- should this theorem stated as ≠, or as > ???

/- area ≥ 0, nontrivial → >0, =0 → trivial -/

end Triangle

end EuclidGeom