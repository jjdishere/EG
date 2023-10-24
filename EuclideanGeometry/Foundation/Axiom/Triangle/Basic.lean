import EuclideanGeometry.Foundation.Axiom.Position.Orientation
import EuclideanGeometry.Foundation.Axiom.Linear.Colinear

universe u

noncomputable section
namespace EuclidGeom

open Classical

/- Class of generalized triangles -/
@[ext]
class Triangle (P : Type u) [EuclideanPlane P] where 
  point₁ : P
  point₂ : P
  point₃ : P

namespace Triangle

variable {P : Type u} [EuclideanPlane P]
--implies  1 left of 23, 2 left of 31

-- not is_cclock implies 1 right of 23, ..., ...

def edge₁ (tr : Triangle P) : Seg P := Seg.mk tr.2 tr.3

def edge₂ (tr : Triangle P) : Seg P := Seg.mk tr.3 tr.1

def edge₃ (tr : Triangle P) : Seg P := Seg.mk tr.1 tr.2

def area (tr : Triangle P) : ℝ := sorry 

def is_nd (tr : Triangle P) : Prop := ¬ colinear tr.1 tr.2 tr.3

end Triangle

def Triangle_nd (P : Type u) [EuclideanPlane P] := { tr : Triangle P // tr.is_nd }

namespace Triangle_nd

variable {P : Type u} [EuclideanPlane P] (tr_nd : Triangle_nd P) 

def nontriv₁ := (ne_of_not_colinear tr_nd.2).1

def nontriv₂ := (ne_of_not_colinear tr_nd.2).2.1

def nontriv₃ := (ne_of_not_colinear tr_nd.2).2.2

def edge_nd₁ : Seg_nd P := ⟨tr_nd.1.edge₁, tr_nd.nontriv₁⟩

def edge_nd₂ : Seg_nd P := ⟨tr_nd.1.edge₂, tr_nd.nontriv₂⟩

def edge_nd₃ : Seg_nd P := ⟨tr_nd.1.edge₃, tr_nd.nontriv₃⟩

/- Only nondegenerate triangles can talk about orientation -/
def is_cclock : Prop := tr_nd.1.3 LiesOnLeft (Ray.mk_pt_pt tr_nd.1.1 tr_nd.1.2 (tr_nd.nontriv₃))

def angle₁ : Angle P := Angle.mk_pt_pt_pt _ _ _ (tr_nd.nontriv₃) (tr_nd.nontriv₂).symm

def angle₂ : Angle P := Angle.mk_pt_pt_pt _ _ _ (tr_nd.nontriv₁) (tr_nd.nontriv₃).symm

def angle₃ : Angle P := Angle.mk_pt_pt_pt _ _ _ (tr_nd.nontriv₂) (tr_nd.nontriv₁).symm

end Triangle_nd

variable {P : Type u} [EuclideanPlane P]

namespace Triangle

protected def IsInt (A : P) (tr : Triangle P) : Prop := by 
  by_cases colinear tr.1 tr.2 tr.3
  · exact False
  · let tr_nd : Triangle_nd P := ⟨tr, h⟩ 
    exact (if tr_nd.is_cclock then A LiesOnLeft Seg_nd.toRay ⟨tr.edge₁, tr_nd.nontriv₁⟩ ∧ A LiesOnLeft Seg_nd.toRay ⟨tr.edge₂, tr_nd.nontriv₂⟩ ∧ A LiesOnLeft Seg_nd.toRay ⟨tr.edge₃, tr_nd.nontriv₃⟩ else A LiesOnRight Seg_nd.toRay ⟨tr.edge₁, tr_nd.nontriv₁⟩ ∧ A LiesOnRight Seg_nd.toRay ⟨tr.edge₂, tr_nd.nontriv₂⟩ ∧ A LiesOnRight Seg_nd.toRay ⟨tr.edge₃, tr_nd.nontriv₃⟩)

protected def interior (tr : Triangle P) : Set P := { p : P | Triangle.IsInt p tr }

instance : Interior P (Triangle P) where
  interior := fun t => t.interior

end Triangle

def Triangle_nd.mk (A B C : P) (h : ¬ colinear A B C) : Triangle_nd P := Subtype.mk (Triangle.mk A B C) h

scoped notation "TRI" => Triangle.mk
scoped notation "▵" => Triangle.mk
scoped notation "TRI_nd" A:max B:max C:max h:max => EuclidGeom.Triangle_nd.mk A B C h

namespace Triangle

variable (tr : Triangle P) (tr_nd : Triangle_nd P)

theorem angle_pos_of_cclock (cclock : tr_nd.is_cclock) : 0 < tr_nd.angle₁.value ∧ 0 < tr_nd.angle₂.value ∧ 0 < tr_nd.angle₃.value := by sorry

theorem angle_neg_of_clock (clock : ¬ tr_nd.is_cclock) : tr_nd.angle₁.value < 0 ∧ tr_nd.angle₂.value  < 0 ∧ tr_nd.angle₃.value < 0  := by sorry

theorem cclock_of_pos_angle (h : 0 < tr_nd.angle₁.value ∨ 0 < tr_nd.angle₂.value ∨ 0 < tr_nd.angle₃.value) : tr_nd.is_cclock := sorry

theorem clock_of_neg_angle (h : tr_nd.angle₁.value < 0 ∨ tr_nd.angle₂.value < 0 ∨ tr_nd.angle₃.value < 0) :¬ tr_nd.is_cclock := sorry

theorem angle_sum_eq_pi_of_cclock (cclock : tr_nd.is_cclock): tr_nd.angle₁.value + tr_nd.angle₂.value + tr_nd.angle₃.value = π := sorry

theorem angle_sum_eq_neg_pi_of_clock (clock : ¬ tr_nd.is_cclock): tr_nd.angle₁.value + tr_nd.angle₂.value + tr_nd.angle₃.value = - π := sorry 

theorem triangle_ineq : tr.edge₁.length + tr.edge₂.length ≥ tr.edge₃.length := sorry

theorem triangle_ineq' (nontriv : tr.is_nd) : tr.edge₁.length + tr.edge₂.length > tr.edge₃.length := sorry

theorem trivial_of_edge_sum_eq_edge : tr.edge₁.length + tr.edge₂.length = tr.edge₃.length → ¬ tr.is_nd  := sorry

theorem nontrivial_of_edge_sum_ne_edge : tr.edge₁.length + tr.edge₂.length ≠ tr.edge₃.length → tr.is_nd  := sorry -- should this theorem stated as ≠, or as > ???

theorem edge_sum_eq_edge_iff_colinear :  colinear tr.1 tr.2 tr.3 ↔ (tr.edge₁.length + tr.edge₂.length = tr.edge₃.length) ∨ (tr.edge₂.length + tr.edge₃.length = tr.edge₁.length) ∨ (tr.edge₃.length + tr.edge₁.length = tr.edge₂.length) := sorry 
/- area ≥ 0, nontrivial → >0, =0 → trivial -/

end Triangle

end EuclidGeom