import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex2
import EuclideanGeometry.Foundation.Tactic.Congruence.Attr

namespace EuclidGeom

/- definition of congruence of triangles-/

/- congruences of triangles, separate definitions for reversing orientation or not, (requiring all sides and angles being the same)-/

variable {P : Type _} [EuclideanPlane P]
-- only define congrence for Triangle_nd
--def IsCongr (tr_nd₁ tr_nd₂: Triangle_nd P) : Prop := (tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length ∧ tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length ∧ tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length ∧ tr_nd₁.angle₁.value = tr_nd₂.angle₁.value ∧ tr_nd₁.angle₂.value = tr_nd₂.angle₂.value ∧ tr_nd₁.angle₃.value = tr_nd₂.angle₃.value)
def IsCongr (tr₁ tr₂: Triangle P) : Prop := by
  by_cases tr₁.is_nd ∧ tr₂.is_nd
  · let tr_nd₁ : Triangle_nd P := ⟨tr₁, h.1⟩
    let tr_nd₂ : Triangle_nd P := ⟨tr₂, h.2⟩
    exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length ∧ tr_nd₁.angle₁.value = tr_nd₂.angle₁.value ∧ tr_nd₁.angle₂.value = tr_nd₂.angle₂.value ∧ tr_nd₁.angle₃.value = tr_nd₂.angle₃.value
  · exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length

scoped infix : 50 "IsCongrTo" => IsCongr

scoped infix : 50 "≅" => IsCongr --do we need?

namespace IsCongr

section triangle

variable (tr₁ tr₂: Triangle P) (h : tr₁ IsCongrTo tr₂)

theorem is_nd: tr₁.is_nd = tr₂.is_nd := by
  rw [IsCongr] at h
  by_cases nd1 : tr₁.is_nd
  · let nd₁ := nd1
    rw [eq_true nd₁]
    by_contra nd_2
    simp only [eq_iff_iff, true_iff] at nd_2
    have notnd : ¬ (Triangle.is_nd tr₁ ∧ Triangle.is_nd tr₂) := by
      push_neg
      intro _
      exact nd_2
    unfold Triangle.is_nd at nd_2
    push_neg at nd_2
    have sum := (Triangle.edge_sum_eq_edge_iff_colinear tr₂).mp nd_2
    simp only [dif_neg notnd] at h
    rcases h with ⟨h₁,⟨h₂,h₃⟩⟩
    rw [← h₁,← h₂,← h₃] at sum
    have nd_1 := (Triangle.edge_sum_eq_edge_iff_colinear tr₁).mpr sum
    unfold Triangle.is_nd at nd₁
    exact nd₁ nd_1
  · let nd_1 := nd1
    have notnd : ¬ (Triangle.is_nd tr₁ ∧ Triangle.is_nd tr₂) := by
      push_neg
      intro nd₁
      exfalso
      exact nd_1 nd₁
    unfold Triangle.is_nd at nd_1
    push_neg at nd_1
    have sum := (Triangle.edge_sum_eq_edge_iff_colinear tr₁).mp nd_1
    simp only [dif_neg notnd] at h
    rcases h with ⟨h₁,⟨h₂,h₃⟩⟩
    rw [h₁,h₂,h₃] at sum
    have nd_2 := (Triangle.edge_sum_eq_edge_iff_colinear tr₂).mpr sum
    rw [eq_false nd1]
    simp only [eq_iff_iff, false_iff]
    unfold Triangle.is_nd
    push_neg
    exact nd_2

theorem edge₁ : tr₁.edge₁.length = tr₂.edge₁.length := by
  rw [IsCongr] at h
  have h' := eq_true h
  by_cases nd : (tr₁.is_nd ∧ tr₂.is_nd)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨s₁,_⟩
    exact s₁
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨t₁,_⟩
    exact t₁

theorem edge₂ : tr₁.edge₂.length = tr₂.edge₂.length := by
  rw [IsCongr] at h
  have h' := eq_true h
  by_cases nd : (tr₁.is_nd ∧ tr₂.is_nd)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨s₂,_⟩⟩
    exact s₂
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨t₂,_⟩⟩
    exact t₂

theorem edge₃ : tr₁.edge₃.length = tr₂.edge₃.length := by
  rw[IsCongr] at h
  have h' := eq_true h
  by_cases nd : (tr₁.is_nd ∧ tr₂.is_nd)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨_,⟨s₃,_⟩⟩⟩
    exact s₃
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨_,t₃⟩⟩
    exact t₃

end triangle

section triangle_nd

variable (tr_nd₁ tr_nd₂: Triangle_nd P) (h:tr_nd₁.1 IsCongrTo tr_nd₂.1)

theorem angle₁.value : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value := by
  rw [IsCongr] at h
  have i : Triangle.is_nd tr_nd₁.1 ∧ Triangle.is_nd tr_nd₂.1 := by constructor;exact tr_nd₁.2;exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h
  rcases h with ⟨_,⟨_,⟨_,⟨h₄,_⟩⟩⟩⟩
  exact h₄

theorem angle₂.value : tr_nd₁.angle₂.value = tr_nd₂.angle₂.value := by
  rw [IsCongr] at h
  have i : Triangle.is_nd tr_nd₁.1 ∧ Triangle.is_nd tr_nd₂.1 := by constructor;exact tr_nd₁.2;exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h
  rcases h with ⟨_,⟨_,⟨_,⟨_,⟨h₅,_⟩⟩⟩⟩⟩
  exact h₅

theorem angle₃.value : tr_nd₁.angle₃.value = tr_nd₂.angle₃.value := by
  rw [IsCongr] at h
  have i : Triangle.is_nd tr_nd₁.1 ∧ Triangle.is_nd tr_nd₂.1 := by constructor;exact tr_nd₁.2;exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h
  rcases h with ⟨_,⟨_,⟨_,⟨_,⟨_,h₆⟩⟩⟩⟩⟩
  exact h₆

theorem is_cclock : tr_nd₁.is_cclock = tr_nd₂.is_cclock := by
  rw [IsCongr] at h
  simp [tr_nd₁.2,tr_nd₂.2] at h
  rcases h with ⟨_,_,_,a₁,a₂,a₃⟩
  by_cases cclock₁ : Triangle_nd.is_cclock tr_nd₁
  · have a := Triangle.angle_pos_of_cclock tr_nd₁ cclock₁
    simp only [a₁,a₂,a₃] at a
    have b := Triangle.cclock_of_pos_angle tr_nd₂
    rcases a with ⟨nonneg_a₁,_,_⟩
    simp only [cclock₁,eq_iff_iff, true_iff]
    apply b ; left ; exact nonneg_a₁
  · have a := Triangle.angle_neg_of_clock tr_nd₁ cclock₁
    simp only [a₁,a₂,a₃] at a
    have b := Triangle.clock_of_neg_angle tr_nd₂
    rcases a with ⟨neg_a₁,_,_⟩
    simp only [cclock₁ , eq_iff_iff ,false_iff]
    apply b
    left
    exact neg_a₁

end triangle_nd

end IsCongr

namespace IsCongr

variable (tr tr₁ tr₂ tr₃: Triangle P)

protected theorem refl : tr IsCongrTo tr := by
  rw [IsCongr]
  by_cases h': Triangle.is_nd tr
  · have h'' : Triangle.is_nd tr ∧ Triangle.is_nd tr := by simp only [h', and_self]
    rw [dif_pos h'']
    repeat
     constructor
     rfl
    rfl
  · have h'' : ¬ (Triangle.is_nd tr ∧ Triangle.is_nd tr) := by simp only [h', and_self, not_false_eq_true]
    rw [dif_neg h'']
    repeat
     constructor
     rfl
    rfl

protected theorem symm (h : tr₁ IsCongrTo tr₂) : tr₂ IsCongrTo tr₁ := by
  by_cases nd₁ : Triangle.is_nd tr₁
  · have nd₂ := (is_nd tr₁ tr₂) h
    rw [eq_true nd₁] at nd₂
    simp at nd₂
    rw [IsCongr] at h
    simp only [nd₁,nd₂, and_self, dite_true] at h
    rw [IsCongr]
    simp only [nd₂, nd₁, and_self, dite_true]
    rcases h with ⟨h₁,⟨h₂,⟨h₃,⟨h₄,⟨h₅,h₆⟩⟩⟩⟩⟩
    simp only [h₁, h₂, h₃, h₄, h₅, h₆, and_self]
  · have nd_2 := (is_nd tr₁ tr₂) h
    rw [eq_false nd₁] at nd_2
    simp only [eq_iff_iff, false_iff] at nd_2
    rw [IsCongr] at h
    simp only [nd_2, and_false, dite_false] at h
    rw [IsCongr]
    simp only [nd_2, false_and, dite_false]
    rcases h with ⟨h₁,⟨h₂,h₃⟩⟩
    simp only [h₁, h₂, h₃, and_self]

protected theorem trans (h₁ : tr₁ IsCongrTo tr₂) (h₂ : tr₂ IsCongrTo tr₃) : tr₁ IsCongrTo tr₃ := by
    rw [IsCongr] at h₁ h₂
    rw [IsCongr]
    by_cases nd₁ : tr₁.is_nd
    . have nd₂ : tr₁.is_nd = tr₂.is_nd := by apply IsCongr.is_nd tr₁ tr₂ h₁
      simp only [nd₁, eq_iff_iff, true_iff] at nd₂
      have nd₃ : tr₂.is_nd = tr₃.is_nd := by apply IsCongr.is_nd tr₂ tr₃ h₂
      simp only [nd₂, eq_iff_iff, true_iff] at nd₃
      simp only [nd₁, nd₂, and_self, dite_true] at h₁
      simp only [nd₂, nd₃, and_self, dite_true] at h₂
      simp only [nd₁, nd₃, and_self, dite_true]
      rcases h₁ with ⟨l₁,l₂,l₃,a₁,a₂,a₃⟩
      rcases h₂ with ⟨l₁',l₂',l₃',a₁',a₂',a₃'⟩
      rw [<-l₁] at l₁' ; rw [<-l₂] at l₂' ; rw [<-l₃] at l₃' ; rw [<-a₁] at a₁' ; rw[<-a₂] at a₂' ; rw[<-a₃] at a₃'
      simp only [l₁',l₂',l₃',a₁',a₂',a₃']
    . have nd₂ : tr₁.is_nd = tr₂.is_nd := by apply IsCongr.is_nd tr₁ tr₂ h₁
      simp only [nd₁, eq_iff_iff, false_iff] at nd₂
      have nd₃ : tr₂.is_nd = tr₃.is_nd := by apply IsCongr.is_nd tr₂ tr₃ h₂
      simp only [nd₂, eq_iff_iff, false_iff] at nd₃
      simp only [nd₁, nd₂, and_self, dite_false] at h₁
      simp only [nd₂, nd₃, and_self, dite_false] at h₂
      simp only [nd₁, nd₃, and_self, dite_false]
      rcases h₁ with ⟨l₁,l₂,l₃⟩
      rcases h₂ with ⟨l₁',l₂',l₃'⟩
      rw [<-l₁] at l₁' ; rw [<-l₂] at l₂' ; rw [<-l₃] at l₃'
      simp only [l₁',l₂',l₃']

instance : IsEquiv (Triangle P) IsCongr where
  refl := IsCongr.refl
  symm := IsCongr.symm
  trans := IsCongr.trans

end IsCongr

/- Anti-congruence -/
def IsACongr (tr₁ tr₂: Triangle P) : Prop := by
  by_cases tr₁.is_nd ∧ tr₂.is_nd
  · let tr_nd₁ : Triangle_nd P := ⟨tr₁, h.1⟩
    let tr_nd₂ : Triangle_nd P := ⟨tr₂, h.2⟩
    exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length ∧ tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value ∧ tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value ∧ tr_nd₁.angle₃.value = - tr_nd₂.angle₃.value
  · exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length

scoped infix : 50 "IsACongrTo" => IsACongr

scoped infix : 50 "≅ₐ" => IsACongr --do we need?

namespace IsACongr

section triangle

variable (tr₁ tr₂: Triangle P) (h : tr₁ IsACongrTo tr₂)

theorem is_nd: tr₁.is_nd ↔ tr₂.is_nd := by
  rw [IsACongr] at h
  constructor
  · intro nd₁
    by_contra nd_2
    have notnd : ¬ (Triangle.is_nd tr₁ ∧ Triangle.is_nd tr₂) := by
      push_neg
      intro _
      exact nd_2
    unfold Triangle.is_nd at nd_2
    push_neg at nd_2
    have sum := (Triangle.edge_sum_eq_edge_iff_colinear tr₂).mp nd_2
    simp only [dif_neg notnd] at h
    rcases h with ⟨h₁,⟨h₂,h₃⟩⟩
    rw [← h₁,← h₂,← h₃] at sum
    have nd_1 := (Triangle.edge_sum_eq_edge_iff_colinear tr₁).mpr sum
    unfold Triangle.is_nd at nd₁
    exact nd₁ nd_1
  · intro nd₂
    by_contra nd_1
    have notnd : ¬ (Triangle.is_nd tr₁ ∧ Triangle.is_nd tr₂) := by
      push_neg
      intro nd₁
      exfalso
      exact nd_1 nd₁
    unfold Triangle.is_nd at nd_1
    push_neg at nd_1
    have sum := (Triangle.edge_sum_eq_edge_iff_colinear tr₁).mp nd_1
    simp only [dif_neg notnd] at h
    rcases h with ⟨h₁,⟨h₂,h₃⟩⟩
    rw [h₁,h₂,h₃] at sum
    have nd_2 := (Triangle.edge_sum_eq_edge_iff_colinear tr₂).mpr sum
    exact nd₂ nd_2

theorem edge₁ : tr₁.edge₁.length = tr₂.edge₁.length := by
  rw [IsACongr] at h
  have h' :=eq_true h
  by_cases nd : (tr₁.is_nd ∧ tr₂.is_nd)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨s₁,_⟩
    exact s₁
  · simp only [nd, dite_false, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨t₁,_⟩
    exact t₁

theorem edge₂ : tr₁.edge₂.length = tr₂.edge₂.length := by
  rw [IsACongr] at h
  have h' := eq_true h
  by_cases nd : (tr₁.is_nd ∧ tr₂.is_nd)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨s₂,_⟩⟩
    exact s₂
  · simp only [nd, dite_false, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨t₂,_⟩⟩
    exact t₂

theorem edge₃ : tr₁.edge₃.length = tr₂.edge₃.length := by
  rw [IsACongr] at h
  have h' := eq_true h
  by_cases nd : (tr₁.is_nd ∧ tr₂.is_nd)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨_,⟨s₃,_⟩⟩⟩
    exact s₃
  · simp only [nd, dite_false, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨_,t₃⟩⟩
    exact t₃

end triangle

section triangle_nd

variable (tr_nd₁ tr_nd₂: Triangle_nd P) (h : tr_nd₁.1 IsACongrTo tr_nd₂.1)

theorem angle₁.value : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value := by
  rw [IsACongr] at h
  have i : Triangle.is_nd tr_nd₁.1 ∧ Triangle.is_nd tr_nd₂.1 := by constructor ; exact tr_nd₁.2 ; exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h
  rcases h with ⟨_,⟨_,⟨_,⟨h₄,_⟩⟩⟩⟩
  exact h₄

theorem angle₂.value : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value := by
  rw [IsACongr] at h
  have i : Triangle.is_nd tr_nd₁.1 ∧ Triangle.is_nd tr_nd₂.1 := by constructor ; exact tr_nd₁.2 ; exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h
  rcases h with ⟨_,⟨_,⟨_,⟨_,⟨h₅,_⟩⟩⟩⟩⟩
  exact h₅

theorem angle₃.value : tr_nd₁.angle₃.value = - tr_nd₂.angle₃.value := by
  rw [IsACongr] at h
  have i : Triangle.is_nd tr_nd₁.1 ∧ Triangle.is_nd tr_nd₂.1 := by constructor ; exact tr_nd₁.2 ; exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h
  rcases h with ⟨_,⟨_,⟨_,⟨_,⟨_,h₆⟩⟩⟩⟩⟩
  exact h₆

theorem is_cclock : tr_nd₁.is_cclock = ¬ tr_nd₂.is_cclock := by
  rw [IsACongr] at h
  simp [tr_nd₁.2,tr_nd₂.2] at h
  rcases h with ⟨_,_,_,a₁,a₂,a₃⟩
  by_cases cclock₁ : Triangle_nd.is_cclock tr_nd₁
  . have a := Triangle.angle_pos_of_cclock tr_nd₁ cclock₁
    simp only [a₁,a₂,a₃] at a
    have b := Triangle.clock_of_neg_angle tr_nd₂
    rcases a with ⟨nonneg_a₁,_,_⟩
    simp only [cclock₁,eq_iff_iff, true_iff]
    apply b ; left ; simp only [Left.neg_pos_iff] at nonneg_a₁ ;exact nonneg_a₁
  . have a := Triangle.angle_neg_of_clock tr_nd₁ cclock₁
    simp only [a₁,a₂,a₃] at a
    have b := Triangle.cclock_of_pos_angle tr_nd₂
    rcases a with ⟨neg_a₁,_,_⟩
    simp only [cclock₁ , eq_iff_iff ,false_iff]
    push_neg
    apply b
    left
    simp only [Left.neg_neg_iff] at neg_a₁
    exact neg_a₁

end triangle_nd

end IsACongr

namespace IsACongr

variable (tr tr₁ tr₂ tr₃: Triangle P)

theorem triv_of_acongr_self (h : tr IsACongrTo tr) : ¬ tr.is_nd := by
   rw [IsACongr] at h
   by_contra nd
   let tr_nd : Triangle_nd P := ⟨tr,nd⟩
   simp only [nd, and_self, true_and, dite_true] at h
   rcases h with ⟨anti_angle,_⟩
   have eq_zero : Angle.value tr_nd.angle₁ = 0 := by linarith
   unfold Triangle_nd.angle₁ at eq_zero
   have col := Angle.colinear_of_zero_angle eq_zero
   unfold Triangle.is_nd at nd
   apply nd ; exact col

protected theorem symm (h : tr₁ IsACongrTo tr₂) : tr₂ IsACongrTo tr₁ := by
  by_cases nd₁:Triangle.is_nd tr₁
  · have nd₂ := (is_nd tr₁ tr₂) h
    rw [eq_true nd₁] at nd₂
    simp only [true_iff] at nd₂
    have nd : Triangle.is_nd tr₁ ∧ Triangle.is_nd tr₂ := by
      constructor
      exact nd₁
      exact nd₂
    rw [IsACongr] at h
    simp only [nd, and_self, dite_true] at h
    have nd' := And.symm nd
    rw [IsACongr]
    rw [dif_pos nd']
    simp only
    rcases h with ⟨h₁,⟨h₂,⟨h₃,⟨h₄,⟨h₅,h₆⟩⟩⟩⟩⟩
    simp only [h₁, h₂, h₃, h₄, neg_neg, h₅, h₆, and_self]
  · let nd_1 := nd₁
    have nd_2 := (is_nd tr₁ tr₂) h
    rw [eq_false nd₁] at nd_2
    simp at nd_2
    have nd : ¬ (Triangle.is_nd tr₁ ∧ Triangle.is_nd tr₂) := by
      push_neg
      intro nd₁
      exfalso
      exact nd_1 nd₁
    rw [IsACongr] at h
    simp only [nd,dite_false] at h
    have nd' : ¬ (Triangle.is_nd tr₂ ∧ Triangle.is_nd tr₁) := by
      push_neg
      intro _
      exact nd_1
    rw [IsACongr]
    rw [dif_neg nd']
    rcases h with ⟨h₁,⟨h₂,h₃⟩⟩
    simp only [h₁, h₂, h₃, and_self]

theorem congr_of_trans_acongr (h₁ : tr₁ IsACongrTo tr₂) (h₂ : tr₂ IsACongrTo tr₃) : tr₁ IsCongrTo tr₃ := by
    rw [IsACongr] at h₁ h₂
    rw [IsCongr]
    by_cases nd₁ : tr₁.is_nd
    . have nd₂ : tr₁.is_nd ↔ tr₂.is_nd := by apply IsACongr.is_nd tr₁ tr₂ h₁
      simp only [nd₁, true_iff] at nd₂
      have nd₃ : tr₂.is_nd ↔ tr₃.is_nd := by apply IsACongr.is_nd tr₂ tr₃ h₂
      simp only [nd₂, true_iff] at nd₃
      simp only [nd₁, nd₂, and_self, dite_true] at h₁
      simp only [nd₂, nd₃, and_self, dite_true] at h₂
      simp only [nd₁, nd₃, and_self, dite_true]
      rcases h₁ with ⟨l₁,l₂,l₃,a₁,a₂,a₃⟩
      rcases h₂ with ⟨l₁',l₂',l₃',a₁',a₂',a₃'⟩
      rw [<-l₁] at l₁' ; rw [<-l₂] at l₂' ; rw [<-l₃] at l₃' ; rw[ neg_eq_iff_eq_neg.mpr a₁'] at a₁ ; rw[neg_eq_iff_eq_neg.mpr a₂'] at a₂ ; rw[neg_eq_iff_eq_neg.mpr a₃'] at a₃
      simp only [l₁',l₂',l₃',a₁,a₂,a₃]
    . have nd₂ : tr₁.is_nd ↔ tr₂.is_nd := by apply IsACongr.is_nd tr₁ tr₂ h₁
      simp [nd₁] at nd₂
      have nd₃ : tr₂.is_nd ↔ tr₃.is_nd := by apply IsACongr.is_nd tr₂ tr₃ h₂
      simp only [nd₂, false_iff] at nd₃
      simp only [nd₁, nd₂, and_self, dite_false] at h₁
      simp only [nd₂, nd₃, and_self, dite_false] at h₂
      simp only [nd₁, nd₃, and_self, dite_false]
      rcases h₁ with ⟨l₁,l₂,l₃⟩
      rcases h₂ with ⟨l₁',l₂',l₃'⟩
      rw [<-l₁] at l₁' ; rw [<-l₂] at l₂' ; rw [<-l₃] at l₃'
      simp only [l₁',l₂',l₃']

instance : IsSymm (Triangle P) IsACongr where
  symm := IsACongr.symm

end IsACongr


section criteria
/-
criteria of congruence of triangles. each SAS ASA AAS SSS involves congr and anti congr. SSS is special.
Need a tactic `Congrence` to consider filp and permutation. -/

variable {tr_nd₁ tr_nd₂ : Triangle_nd P}

/- SAS -/
@[congr_sa]
theorem congr_of_SAS (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length): tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

theorem acongr_of_SAS (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (a₁ : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length): tr_nd₁.1 IsACongrTo tr_nd₂.1 := sorry

/- ASA -/
@[congr_sa]
theorem congr_of_ASA (a₂ : tr_nd₁.angle₂.value = tr_nd₂.angle₂.value) (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (a₃ : tr_nd₁.angle₃.value = tr_nd₂.angle₃.value): tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

theorem acongr_of_ASA (a₂ : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value) (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (a₃ : tr_nd₁.angle₃.value = - tr_nd₂.angle₃.value): tr_nd₁.1 IsACongrTo tr_nd₂.1 := sorry

/- AAS -/
@[congr_sa]
theorem congr_of_AAS (a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value) (a₂ : tr_nd₁.angle₂.value = tr_nd₂.angle₂.value) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) : tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

theorem acongr_of_AAS (a₁ : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value) (a₂ : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) : tr_nd₁.1 IsACongrTo tr_nd₂.1 := sorry

/- SSS -/
/- cannot decide orientation -/
theorem congr_of_SSS_of_eq_orientation (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) (c : tr_nd₁.is_cclock = tr_nd₂.is_cclock) : tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

theorem acongr_of_SSS_of_ne_orientation (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) (c : tr_nd₁.is_cclock = ¬ tr_nd₂.is_cclock) : tr_nd₁.1 IsACongrTo tr_nd₂.1 := sorry

theorem congr_or_acongr_of_SSS (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length): tr_nd₁.1 IsCongrTo tr_nd₂.1 ∨ tr_nd₁.1 IsACongrTo tr_nd₂.1 := sorry

end criteria

end EuclidGeom
