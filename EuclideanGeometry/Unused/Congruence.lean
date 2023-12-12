import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_ex
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex2
import EuclideanGeometry.Foundation.Tactic.Congruence.Attr
import EuclideanGeometry.Foundation.Axiom.Triangle.Trigonometric
import EuclideanGeometry.Foundation.Axiom.Linear.Ray
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_trash

open Classical
namespace EuclidGeom

/- definition of congruence of triangles-/

/- congruences of triangles, separate definitions for reversing orientation or not, (requiring all sides and angles being the same)-/

variable {P : Type _} [EuclideanPlane P]
-- only define congrence for TriangleND
--def IsCongr (tr_nd₁ tr_nd₂: TriangleND P) : Prop := (tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length ∧ tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length ∧ tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length ∧ tr_nd₁.angle₁.value = tr_nd₂.angle₁.value ∧ tr_nd₁.angle₂.value = tr_nd₂.angle₂.value ∧ tr_nd₁.angle₃.value = tr_nd₂.angle₃.value)
def IsCongr (tr₁ tr₂: Triangle P) : Prop := by
  by_cases tr₁.isND ∧ tr₂.isND
  · let tr_nd₁ : TriangleND P := ⟨tr₁, h.1⟩
    let tr_nd₂ : TriangleND P := ⟨tr₂, h.2⟩
    exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length ∧ tr_nd₁.angle₁.value = tr_nd₂.angle₁.value ∧ tr_nd₁.angle₂.value = tr_nd₂.angle₂.value ∧ tr_nd₁.angle₃.value = tr_nd₂.angle₃.value
  · exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length

scoped infix : 50 " IsCongrTo " => IsCongr

-- scoped infix : 50 " ≅ " => IsCongr --do we need?

namespace IsCongr

section triangle

variable (tr₁ tr₂: Triangle P) (h : tr₁ IsCongrTo tr₂)

theorem isND: tr₁.isND = tr₂.isND := by
  rw [IsCongr] at h
  by_cases nd1 : tr₁.isND
  · let nd₁ := nd1
    rw [eq_true nd₁]
    by_contra nd_2
    simp only [eq_iff_iff, true_iff] at nd_2
    have notnd : ¬ (Triangle.isND tr₁ ∧ Triangle.isND tr₂) := by
      push_neg
      intro _
      exact nd_2
    unfold Triangle.isND at nd_2
    push_neg at nd_2
    have sum := (Triangle.edge_sum_eq_edge_iff_colinear tr₂).mp nd_2
    simp only [dif_neg notnd] at h
    rcases h with ⟨h₁,⟨h₂,h₃⟩⟩
    rw [← h₁,← h₂,← h₃] at sum
    have nd_1 := (Triangle.edge_sum_eq_edge_iff_colinear tr₁).mpr sum
    unfold Triangle.isND at nd₁
    exact nd₁ nd_1
  · let nd_1 := nd1
    have notnd : ¬ (Triangle.isND tr₁ ∧ Triangle.isND tr₂) := by
      push_neg
      intro nd₁
      exfalso
      exact nd_1 nd₁
    unfold Triangle.isND at nd_1
    push_neg at nd_1
    have sum := (Triangle.edge_sum_eq_edge_iff_colinear tr₁).mp nd_1
    simp only [dif_neg notnd] at h
    rcases h with ⟨h₁,⟨h₂,h₃⟩⟩
    rw [h₁,h₂,h₃] at sum
    have nd_2 := (Triangle.edge_sum_eq_edge_iff_colinear tr₂).mpr sum
    rw [eq_false nd1]
    simp only [eq_iff_iff, false_iff]
    unfold Triangle.isND
    push_neg
    exact nd_2

theorem edge₁ : tr₁.edge₁.length = tr₂.edge₁.length := by
  rw [IsCongr] at h
  have h' := eq_true h
  by_cases nd : (tr₁.isND ∧ tr₂.isND)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨s₁,_⟩
    exact s₁
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨t₁,_⟩
    exact t₁

theorem edge₂ : tr₁.edge₂.length = tr₂.edge₂.length := by
  rw [IsCongr] at h
  have h' := eq_true h
  by_cases nd : (tr₁.isND ∧ tr₂.isND)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨s₂,_⟩⟩
    exact s₂
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨t₂,_⟩⟩
    exact t₂

theorem edge₃ : tr₁.edge₃.length = tr₂.edge₃.length := by
  rw[IsCongr] at h
  have h' := eq_true h
  by_cases nd : (tr₁.isND ∧ tr₂.isND)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨_,⟨s₃,_⟩⟩⟩
    exact s₃
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨_,t₃⟩⟩
    exact t₃

end triangle

section triangle_nd

variable (tr_nd₁ tr_nd₂: TriangleND P) (h:tr_nd₁.1 IsCongrTo tr_nd₂.1)

theorem angle₁.value : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value := by
  rw [IsCongr] at h
  have i : Triangle.isND tr_nd₁.1 ∧ Triangle.isND tr_nd₂.1 := by constructor;exact tr_nd₁.2;exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h
  rcases h with ⟨_,⟨_,⟨_,⟨h₄,_⟩⟩⟩⟩
  exact h₄

theorem angle₂.value : tr_nd₁.angle₂.value = tr_nd₂.angle₂.value := by
  rw [IsCongr] at h
  have i : Triangle.isND tr_nd₁.1 ∧ Triangle.isND tr_nd₂.1 := by constructor;exact tr_nd₁.2;exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h
  rcases h with ⟨_,⟨_,⟨_,⟨_,⟨h₅,_⟩⟩⟩⟩⟩
  exact h₅

theorem angle₃.value : tr_nd₁.angle₃.value = tr_nd₂.angle₃.value := by
  rw [IsCongr] at h
  have i : Triangle.isND tr_nd₁.1 ∧ Triangle.isND tr_nd₂.1 := by constructor;exact tr_nd₁.2;exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h
  rcases h with ⟨_,⟨_,⟨_,⟨_,⟨_,h₆⟩⟩⟩⟩⟩
  exact h₆

theorem is_cclock : tr_nd₁.is_cclock = tr_nd₂.is_cclock := by
  rw [IsCongr] at h
  simp [tr_nd₁.2,tr_nd₂.2] at h
  rcases h with ⟨_,_,_,a₁,a₂,a₃⟩
  by_cases cclock₁ : TriangleND.is_cclock tr_nd₁
  · have a := tr_nd₁.angle_pos_of_cclock cclock₁
    simp only [a₁,a₂,a₃] at a
    have b := tr_nd₂.cclock_of_pos_angle
    rcases a with ⟨nonneg_a₁,_,_⟩
    simp only [cclock₁,eq_iff_iff, true_iff]
    apply b ; left ; exact nonneg_a₁
  · have a := tr_nd₁.angle_neg_of_clock cclock₁
    simp only [a₁,a₂,a₃] at a
    have b := tr_nd₂.clock_of_neg_angle
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
  by_cases h': Triangle.isND tr
  · have h'' : Triangle.isND tr ∧ Triangle.isND tr := by simp only [h', and_self]
    rw [dif_pos h'']
    repeat
     constructor
     rfl
    rfl
  · have h'' : ¬ (Triangle.isND tr ∧ Triangle.isND tr) := by simp only [h', and_self, not_false_eq_true]
    rw [dif_neg h'']
    repeat
     constructor
     rfl
    rfl

protected theorem symm (h : tr₁ IsCongrTo tr₂) : tr₂ IsCongrTo tr₁ := by
  by_cases nd₁ : Triangle.isND tr₁
  · have nd₂ := (isND tr₁ tr₂) h
    rw [eq_true nd₁] at nd₂
    simp at nd₂
    rw [IsCongr] at h
    simp only [nd₁,nd₂, and_self, dite_true] at h
    rw [IsCongr]
    simp only [nd₂, nd₁, and_self, dite_true]
    rcases h with ⟨h₁,⟨h₂,⟨h₃,⟨h₄,⟨h₅,h₆⟩⟩⟩⟩⟩
    simp only [h₁, h₂, h₃, h₄, h₅, h₆, and_self]
  · have nd_2 := (isND tr₁ tr₂) h
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
    by_cases nd₁ : tr₁.isND
    . have nd₂ : tr₁.isND = tr₂.isND := by apply IsCongr.isND tr₁ tr₂ h₁
      simp only [nd₁, eq_iff_iff, true_iff] at nd₂
      have nd₃ : tr₂.isND = tr₃.isND := by apply IsCongr.isND tr₂ tr₃ h₂
      simp only [nd₂, eq_iff_iff, true_iff] at nd₃
      simp only [nd₁, nd₂, and_self, dite_true] at h₁
      simp only [nd₂, nd₃, and_self, dite_true] at h₂
      simp only [nd₁, nd₃, and_self, dite_true]
      rcases h₁ with ⟨l₁,l₂,l₃,a₁,a₂,a₃⟩
      rcases h₂ with ⟨l₁',l₂',l₃',a₁',a₂',a₃'⟩
      rw [<-l₁] at l₁' ; rw [<-l₂] at l₂' ; rw [<-l₃] at l₃' ; rw [<-a₁] at a₁' ; rw[<-a₂] at a₂' ; rw[<-a₃] at a₃'
      simp only [l₁',l₂',l₃',a₁',a₂',a₃']
      tauto
    . have nd₂ : tr₁.isND = tr₂.isND := by apply IsCongr.isND tr₁ tr₂ h₁
      simp only [nd₁, eq_iff_iff, false_iff] at nd₂
      have nd₃ : tr₂.isND = tr₃.isND := by apply IsCongr.isND tr₂ tr₃ h₂
      simp only [nd₂, eq_iff_iff, false_iff] at nd₃
      simp only [nd₁, nd₂, and_self, dite_false] at h₁
      simp only [nd₂, nd₃, and_self, dite_false] at h₂
      simp only [nd₁, nd₃, and_self, dite_false]
      rcases h₁ with ⟨l₁,l₂,l₃⟩
      rcases h₂ with ⟨l₁',l₂',l₃'⟩
      rw [<-l₁] at l₁' ; rw [<-l₂] at l₂' ; rw [<-l₃] at l₃'
      simp only [l₁',l₂',l₃']
      tauto

instance : IsEquiv (Triangle P) IsCongr where
  refl := IsCongr.refl
  symm := IsCongr.symm
  trans := IsCongr.trans

end IsCongr

/- Anti-congruence -/
def IsACongr (tr₁ tr₂: Triangle P) : Prop := by
  by_cases tr₁.isND ∧ tr₂.isND
  · let tr_nd₁ : TriangleND P := ⟨tr₁, h.1⟩
    let tr_nd₂ : TriangleND P := ⟨tr₂, h.2⟩
    exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length ∧ tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value ∧ tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value ∧ tr_nd₁.angle₃.value = - tr_nd₂.angle₃.value
  · exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length

scoped infix : 50 " IsACongrTo " => IsACongr

-- scoped infix : 50 " ≅ₐ " => IsACongr --do we need?

namespace IsACongr

section triangle

variable (tr₁ tr₂: Triangle P) (h : tr₁ IsACongrTo tr₂)

theorem isND: tr₁.isND ↔ tr₂.isND := by
  rw [IsACongr] at h
  constructor
  · intro nd₁
    by_contra nd_2
    have notnd : ¬ (Triangle.isND tr₁ ∧ Triangle.isND tr₂) := by
      push_neg
      intro _
      exact nd_2
    unfold Triangle.isND at nd_2
    push_neg at nd_2
    have sum := (Triangle.edge_sum_eq_edge_iff_colinear tr₂).mp nd_2
    simp only [dif_neg notnd] at h
    rcases h with ⟨h₁,⟨h₂,h₃⟩⟩
    rw [← h₁,← h₂,← h₃] at sum
    have nd_1 := (Triangle.edge_sum_eq_edge_iff_colinear tr₁).mpr sum
    unfold Triangle.isND at nd₁
    exact nd₁ nd_1
  · intro nd₂
    by_contra nd_1
    have notnd : ¬ (Triangle.isND tr₁ ∧ Triangle.isND tr₂) := by
      push_neg
      intro nd₁
      exfalso
      exact nd_1 nd₁
    unfold Triangle.isND at nd_1
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
  by_cases nd : (tr₁.isND ∧ tr₂.isND)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨s₁,_⟩
    exact s₁
  · simp only [nd, dite_false, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨t₁,_⟩
    exact t₁

theorem edge₂ : tr₁.edge₂.length = tr₂.edge₂.length := by
  rw [IsACongr] at h
  have h' := eq_true h
  by_cases nd : (tr₁.isND ∧ tr₂.isND)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨s₂,_⟩⟩
    exact s₂
  · simp only [nd, dite_false, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨t₂,_⟩⟩
    exact t₂

theorem edge₃ : tr₁.edge₃.length = tr₂.edge₃.length := by
  rw [IsACongr] at h
  have h' := eq_true h
  by_cases nd : (tr₁.isND ∧ tr₂.isND)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨_,⟨s₃,_⟩⟩⟩
    exact s₃
  · simp only [nd, dite_false, eq_iff_iff, iff_true] at h'
    rcases h' with ⟨_,⟨_,t₃⟩⟩
    exact t₃

end triangle

section triangle_nd

variable (tr_nd₁ tr_nd₂: TriangleND P) (h : tr_nd₁.1 IsACongrTo tr_nd₂.1)

theorem angle₁.value : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value := by
  rw [IsACongr] at h
  have i : Triangle.isND tr_nd₁.1 ∧ Triangle.isND tr_nd₂.1 := by constructor ; exact tr_nd₁.2 ; exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h
  rcases h with ⟨_,⟨_,⟨_,⟨h₄,_⟩⟩⟩⟩
  exact h₄

theorem angle₂.value : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value := by
  rw [IsACongr] at h
  have i : Triangle.isND tr_nd₁.1 ∧ Triangle.isND tr_nd₂.1 := by constructor ; exact tr_nd₁.2 ; exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h
  rcases h with ⟨_,⟨_,⟨_,⟨_,⟨h₅,_⟩⟩⟩⟩⟩
  exact h₅

theorem angle₃.value : tr_nd₁.angle₃.value = - tr_nd₂.angle₃.value := by
  rw [IsACongr] at h
  have i : Triangle.isND tr_nd₁.1 ∧ Triangle.isND tr_nd₂.1 := by constructor ; exact tr_nd₁.2 ; exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h
  rcases h with ⟨_,⟨_,⟨_,⟨_,⟨_,h₆⟩⟩⟩⟩⟩
  exact h₆

theorem is_cclock : tr_nd₁.is_cclock = ¬ tr_nd₂.is_cclock := by
  rw [IsACongr] at h
  simp [tr_nd₁.2,tr_nd₂.2] at h
  rcases h with ⟨_,_,_,a₁,a₂,a₃⟩
  by_cases cclock₁ : TriangleND.is_cclock tr_nd₁
  . have a := tr_nd₁.angle_pos_of_cclock cclock₁
    simp only [a₁,a₂,a₃] at a
    have b := tr_nd₂.clock_of_neg_angle
    rcases a with ⟨nonneg_a₁,_,_⟩
    simp only [cclock₁,eq_iff_iff, true_iff]
    apply b ; left ; simp only [Left.neg_pos_iff] at nonneg_a₁ ;exact nonneg_a₁
  . have a := tr_nd₁.angle_neg_of_clock cclock₁
    simp only [a₁,a₂,a₃] at a
    have b := tr_nd₂.cclock_of_pos_angle
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

theorem triv_of_acongr_self (h : tr IsACongrTo tr) : ¬ tr.isND := by
   rw [IsACongr] at h
   by_contra nd
   let tr_nd : TriangleND P := ⟨tr,nd⟩
   simp only [nd, and_self, true_and, dite_true] at h
   rcases h with ⟨anti_angle,_⟩
   have eq_zero : Angle.value tr_nd.angle₁ = 0 := by linarith
   unfold TriangleND.angle₁ at eq_zero
   have col := colinear_of_zero_angle eq_zero
   unfold Triangle.isND at nd
   apply nd ; exact col

protected theorem symm (h : tr₁ IsACongrTo tr₂) : tr₂ IsACongrTo tr₁ := by
  by_cases nd₁:Triangle.isND tr₁
  · have nd₂ := (isND tr₁ tr₂) h
    rw [eq_true nd₁] at nd₂
    simp only [true_iff] at nd₂
    have nd : Triangle.isND tr₁ ∧ Triangle.isND tr₂ := by
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
    have nd_2 := (isND tr₁ tr₂) h
    rw [eq_false nd₁] at nd_2
    simp at nd_2
    have nd : ¬ (Triangle.isND tr₁ ∧ Triangle.isND tr₂) := by
      push_neg
      intro nd₁
      exfalso
      exact nd_1 nd₁
    rw [IsACongr] at h
    simp only [nd,dite_false] at h
    have nd' : ¬ (Triangle.isND tr₂ ∧ Triangle.isND tr₁) := by
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
    by_cases nd₁ : tr₁.isND
    . have nd₂ : tr₁.isND ↔ tr₂.isND := by apply IsACongr.isND tr₁ tr₂ h₁
      simp only [nd₁, true_iff] at nd₂
      have nd₃ : tr₂.isND ↔ tr₃.isND := by apply IsACongr.isND tr₂ tr₃ h₂
      simp only [nd₂, true_iff] at nd₃
      simp only [nd₁, nd₂, and_self, dite_true] at h₁
      simp only [nd₂, nd₃, and_self, dite_true] at h₂
      simp only [nd₁, nd₃, and_self, dite_true]
      rcases h₁ with ⟨l₁,l₂,l₃,a₁,a₂,a₃⟩
      rcases h₂ with ⟨l₁',l₂',l₃',a₁',a₂',a₃'⟩
      rw [<-l₁] at l₁' ; rw [<-l₂] at l₂' ; rw [<-l₃] at l₃' ; rw[ neg_eq_iff_eq_neg.mpr a₁'] at a₁ ; rw[neg_eq_iff_eq_neg.mpr a₂'] at a₂ ; rw[neg_eq_iff_eq_neg.mpr a₃'] at a₃
      simp only [l₁',l₂',l₃',a₁,a₂,a₃]
      tauto
    . have nd₂ : tr₁.isND ↔ tr₂.isND := by apply IsACongr.isND tr₁ tr₂ h₁
      simp [nd₁] at nd₂
      have nd₃ : tr₂.isND ↔ tr₃.isND := by apply IsACongr.isND tr₂ tr₃ h₂
      simp only [nd₂, false_iff] at nd₃
      simp only [nd₁, nd₂, and_self, dite_false] at h₁
      simp only [nd₂, nd₃, and_self, dite_false] at h₂
      simp only [nd₁, nd₃, and_self, dite_false]
      rcases h₁ with ⟨l₁,l₂,l₃⟩
      rcases h₂ with ⟨l₁',l₂',l₃'⟩
      rw [<-l₁] at l₁' ; rw [<-l₂] at l₂' ; rw [<-l₃] at l₃'
      simp only [l₁',l₂',l₃']
      tauto

instance : IsSymm (Triangle P) IsACongr where
  symm := IsACongr.symm

end IsACongr


section criteria
/-
criteria of congruence of triangles. each SAS ASA AAS SSS involves congr and anti congr. SSS is special.
Need a tactic `Congrence` to consider filp and permutation. -/

variable {tr_nd₁ tr_nd₂ : TriangleND P}

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
theorem congr_of_AAS (a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value) (a₂ : tr_nd₁.angle₂.value = tr_nd₂.angle₂.value) (e₃ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) : tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

theorem acongr_of_AAS (a₁ : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value) (a₂ : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value) (e₃ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) : tr_nd₁.1 IsACongrTo tr_nd₂.1 := sorry

/- SSS -/
/- cannot decide orientation -/
theorem cosine_eq_of_SSS (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) : Real.cos tr_nd₁.angle₁.value = Real.cos tr_nd₂.angle₁.value:= by
  have cos₁ : 2 * (tr_nd₁.1.edge₃.length * tr_nd₁.1.edge₂.length * Real.cos tr_nd₁.angle₁.value) = tr_nd₁.1.edge₃.length ^ 2 + tr_nd₁.1.edge₂.length ^ 2 - tr_nd₁.1.edge₁.length^2 := Triangle.cosine_rule tr_nd₁
  have cos₂ : 2 * (tr_nd₂.1.edge₃.length * tr_nd₂.1.edge₂.length * Real.cos tr_nd₂.angle₁.value) = tr_nd₂.1.edge₃.length ^ 2 + tr_nd₂.1.edge₂.length ^ 2 - tr_nd₂.1.edge₁.length^2 := Triangle.cosine_rule tr_nd₂
  rw [e₁,e₂,e₃,←cos₂] at cos₁
  field_simp at cos₁
  have u₁ : 0 < tr_nd₂.1.edge₃.length := by
    exact length_pos_iff_nd.mpr tr_nd₂.edge_nd₃.2
  have u₂ : 0 < tr_nd₂.1.edge₂.length := by
    exact length_pos_iff_nd.mpr tr_nd₂.edge_nd₂.2
  have h0 : (tr_nd₂.1.edge₃.length * tr_nd₂.1.edge₂.length) > 0 := by
    field_simp [u₁,u₂]
  rcases cos₁ with x | y
  ·apply x
  ·have h1 : ¬((tr_nd₂.1.edge₃.length * tr_nd₂.1.edge₂.length)) = 0 := ne_of_gt h0
   absurd h1 y
   exact False.elim (h1 y)

theorem congr_of_SSS_of_eq_orientation (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) (c : tr_nd₁.is_cclock ↔ tr_nd₂.is_cclock) : tr_nd₁.1 IsCongrTo tr_nd₂.1 := by
  have a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value := by
    exact angle_eq_of_cosine_eq_of_cclock c (cosine_eq_of_SSS e₁ e₂ e₃)
  have a₂ : tr_nd₁.angle₂.value = tr_nd₂.angle₂.value := by
    let pptr_nd₁ := tr_nd₁.perm_vertices.perm_vertices
    let pptr_nd₂ := tr_nd₂.perm_vertices.perm_vertices
    have ppe₁ : pptr_nd₁.1.edge₁.length = pptr_nd₂.1.edge₁.length := by
      simp
      rw [←(TriangleND.edge_eq_edge_of_perm_vertices_two_times tr_nd₁).2.1,←(TriangleND.edge_eq_edge_of_perm_vertices_two_times tr_nd₂).2.1]
      exact e₂
    have ppe₂ : pptr_nd₁.1.edge₂.length = pptr_nd₂.1.edge₂.length := by
      simp
      rw [←(TriangleND.edge_eq_edge_of_perm_vertices_two_times tr_nd₁).2.2,←(TriangleND.edge_eq_edge_of_perm_vertices_two_times tr_nd₂).2.2]
      exact e₃
    have ppe₃ : pptr_nd₁.1.edge₃.length = pptr_nd₂.1.edge₃.length := by
      simp
      rw [←(TriangleND.edge_eq_edge_of_perm_vertices_two_times tr_nd₁).1,←(TriangleND.edge_eq_edge_of_perm_vertices_two_times tr_nd₂).1]
      exact e₁
    have ppc : pptr_nd₁.is_cclock ↔ pptr_nd₂.is_cclock := by
      rw [←TriangleND.same_orient_of_perm_vertices,←TriangleND.same_orient_of_perm_vertices,←TriangleND.same_orient_of_perm_vertices,←TriangleND.same_orient_of_perm_vertices]
      exact c
    have ppa₁ : pptr_nd₁.angle₁.value = pptr_nd₂.angle₁.value := by
      exact angle_eq_of_cosine_eq_of_cclock ppc (cosine_eq_of_SSS ppe₁ ppe₂ ppe₃)
    rw [←(TriangleND.angle_eq_angle_of_perm_vertices_two_times tr_nd₁).2.1,←(TriangleND.angle_eq_angle_of_perm_vertices_two_times tr_nd₂).2.1] at ppa₁
    exact ppa₁
  have a₃ : tr_nd₁.angle₃.value = tr_nd₂.angle₃.value := by
    let ptr_nd₁ := tr_nd₁.perm_vertices
    let ptr_nd₂ := tr_nd₂.perm_vertices
    have pe₁ : ptr_nd₁.edge₁.length = ptr_nd₂.edge₁.length := by
      simp
      rw [←(TriangleND.edge_eq_edge_of_perm_vertices tr_nd₁).2.2,←(TriangleND.edge_eq_edge_of_perm_vertices tr_nd₂).2.2]
      exact e₃
    have pe₂ : ptr_nd₁.edge₂.length = ptr_nd₂.edge₂.length := by
      simp
      rw [←(TriangleND.edge_eq_edge_of_perm_vertices tr_nd₁).1,←(TriangleND.edge_eq_edge_of_perm_vertices tr_nd₂).1]
      exact e₁
    have pe₃ : ptr_nd₁.edge₃.length = ptr_nd₂.edge₃.length := by
      simp
      rw [←(TriangleND.edge_eq_edge_of_perm_vertices tr_nd₁).2.1,←(TriangleND.edge_eq_edge_of_perm_vertices tr_nd₂).2.1]
      exact e₂
    have pc : ptr_nd₁.is_cclock ↔ ptr_nd₂.is_cclock := by
      rw [←TriangleND.same_orient_of_perm_vertices,←TriangleND.same_orient_of_perm_vertices]
      exact c
    have pa₁ : ptr_nd₁.angle₁.value = ptr_nd₂.angle₁.value := by
      exact angle_eq_of_cosine_eq_of_cclock pc (cosine_eq_of_SSS pe₁ pe₂ pe₃)
    rw [←(TriangleND.angle_eq_angle_of_perm_vertices tr_nd₁).2.2,←(TriangleND.angle_eq_angle_of_perm_vertices tr_nd₂).2.2] at pa₁
    exact pa₁
  have final : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length ∧ tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length ∧tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length ∧ tr_nd₁.angle₁.value = tr_nd₂.angle₁.value ∧ tr_nd₁.angle₂.value = tr_nd₂.angle₂.value ∧ tr_nd₁.angle₃.value = tr_nd₂.angle₃.value := ⟨e₁,e₂,e₃,a₁,a₂,a₃⟩
  have h0 : tr_nd₁.1.isND ∧ tr_nd₂.1.isND := ⟨tr_nd₁.2,tr_nd₂.2⟩
  have k : (tr_nd₁.1 IsCongrTo tr_nd₂.1) = True := by
    dsimp only [IsCongr]
    rw [dite_eq_iff]
    left
    use h0
    rw[←iff_eq_eq,iff_true]
    apply final
  rw[←iff_eq_eq,iff_true] at k
  apply k

theorem acongr_of_SSS_of_ne_orientation (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) (c : tr_nd₁.is_cclock = ¬ tr_nd₂.is_cclock) : tr_nd₁.1 IsACongrTo tr_nd₂.1 := sorry

theorem congr_or_acongr_of_SSS (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length): tr_nd₁.1 IsCongrTo tr_nd₂.1 ∨ tr_nd₁.1 IsACongrTo tr_nd₂.1 := sorry

end criteria

end EuclidGeom
