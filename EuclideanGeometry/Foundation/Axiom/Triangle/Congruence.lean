import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Trigonometric
open Classical

namespace EuclidGeom

/- definition of congruence of triangles-/

/- congruences of triangles, separate definitions for reversing orientation or not, (requiring all sides and angles being the same)-/

variable {P : Type _} [EuclideanPlane P]
-- only define congrence for Triangle_nd
--def IsCongr (tr_nd₁ tr_nd₂: Triangle_nd P) : Prop := (tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length ∧ tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length ∧ tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length ∧ tr_nd₁.angle₁ = tr_nd₂.angle₁ ∧ tr_nd₁.angle₂ = tr_nd₂.angle₂ ∧ tr_nd₁.angle₃ = tr_nd₂.angle₃)
def IsCongr (tr₁ tr₂: Triangle P) : Prop := by
  by_cases tr₁.is_nd ∧ tr₂.is_nd
  · let tr_nd₁ : Triangle_nd P := ⟨tr₁, h.1⟩
    let tr_nd₂ : Triangle_nd P := ⟨tr₂, h.2⟩
    exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length ∧ tr_nd₁.angle₁ = tr_nd₂.angle₁ ∧ tr_nd₁.angle₂ = tr_nd₂.angle₂ ∧ tr_nd₁.angle₃ = tr_nd₂.angle₃
  · exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length

scoped infix : 50 "IsCongrTo" => IsCongr

scoped infix : 50 "≅" => IsCongr --do we need?

namespace IsCongr

section triangle

variable (tr₁ tr₂: Triangle P) (h : tr₁ IsCongrTo tr₂)

theorem is_nd: tr₁.is_nd = tr₂.is_nd := sorry

theorem edge₁ : tr₁.edge₁.length = tr₂.edge₁.length := sorry

theorem edge₂ : tr₁.edge₂.length = tr₂.edge₂.length := sorry

theorem edge₃ : tr₁.edge₃.length = tr₂.edge₃.length := sorry

end triangle

section triangle_nd

variable (tr_nd₁ tr_nd₂: Triangle_nd P)

theorem angle₁ : tr_nd₁.angle₁ = tr_nd₂.angle₁ := sorry

theorem angle₂ : tr_nd₁.angle₂ = tr_nd₂.angle₂ := sorry

theorem angle₃ : tr_nd₁.angle₃ = tr_nd₂.angle₃ := sorry

theorem is_cclock : tr_nd₁.is_cclock = tr_nd₂.is_cclock := sorry

end triangle_nd

end IsCongr

namespace IsCongr

variable (tr tr₁ tr₂ tr₃: Triangle P)

protected theorem refl : tr IsCongrTo tr := sorry

protected theorem symm (h : tr₁ IsCongrTo tr₂) : tr₂ IsCongrTo tr₁ := sorry

protected theorem trans (h₁ : tr₁ IsCongrTo tr₂) (h₂ : tr₂ IsCongrTo tr₃) : tr₁ IsCongrTo tr₃ := sorry

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
    exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length ∧ tr_nd₁.angle₁ = - tr_nd₂.angle₁ ∧ tr_nd₁.angle₂ = - tr_nd₂.angle₂ ∧ tr_nd₁.angle₃ = - tr_nd₂.angle₃
  · exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length

scoped infix : 50 "IsACongrTo" => IsACongr

scoped infix : 50 "≅ₐ" => IsACongr --do we need?

namespace IsACongr

section triangle

variable (tr₁ tr₂: Triangle P) (h : tr₁ IsACongrTo tr₂)

theorem is_nd: tr₁.is_nd ↔ tr₂.is_nd := sorry

theorem edge₁ : tr₁.edge₁.length = tr₂.edge₁.length := sorry

theorem edge₂ : tr₁.edge₂.length = tr₂.edge₂.length := sorry

theorem edge₃ : tr₁.edge₃.length = tr₂.edge₃.length := sorry

end triangle

section triangle_nd

variable (tr_nd₁ tr_nd₂: Triangle_nd P) (h : tr_nd₁.1 IsACongrTo tr_nd₂.1)

theorem angle₁ : tr_nd₁.angle₁ = - tr_nd₂.angle₁ := sorry

theorem angle₂ : tr_nd₁.angle₂ = - tr_nd₂.angle₂ := sorry

theorem angle₃ : tr_nd₁.angle₃ = - tr_nd₂.angle₃ := sorry

theorem is_cclock : tr_nd₁.is_cclock = ¬ tr_nd₂.is_cclock := sorry

end triangle_nd

end IsACongr

namespace IsACongr

variable (tr tr₁ tr₂ tr₃: Triangle P) 

theorem triv_of_acongr_self (h : tr IsACongrTo tr) : ¬ tr.is_nd := sorry

protected theorem symm (h : tr₁ IsACongrTo tr₂) : tr₂ IsACongrTo tr₁ := sorry

theorem congr_of_trans_acongr (h₁ : tr₁ IsACongrTo tr₂) (h₂ : tr₂ IsACongrTo tr₃) : tr₁ IsCongrTo tr₃ := sorry

instance : IsSymm (Triangle P) IsACongr where
  symm := IsACongr.symm

end IsACongr


section criteria
/- 
criteria of congruence of triangles. each SAS ASA AAS SSS involves congr and anti congr. SSS is special.
Need a tactic `Congrence` to consider filp and permutation. -/

variable {tr_nd₁ tr_nd₂ : Triangle_nd P}

/- SAS -/
theorem congr_of_SAS (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (a₁ : tr_nd₁.angle₁ = tr_nd₂.angle₁) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length): tr_nd₁.1 IsCongrTo tr_nd₂.1 := by
  sorry

theorem acongr_of_SAS (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (a₁ : tr_nd₁.angle₁ = - tr_nd₂.angle₁) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length): tr_nd₁.1 IsACongrTo tr_nd₂.1 := sorry

/- ASA -/
theorem congr_of_ASA (a₂ : tr_nd₁.angle₂ = tr_nd₂.angle₂) (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (a₃ : tr_nd₁.angle₃ = tr_nd₂.angle₃): tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

theorem acongr_of_ASA (a₂ : tr_nd₁.angle₂ = - tr_nd₂.angle₂) (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (a₃ : tr_nd₁.angle₃ = - tr_nd₂.angle₃): tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

/- AAS -/
theorem congr_of_AAS (a₁ : tr_nd₁.angle₁ = tr_nd₂.angle₁) (a₂ : tr_nd₁.angle₂ = tr_nd₂.angle₂) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) : tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

theorem acongr_of_AAS (a₁ : tr_nd₁.angle₁ = - tr_nd₂.angle₁) (a₂ : tr_nd₁.angle₂ = - tr_nd₂.angle₂) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) : tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

/- SSS -/ 
/- cannot decide orientation -/--/
theorem cosine_eq_of_SSS (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) : Real.cos tr_nd₁.angle₁ = Real.cos tr_nd₂.angle₁:= by
  have cos₁ : 2 * (tr_nd₁.1.edge₃.length * tr_nd₁.1.edge₂.length * Real.cos tr_nd₁.angle₁) = tr_nd₁.1.edge₃.length ^ 2 + tr_nd₁.1.edge₂.length ^ 2 - tr_nd₁.1.edge₁.length^2 := Triangle.cosine_rule tr_nd₁
  have cos₂ : 2 * (tr_nd₂.1.edge₃.length * tr_nd₂.1.edge₂.length * Real.cos tr_nd₂.angle₁) = tr_nd₂.1.edge₃.length ^ 2 + tr_nd₂.1.edge₂.length ^ 2 - tr_nd₂.1.edge₁.length^2 := Triangle.cosine_rule tr_nd₂
  rw [e₁,e₂,e₃,←cos₂] at cos₁
  field_simp at cos₁
  have h0 : (tr_nd₂.1.edge₃.length * tr_nd₂.1.edge₂.length) > 0 := by
    field_simp [tr_nd₂.length_edge_ne_zero.1,tr_nd₂.length_edge_ne_zero.2]
  rcases cos₁ with x | y  
  ·apply x
  ·have h1 : ¬((tr_nd₂.1.edge₃.length * tr_nd₂.1.edge₂.length)) = 0 := ne_of_gt h0
   absurd h1 y
   exact False.elim (h1 y)

theorem congr_of_SSS_of_eq_orientation (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) (c : tr_nd₁.is_cclock ↔ tr_nd₂.is_cclock) : tr_nd₁.1 IsCongrTo tr_nd₂.1 := by
  have a₁ : tr_nd₁.angle₁ = tr_nd₂.angle₁ := by sorry
    --have g₁ : (0 < tr_nd₁.angle₁ ∧ 0 < tr_nd₂.angle₁) ∨ (tr_nd₁.--angle₁ < 0 ∧ tr_nd₂.angle₁ < 0) := by 
      --rw [Triangle.pos_pos_or_neg_neg_of_iff_cclock] at c
      --apply c
  have a₂ : tr_nd₁.angle₂ = tr_nd₂.angle₂ := sorry
  have a₃ : tr_nd₁.angle₃ = tr_nd₂.angle₃ := sorry
  have final : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length ∧ tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length ∧tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length ∧ tr_nd₁.angle₁ = tr_nd₂.angle₁ ∧ tr_nd₁.angle₂ = tr_nd₂.angle₂ ∧ tr_nd₁.angle₃ = tr_nd₂.angle₃ := ⟨e₁,e₂,e₃,a₁,a₂,a₃⟩  
  have h0 : tr_nd₁.1.is_nd ∧ tr_nd₂.1.is_nd := ⟨tr_nd₁.2,tr_nd₂.2⟩ 
  have k : (tr_nd₁.1 IsCongrTo tr_nd₂.1) = True := by 
    dsimp only [IsCongr] 
    rw [dite_eq_iff]
    left 
    use h0
    rw[←iff_eq_eq,iff_true]
    apply final
  rw[←iff_eq_eq,iff_true] at k
  apply k

theorem acongr_of_SSS_of_ne_orientation (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) (c : tr_nd₁.is_cclock ↔ ¬ tr_nd₂.is_cclock) : tr_nd₁.1 IsACongrTo tr_nd₂.1 := sorry

theorem congr_or_acongr_of_SSS (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length): tr_nd₁.1 IsCongrTo tr_nd₂.1 ∨ tr_nd₁.1 IsACongrTo tr_nd₂.1  := sorry

end criteria


end EuclidGeom