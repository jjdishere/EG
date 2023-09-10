import EuclideanGeometry.Foundation.Axiom.Triangle

namespace EuclidGeom

/- definition of congruence of triangles-/

/- congruences of triangles, separate definitions for reversing orientation or not, (requiring all sides and angles being the same)-/

variable {P : Type _} [EuclideanPlane P]

def IsCongr (tr₁ tr₂: Triangle P) : Prop := by
  by_cases tr₁.is_nd ∧ tr₂.is_nd 
  · exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length ∧ tr₁.angle₁ h.1 = tr₂.angle₁ h.2 ∧ tr₁.angle₂ h.1 = tr₂.angle₂ h.2 ∧ tr₁.angle₃ h.1 = tr₂.angle₃ h.2
  · exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length

scoped infix : 50 "IsCongrTo" => IsCongr

scoped infix : 50 "≃" => IsCongr --do we need?

namespace IsCongr

variable (tr₁ tr₂: Triangle P) (h : tr₁ IsCongrTo tr₂)

theorem is_nd: tr₁.is_nd = tr₂.is_nd := sorry

theorem edge₁ : tr₁.edge₁.length = tr₂.edge₁.length := sorry

theorem edge₂ : tr₁.edge₂.length = tr₂.edge₂.length := sorry

theorem edge₃ : tr₁.edge₃.length = tr₂.edge₃.length := sorry

variable (nontriv₁ : tr₁.is_nd) (nontriv₂ : tr₂.is_nd)

theorem angle₁ : tr₁.angle₁ nontriv₁ = tr₂.angle₁ nontriv₂ := sorry

theorem angle₂ : tr₁.angle₂ nontriv₁ = tr₂.angle₂ nontriv₂ := sorry

theorem angle₃ : tr₁.angle₃ nontriv₁ = tr₂.angle₃ nontriv₂ := sorry

theorem is_cclock : tr₁.is_cclock nontriv₁ = tr₂.is_cclock nontriv₂ := sorry

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
  · exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length ∧ tr₁.angle₁ h.1 = - tr₂.angle₁ h.2 ∧ tr₁.angle₂ h.1 = - tr₂.angle₂ h.2 ∧ tr₁.angle₃ h.1 = - tr₂.angle₃ h.2
  · exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length

scoped infix : 50 "IsACongrTo" => IsACongr

scoped infix : 50 "≃ₐ" => IsACongr --do we need?

namespace IsACongr

variable (tr₁ tr₂: Triangle P) (h : tr₁ IsACongrTo tr₂)

theorem is_nd: tr₁.is_nd ↔ tr₂.is_nd := sorry

theorem edge₁ : tr₁.edge₁.length = tr₂.edge₁.length := sorry

theorem edge₂ : tr₁.edge₂.length = tr₂.edge₂.length := sorry

theorem edge₃ : tr₁.edge₃.length = tr₂.edge₃.length := sorry

variable (nontriv₁ : tr₁.is_nd) (nontriv₂ : tr₂.is_nd)

theorem angle₁ : tr₁.angle₁ nontriv₁ = - tr₂.angle₁ nontriv₂ := sorry

theorem angle₂ : tr₁.angle₂ nontriv₁ = - tr₂.angle₂ nontriv₂ := sorry

theorem angle₃ : tr₁.angle₃ nontriv₁ = - tr₂.angle₃ nontriv₂ := sorry

theorem is_cclock : tr₁.is_cclock nontriv₁ = ¬ tr₂.is_cclock nontriv₂ := sorry

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

variable {tr₁ tr₂ : Triangle P}

/- SAS -/
theorem congr_of_SAS {nontriv₁ : tr₁.is_nd} {nontriv₂ : tr₂.is_nd} (e₂ : tr₁.edge₂.length = tr₂.edge₂.length) (a₁ : tr₁.angle₁ nontriv₁ = tr₂.angle₁ nontriv₂) (e₃ : tr₁.edge₃.length = tr₂.edge₃.length): tr₁ IsCongrTo tr₂ := sorry 

theorem acongr_of_SAS {nontriv₁ : tr₁.is_nd} {nontriv₂ : tr₂.is_nd} (e₂ : tr₁.edge₂.length = tr₂.edge₂.length) (a₁ : tr₁.angle₁ nontriv₁ = - tr₂.angle₁ nontriv₂) (e₃ : tr₁.edge₃.length = tr₂.edge₃.length): tr₁ IsACongrTo tr₂ := sorry 

/- ASA -/
theorem congr_of_ASA {nontriv₁ : tr₁.is_nd} {nontriv₂ : tr₂.is_nd} (a₂ : tr₁.angle₂ nontriv₁ = tr₂.angle₂ nontriv₂) (e₁ : tr₁.edge₁.length = tr₂.edge₁.length) (a₃ : tr₁.angle₃ nontriv₁ = tr₂.angle₃ nontriv₂): tr₁ IsCongrTo tr₂ := sorry

theorem acongr_of_ASA {nontriv₁ : tr₁.is_nd} {nontriv₂ : tr₂.is_nd} (a₂ : tr₁.angle₂ nontriv₁ = - tr₂.angle₂ nontriv₂) (e₁ : tr₁.edge₁.length = tr₂.edge₁.length) (a₃ : tr₁.angle₃ nontriv₁ = - tr₂.angle₃ nontriv₂): tr₁ IsACongrTo tr₂ := sorry

/- AAS -/
theorem congr_of_AAS {nontriv₁ : tr₁.is_nd} {nontriv₂ : tr₂.is_nd} (a₁ : tr₁.angle₁ nontriv₁ = tr₂.angle₁ nontriv₂) (a₂ : tr₁.angle₂ nontriv₁ = tr₂.angle₂ nontriv₂) (e₃ : tr₁.edge₃.length = tr₂.edge₃.length) : tr₁ IsCongrTo tr₂ := sorry

theorem acongr_of_AAS {nontriv₁ : tr₁.is_nd} {nontriv₂ : tr₂.is_nd} (a₁ : tr₁.angle₁ nontriv₁ = - tr₂.angle₁ nontriv₂) (a₂ : tr₁.angle₂ nontriv₁ = - tr₂.angle₂ nontriv₂) (e₃ : tr₁.edge₃.length = tr₂.edge₃.length) : tr₁ IsACongrTo tr₂ := sorry

/- SSS -/ 
/- cannot decide orientation -/
theorem congr_or_acongr_of_SSS (e₁ : tr₁.edge₁.length = tr₂.edge₁.length) (e₂ : tr₁.edge₂.length = tr₂.edge₂.length) (e₃ : tr₁.edge₃.length = tr₂.edge₃.length): tr₁ IsCongrTo tr₂ ∨ tr₁ IsACongrTo tr₂  := sorry 

theorem congr_of_SSS_of_eq_orientation {nontriv₁ : tr₁.is_nd} {nontriv₂ : tr₂.is_nd} (e₁ : tr₁.edge₁.length = tr₂.edge₁.length) (e₂ : tr₁.edge₂.length = tr₂.edge₂.length) (e₃ : tr₁.edge₃.length = tr₂.edge₃.length) (c : tr₁.is_cclock nontriv₁ = tr₂.is_cclock nontriv₂): tr₁ IsCongrTo tr₂ := sorry 

theorem acongr_of_SSS_of_ne_orientation {nontriv₁ : tr₁.is_nd} {nontriv₂ : tr₂.is_nd} (e₁ : tr₁.edge₁.length = tr₂.edge₁.length) (e₂ : tr₁.edge₂.length = tr₂.edge₂.length) (e₃ : tr₁.edge₃.length = tr₂.edge₃.length) (c : tr₁.is_cclock nontriv₁ ≠ tr₂.is_cclock nontriv₂): tr₁ IsACongrTo tr₂ := sorry 

end criteria


end EuclidGeom