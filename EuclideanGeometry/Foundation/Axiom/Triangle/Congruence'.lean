import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex2

namespace EuclidGeom

/- definition of congruence of triangles-/

/- congruences of triangles, separate definitions for reversing orientation or not, (requiring all sides and angles being the same)-/

variable {P : Type _} [EuclideanPlane P] {tr tr₁ tr₂ tr₃ : Triangle P} {tr_nd tr_nd₁ tr_nd₂ : Triangle_nd P}

open Classical

-- Do not change `IsCongr, IsACongr` notation into `≅, ≅ₐ` in any theorem with name  `IsCongr.some_theorem, IsACongr.some_theorem`, to use `h.some_theorem` when h is of shape `tr₁ ≅ tr₂`.
namespace Triangle

structure IsCongr (tr₁ tr₂ : Triangle P) : Prop where intro ::
  edge₁ : tr₁.edge₁.length = tr₂.edge₁.length
  edge₂ : tr₁.edge₂.length = tr₂.edge₂.length
  edge₃ : tr₁.edge₃.length = tr₂.edge₃.length
  angle₁ : if h : tr₁.is_nd ∧ tr₂.is_nd then
    (Triangle_nd.angle₁ ⟨tr₁, h.1⟩).value = (Triangle_nd.angle₁ ⟨tr₂, h.2⟩).value
    else True
  angle₂ : if h : tr₁.is_nd ∧ tr₂.is_nd then
    (Triangle_nd.angle₂ ⟨tr₁, h.1⟩).value = (Triangle_nd.angle₂ ⟨tr₂, h.2⟩).value
    else True
  angle₃ : if h : tr₁.is_nd ∧ tr₂.is_nd then
    (Triangle_nd.angle₃ ⟨tr₁, h.1⟩).value = (Triangle_nd.angle₃ ⟨tr₂, h.2⟩).value
    else True

namespace IsCongr

protected theorem refl (tr : Triangle P) : tr.IsCongr tr where
  edge₁ := rfl
  edge₂ := rfl
  edge₃ := rfl
  angle₁ := (dite_prop_iff_and _).mpr ⟨fun _ ↦ rfl, fun _ ↦ trivial⟩
  angle₂ := (dite_prop_iff_and _).mpr ⟨fun _ ↦ rfl, fun _ ↦ trivial⟩
  angle₃ := (dite_prop_iff_and _).mpr ⟨fun _ ↦ rfl, fun _ ↦ trivial⟩

protected theorem symm (h : tr₁.IsCongr tr₂) : tr₂.IsCongr tr₁ where
  edge₁ := h.1.symm
  edge₂ := h.2.symm
  edge₃ := h.3.symm
  angle₁ := (dite_prop_iff_and _).mpr ⟨fun c ↦ (((dite_prop_iff_and _).mp h.4).1 c.symm).symm, fun _ ↦ trivial⟩
  angle₂ := (dite_prop_iff_and _).mpr ⟨fun c ↦ (((dite_prop_iff_and _).mp h.5).1 c.symm).symm, fun _ ↦ trivial⟩
  angle₃ := (dite_prop_iff_and _).mpr ⟨fun c ↦ (((dite_prop_iff_and _).mp h.6).1 c.symm).symm, fun _ ↦ trivial⟩

protected theorem trans (h₁ : tr₁.IsCongr tr₂) (h₂ : tr₂.IsCongr tr₃) : tr₁.IsCongr tr₃ := sorry

instance instHasCongr : HasCongr (Triangle P) where
  congr := IsCongr
  refl := IsCongr.refl
  symm := IsCongr.symm
  trans := IsCongr.trans

theorem is_nd_of_nd (h : tr₁.IsCongr tr₂) (nd : tr₁.is_nd) : tr₂.is_nd := sorry

theorem area (h : tr₁.IsCongr tr₂) : tr₁.area = tr₂.area := sorry

end IsCongr

structure IsACongr (tr₁ tr₂ : Triangle P) : Prop where intro ::
  edge₁ : tr₁.edge₁.length = tr₂.edge₁.length
  edge₂ : tr₁.edge₂.length = tr₂.edge₂.length
  edge₃ : tr₁.edge₃.length = tr₂.edge₃.length
  angle₁ : if h : tr₁.is_nd ∧ tr₂.is_nd then
    (Triangle_nd.angle₁ ⟨tr₁, h.1⟩).value = - (Triangle_nd.angle₁ ⟨tr₂, h.2⟩).value
    else True
  angle₂ : if h : tr₁.is_nd ∧ tr₂.is_nd then
    (Triangle_nd.angle₂ ⟨tr₁, h.1⟩).value = - (Triangle_nd.angle₂ ⟨tr₂, h.2⟩).value
    else True
  angle₃ : if h : tr₁.is_nd ∧ tr₂.is_nd then
    (Triangle_nd.angle₃ ⟨tr₁, h.1⟩).value = - (Triangle_nd.angle₃ ⟨tr₂, h.2⟩).value
    else True

namespace IsACongr

theorem is_nd_of_nd (h : tr₁.IsACongr tr₂) (nd : tr₁.is_nd) : tr₂.is_nd := sorry

protected theorem symm (h : tr₁.IsACongr tr₂) : tr₂.IsACongr tr₁ := sorry

theorem congr_of_trans_acongr (h₁ : tr₁.IsACongr tr₂) (h₂ : tr₂.IsACongr tr₃) : tr₁.IsCongr tr₃ := sorry

instance instHasACongr : HasACongr (Triangle P) where
  acongr := IsACongr
  symm := IsACongr.symm

end IsACongr

end Triangle

namespace Triangle_nd

structure IsCongr (tr_nd₁ tr_nd₂ : Triangle_nd P) : Prop where intro ::
  edge₁ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length
  edge₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length
  edge₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length
  angle₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value
  angle₂ : tr_nd₁.angle₂.value = tr_nd₂.angle₂.value
  angle₃ : tr_nd₁.angle₃.value = tr_nd₂.angle₃.value

namespace IsCongr

protected theorem refl (tr_nd : Triangle_nd P) : tr_nd.IsCongr tr_nd := sorry

protected theorem symm (h : tr_nd₁.IsCongr tr_nd₂) : tr_nd₂.IsCongr tr_nd₁ := sorry

protected theorem trans (h₁ : tr_nd₁.IsCongr tr_nd₂) (h₂ : tr_nd₂.IsCongr tr_nd₃) : tr_nd₁.IsCongr tr_nd₃ := sorry

instance instHasCongr : HasCongr (Triangle_nd P) where
  congr := IsCongr
  refl := IsCongr.refl
  symm := IsCongr.symm
  trans := IsCongr.trans

theorem is_cclock_of_cclock (h : tr_nd₁.IsCongr tr_nd₂) (cc : tr_nd₁.is_cclock) : tr_nd₂.is_cclock := sorry

theorem area (h : tr_nd₁.IsCongr tr_nd₂) : tr_nd₁.area = tr_nd₂.area := sorry

end IsCongr

structure IsACongr (tr_nd₁ tr_nd₂: Triangle_nd P) : Prop where intro ::
  edge₁ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length
  edge₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length
  edge₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length
  angle₁ : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value
  angle₂ : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value
  angle₃ : tr_nd₁.angle₃.value = - tr_nd₂.angle₃.value

namespace IsACongr

theorem not_cclock_of_cclock (h : tr_nd₁.IsACongr tr_nd₂) (cc : tr_nd₁.is_cclock) : ¬ tr_nd₂.is_cclock := sorry

protected theorem symm (h : tr_nd₁.IsACongr tr_nd₂) : tr_nd₂.IsACongr tr_nd₁ := sorry

theorem congr_of_trans_acongr (h₁ : tr_nd₁.IsACongr tr_nd₂) (h₂ : tr_nd₂.IsACongr tr_nd₃) : tr_nd₁.IsACongr tr_nd₃ := sorry

instance instHasACongr : HasACongr (Triangle_nd P) where
  acongr := IsACongr
  symm := IsACongr.symm

end IsACongr

end Triangle_nd

section compatibility

theorem Triangle.congr_of_congr (h : tr_nd₁ ≅ tr_nd₂) : tr_nd₁.1 ≅ tr_nd₂.1 := sorry

theorem Triangle.nd_of_congr (h : tr_nd.1 ≅ tr) : tr.is_nd := sorry

theorem Triangle_nd.congr_of_congr (h : tr_nd.1 ≅ tr) : tr_nd ≅ ⟨tr, tr.nd_of_congr h⟩ := sorry

end compatibility

namespace Triangle

section degenerate

theorem IsCongr.not_nd_of_not_nd (h : tr₁ ≅ tr₂) (nnd : ¬ tr₁.is_nd) : ¬ tr₂.is_nd :=
  fun nd ↦ nnd (h.symm.is_nd_of_nd nd)

theorem IsACongr.not_nd_of_not_nd (h : tr₁.IsACongr tr₂) (nnd : ¬ tr₁.is_nd) : ¬ tr₂.is_nd :=
  fun nd ↦ nnd (h.symm.is_nd_of_nd nd)

theorem triv_of_acongr_self (h : tr.IsACongr tr) : ¬ tr.is_nd := sorry

theorem acongr_self_of_triv (nnd : ¬ tr.is_nd) : tr.IsACongr tr := sorry

theorem IsCongr.acongr_of_left_triv (h : tr₁.IsCongr tr₂) (nnd : ¬ tr₁.is_nd) : tr₁.IsACongr tr₂ := sorry

theorem IsCongr.acongr_of_right_triv (h : tr₁.IsCongr tr₂) (nnd : ¬ tr₂.is_nd) : tr₁.IsACongr tr₂ := sorry

theorem IsACongr.congr_of_left_triv (h : tr₁.IsACongr tr₂) (nnd : ¬ tr₁.is_nd) : tr₁.IsCongr tr₂ := sorry

theorem IsACongr.congr_of_right_triv (h : tr₁.IsACongr tr₂) (nnd : ¬ tr₂.is_nd) : tr₁.IsCongr tr₂ := sorry

end degenerate

end Triangle

section criteria
/- criteria of congruence of triangles. each SAS ASA AAS SSS involves congr and anti congr. SSS is special.
Need a tactic `Congrence` to consider filp and permutation. -/

namespace Triangle_nd

/- SAS -/
theorem congr_of_SAS (e₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length) (a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value) (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) : tr_nd₁ ≅ tr_nd₂ := sorry

theorem acongr_of_SAS (e₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length) (a₁ : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value) (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) : tr_nd₁ ≅ₐ tr_nd₂ := sorry

/- ASA -/
theorem congr_of_ASA (a₂ : tr_nd₁.angle₂.value = tr_nd₂.angle₂.value) (e₁ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length) (a₃ : tr_nd₁.angle₃.value = tr_nd₂.angle₃.value) : tr_nd₁ ≅ tr_nd₂ := sorry

theorem acongr_of_ASA (a₂ : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value) (e₁ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length) (a₃ : tr_nd₁.angle₃.value = - tr_nd₂.angle₃.value) : tr_nd₁ ≅ₐ tr_nd₂ := sorry

/- AAS -/
theorem congr_of_AAS (a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value) (a₂ : tr_nd₁.angle₂.value = tr_nd₂.angle₂.value) (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) : tr_nd₁ ≅ tr_nd₂ := sorry

theorem acongr_of_AAS (a₁ : tr_nd₁.angle₁.value = - tr_nd₂.angle₁.value) (a₂ : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value) (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) : tr_nd₁ ≅ₐ tr_nd₂ := sorry

/- HL -/
theorem congr_of_HL (h₁ : tr_nd₁.angle₁.value = π / 2) (h₂ : tr_nd₂.angle₁.value = π / 2) (e₁ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length) (e₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length) : tr_nd₁ ≅ tr_nd₂ := sorry

theorem acongr_of_HL (h₁ : tr_nd₁.angle₁.value = π / 2) (h₂ : tr_nd₂.angle₁.value = - π / 2) (e₁ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length) (e₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length) : tr_nd₁ ≅ₐ tr_nd₂ := sorry

/- SSS -/
/- cannot decide orientation -/
theorem congr_of_SSS_of_eq_orientation (e₁ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length) (e₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length) (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) (c : tr_nd₁.is_cclock = tr_nd₂.is_cclock) : tr_nd₁ ≅ tr_nd₂ := sorry

theorem acongr_of_SSS_of_ne_orientation (e₁ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length) (e₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length) (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) (c : tr_nd₁.is_cclock = ¬ tr_nd₂.is_cclock) : tr_nd₁ ≅ₐ tr_nd₂ := sorry

theorem congr_or_acongr_of_SSS (e₁ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length) (e₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length) (e₃ : tr_nd₁.edge₃.length = tr_nd₂.edge₃.length) : tr_nd₁ ≅ tr_nd₂ ∨ tr_nd₁ ≅ₐ tr_nd₂ := sorry

end Triangle_nd

namespace Triangle

theorem congr_of_SSS_of_left_triv (e₁ : tr₁.edge₁.length = tr₂.edge₁.length) (e₂ : tr₁.edge₂.length = tr₂.edge₂.length) (e₃ : tr₁.edge₃.length = tr₂.edge₃.length) (nnd : ¬ tr₁.is_nd) : tr₁ ≅ tr₂ := sorry

theorem congr_of_SSS_of_right_triv (e₁ : tr₁.edge₁.length = tr₂.edge₁.length) (e₂ : tr₁.edge₂.length = tr₂.edge₂.length) (e₃ : tr₁.edge₃.length = tr₂.edge₃.length) (nnd : ¬ tr₂.is_nd) : tr₁ ≅ tr₂ := sorry

theorem acongr_of_SSS_of_left_triv (e₁ : tr₁.edge₁.length = tr₂.edge₁.length) (e₂ : tr₁.edge₂.length = tr₂.edge₂.length) (e₃ : tr₁.edge₃.length = tr₂.edge₃.length) (nnd : ¬ tr₁.is_nd) : tr₁ ≅ₐ tr₂ :=
  (congr_of_SSS_of_left_triv e₁ e₂ e₃ nnd).acongr_of_left_triv nnd

theorem acongr_of_SSS_of_right_triv (e₁ : tr₁.edge₁.length = tr₂.edge₁.length) (e₂ : tr₁.edge₂.length = tr₂.edge₂.length) (e₃ : tr₁.edge₃.length = tr₂.edge₃.length) (nnd : ¬ tr₂.is_nd) : tr₁ ≅ₐ tr₂ :=
  (congr_of_SSS_of_right_triv e₁ e₂ e₃ nnd).acongr_of_right_triv nnd

theorem congr_or_acongr_of_SSS (e₁ : tr₁.edge₁.length = tr₂.edge₁.length) (e₂ : tr₁.edge₂.length = tr₂.edge₂.length) (e₃ : tr₁.edge₃.length = tr₂.edge₃.length) : tr₁ ≅ tr₂ ∨ tr₁ ≅ₐ tr₂ := sorry

end Triangle

end criteria

end EuclidGeom
