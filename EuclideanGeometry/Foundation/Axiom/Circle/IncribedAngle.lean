import EuclideanGeometry.Foundation.Axiom.Circle.Basic

noncomputable section
namespace EuclidGeom

@[ext]
structure Arc (P : Type _) [EuclideanPlane P] where
  source : P
  target : P
  circle : Circle P
  center : P
  ison : (source LiesOn circle) ∧ (target LiesOn circle)
  endpts_ne : target ≠ source

variable {P : Type _} [EuclideanPlane P]

namespace Arc

def mk_pt_pt_circle (A B : P) {ω : Circle P} (h : B ≠ A) (ha : A LiesOn ω) (hb : B LiesOn ω) : Arc P where
  source := A
  target := B
  circle := ω
  center := ω.center
  ison := ⟨ha, hb⟩
  endpts_ne := h

end Arc

scoped notation "ARC" => Arc.mk_pt_pt_circle


section position

namespace Arc

protected def IsOn (p : P) (β : Arc P) : Prop := (p LiesOn β.circle) ∧ (¬ p LiesOnLeft (RAY β.source β.target β.endpts_ne))

def Isnot_arc_endpts (p : P) (β : Arc P) : Prop := (p ≠ β.source) ∧ (p ≠ β.target)

protected def IsInt (p : P) (β : Arc P) : Prop := (Arc.IsOn p β) ∧ (Isnot_arc_endpts p β)

protected def carrier (β : Arc P) : Set P := { p : P | Arc.IsOn p β }

protected def interior (β : Arc P) : Set P := { p : P | Arc.IsInt p β }

instance : Fig Arc where
  carrier := Arc.carrier

instance : Interior Arc where
  interior := Arc.interior

def complement (β : Arc P) : Arc P where
  source := β.target
  target := β.source
  circle := β.circle
  center := β.center
  ison := and_comm.mp β.ison
  endpts_ne := β.endpts_ne.symm

end Arc

end position


section angle

namespace Arc

def angle_mk_pt_arc (p : P) (β : Arc P) (h : Isnot_arc_endpts p β) : Angle P := ANG β.source p β.target h.1.symm h.2.symm

def InAngle (p : P) (β : Arc P) (h₁ : Isnot_arc_endpts p β) (h₂ : p LiesOn β.circle) : Angle P := angle_mk_pt_arc p β h₁

end Arc

end angle

end EuclidGeom
