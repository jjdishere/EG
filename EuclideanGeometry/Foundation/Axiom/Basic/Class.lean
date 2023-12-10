import EuclideanGeometry.Foundation.Axiom.Basic.Plane

/-!
# Basic Classes in Euclidean Geometry

In this file, we define classes that will be used in Euclidean geometry. In this file, classes for carriers and classes for notations will be defined.

## Main Definitions

* `Fig` : The class of plane figures equipped with a carrier set.
* `Interior` : The class of plane figures with interior, further equipped with a interior set.
* `HasCongr` : The carrying class of the equivalent relation congruence.
* `HasACongr` : The carrying class of the symmetric relation anti-congruence.
* `HasSim` : The carrying class of the equivalent relation similarity.
* `HasASimr` : The carrying class of the symmetric relation anti-similarity.

## Notations

* `LiesOn` : A point belongs to the carrier of a specific figure.
* `LiesInt` : A point belongs to the interior of a specific figure.
* `IsInx` : A point belongs to both carrier of two specific figures.
* `InxWith` : The carriers of two figures have a common point.
* `IsCongrTo`, `≅` : the notation for congruence relation
* `IsACongrTo`, `≅ₐ` : the notation for anti-congruence relation
* `IsSimTo`, `∼` : the notation for similarity relation
* `IsASimTo`, `∼ₐ` : the notation for anti-similarity relation


## Further Works
1. The property `concurrent` (maybe we should extend to an arbitary number of figures version), the class `Convex_2D` is defined, but not actually in use.
2. Make `HasACongr` extends `HasCongr`, and requires transitivity relations between them in the class.

-/

/- define class of On and In and FallsOn, define LiesOn and IsIntersection, every geometric figure should be an instance of these classes -/


noncomputable section
namespace EuclidGeom

variable {P : Type*} {α β γ}

section carrier

/-- The class of plane figures. We say `α` is a plane figure, if for every given Euclidean plane `P`, `α P` is a collection of specific figures on `P`, each equipped with a carrier set of type `Set P`. -/
class Fig (α : Type*) (P : outParam <| Type*) where
  carrier : α → Set P

/-- The class of plane figures with interior. We say `α` is with interior, if for every given Euclidean plane `P`, each element in the collection `α P` is equipped with an interior set of type `Set P` -/
class Interior (α : Type*) (P : outParam <| Type*) where
  interior : α → Set P

/-- The class of plane figures with both carrier and interior. We say a plane figure `α` is with interior, if for every given Euclidean plane `P`, each element in the collection `α P` is equipped with bith a carrier set and an interior set of type `Set P`, and the interior set is contained in the carrier set. -/
class IntFig (α : Type*) (P : outParam <| Type*) extends Fig α P, Interior α P where
    interior_subset_carrier : ∀ (F : α), interior F ⊆ carrier F

def lies_on [Fig α P] (A : P) (F : α) : Prop := A ∈ (Fig.carrier F)

def lies_int [Interior α P] (A : P) (F : α) := A ∈ (Interior.interior F)

-- def lies_in [Interior α] (A : P) (F : α) : Prop := lies_int A F ∨ lies_on A F

scoped infix : 50 " LiesOn " => lies_on -- to make it work compatible with `∧`, binding power should > 35.
scoped infix : 50 " LiesInt " => lies_int
-- scoped infix : 50 "LiesIn" => lies_in

instance {P : Type*} [IntFig α P] (A : P) (F : α) : Coe (A LiesInt F) (A LiesOn F) where
  coe h := (IntFig.interior_subset_carrier F) h

def is_inx {P : Type*} [Fig α P] [Fig β P] (A : P) (F : α) (G : β) : Prop := A LiesOn F ∧ A LiesOn G

scoped notation:50 A:max " IsInxOf " F:max G:max => (is_inx A F G)

theorem is_inx.symm {P : Type*} [Fig α P] [Fig β P] {A : P} {F : α} {G : β} (h : A IsInxOf F G) : A IsInxOf G F := And.symm h

def intersect {P : Type*} [Fig α P] [Fig β P] (F : α) (G : β) : Prop := ∃ A : P, A LiesOn F ∧ A LiesOn G

scoped notation:50 F:max " InxWith " G:max => intersect F G

theorem intersect.symm {P : Type*} [Fig α P] [Fig β P] {F : α} {G : β} (h : F InxWith G) : G InxWith F := Exists.casesOn h fun _ hu => Exists.intro _ hu.symm


section ne

theorem ne_of_lieson_and_not_lieson {P : Type*} [Fig α P] {F : α} {X Y : P} (hx : X LiesOn F) (hy : ¬ Y LiesOn F) : X ≠ Y := by
  by_contra h
  rw [h] at hx
  tauto

theorem ne_of_liesint_and_not_liesint {P : Type*} [Interior α P] {F : α} {X Y : P} (hx : X LiesInt F) (hy : ¬ Y LiesInt F) : X ≠ Y := by
  by_contra h
  rw [h] at hx
  tauto

end ne

end carrier

/- Three figures concurrent at a point -/
def concurrent {P : Type*} [EuclideanPlane P] [Fig α P] [Fig β P] [Fig γ P] (A : P) (F : α) (G : β) (H : γ) : Prop := A LiesOn F ∧ A LiesOn G ∧ A LiesOn H

class Convex2D (α : Type*) (P : outParam <| Type*) [outParam <| EuclideanPlane P] extends IntFig α P where
  convexity : ∀ (F : α) (A B : P), (A LiesOn F) → (B LiesOn F) → ∃ (t : ℝ), (t • (B -ᵥ A) +ᵥ A) LiesOn F
  int_of_carrier : ∀ (F : α) (A : P), (A LiesInt F) → ∃ (B₁ B₂ B₃ : P) (t₁ t₂ t₃ : ℝ), (B₁ LiesOn F) ∧ (B₂ LiesOn F) ∧ (B₃ LiesOn F) ∧ (0 < t₁) ∧ (0 < t₂) ∧ (0 < t₃) ∧ (t₁ • VEC A B₁ + t₂ • VEC A B₂ + t₃ • VEC A B₃ = 0)

/- Theorem interior is convex-/

/- Intersection -/

class HasCongr (α : Type*) where
  congr : α → α → Prop
  refl : ∀ (a : α), congr a a
  trans : ∀ {a b c : α}, congr a b → congr b c → congr a c
  symm : ∀ {a b : α}, congr a b → congr b a

instance (α : Type*) [HasCongr α] : IsEquiv α HasCongr.congr where
  refl := HasCongr.refl
  trans _ _ _ := HasCongr.trans
  symm _ _ := HasCongr.symm

scoped infix : 50 " ≅ " => HasCongr.congr

scoped infix : 50 " IsCongrTo " => HasCongr.congr

class HasACongr (α : Type*) where
  acongr : α → α → Prop
  symm : ∀ {a b : α}, acongr a b → acongr b a

instance (α : Type*) [HasACongr α] : IsSymm α HasACongr.acongr where
  symm _ _ := HasACongr.symm

scoped infix : 50 " ≅ₐ " => HasACongr.acongr

scoped infix : 50 " IsACongrTo " => HasACongr.acongr

class HasSim (α : Type*) where
  sim : α → α → Prop
  refl : ∀ (a : α), sim a a
  trans : ∀ {a b c : α}, sim a b → sim b c → sim a c
  symm : ∀ {a b : α}, sim a b → sim b a

instance (α : Type*) [HasSim α] : IsEquiv α HasSim.sim where
  refl := HasSim.refl
  trans _ _ _ := HasSim.trans
  symm _ _ := HasSim.symm

/-- The similarity relation is denoted by infix $\sim$.-/
scoped infix : 50 " ∼ " => HasSim.sim

/-- The similarity relation is denoted by infix "IsSimTo".-/
scoped infix : 50 " IsSimTo " => HasSim.sim

class HasASim (α : Type*) where
  asim : α → α → Prop
  symm : ∀ {a b : α}, asim a b → asim b a

instance (α : Type*) [HasACongr α] : IsSymm α HasACongr.acongr where
  symm _ _ := HasACongr.symm

/-- The anti-similarity relation is denoted by infix $\sim_a$.-/
scoped infix : 50 " ∼ₐ " => HasASim.asim

/-- The anti-similarity relation is denoted by infix "IsASimTo".-/
scoped infix : 50 " IsASimTo " => HasASim.asim

end EuclidGeom
