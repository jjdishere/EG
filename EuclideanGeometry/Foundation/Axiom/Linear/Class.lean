import EuclideanGeometry.Foundation.Axiom.Basic.Class
import EuclideanGeometry.Foundation.Axiom.Linear.Line

/-!
# Hierarchy Classes of Linear Objects

Recall we have the following linear objects:
* `Vec` in Basic.Vector
* `VecND` in Basic.Vector
* `Dir` in Basic.Vector
* `Proj` in Basic.Vector
* `Seg` in Linear.Ray
* `SegND` in Linear.Ray DirFig
* `Ray` in Linear.Ray DirFig
* `DirLine` in Linear.Line DirFig
* `Line` in Linear.Line Fig
In this file, we assign linear objects into different abstract classes so that properties holds for the whole classes can be proved in a single theorem.

## Main Definitions

* `LinFig` : The class of linear figures, i.e. every three points in the carrier is colinear.
* `DirObj` : The class of objects with direction, i.e. equipped with a `toDir` method. It does not have to be a plane figure, e.g. `VecND` and `Dir` itself.
* `DirFig` : The class of linear figures with direction. Each figure is equipped with a `toDirLine` method.
* `ProjObj` : The class of objects with projective direction, i.e. equipped with a `toProj` method. It does not have to be a plane figure, e.g. `VecND` and `Proj` itself.
* `ProjFig` : The class of linear figures with projective direction. Each figure is equipped with a `toLine` method.

## Usage of Classes

* `LinFig` : A basic class.
* `DirObj` : Every two objects has a angle between them. This angle should be saved as Dir and has 3 representations, `AngValue` (mod 2π), `(-π, π]`, `[0, 2π)`.
* `DirFig` : `toDirLine` method, can define `odist`, `odist_sign`, `Left`, `Right`, `OnLine`, `OffLine`.
* `ProjObj` : parallel and perpendicular.
* `ProjFig` : `toLine` method, compatibility of carrier to Line.

Only theorems about `ProjFig` will be dealt in this file.

## Further Work

-/

noncomputable section
namespace EuclidGeom

class LinFig (α : (P : Type _) → [EuclideanPlane P] → Type _) extends Fig α where
  colinear' : ∀ {P : Type _} [EuclideanPlane P] {A B C : P} {F : α P}, A LiesOn F → B LiesOn F → C LiesOn F → colinear A B C

class ProjObj (β : Type _) where
  toProj : β → Proj

-- the information here is abundant, choose toProj' + a field carrier_to_proj_eq_to_proj is also enough. Or even ∃ A B ∈ carrier, A ≠ B is enough. toProj' can be defined later. However, we choose to write this way in order to avoid `∃` and use as many rfl as possible.
class ProjFig (α : (P : Type _) → [EuclideanPlane P] → Type _) extends LinFig α where
  toProj' : {P : Type _} → [EuclideanPlane P] → α P → Proj
  toLine : {P : Type _} → [EuclideanPlane P] → α P → Line P
  carrier_subset_toLine : ∀ {P : Type _} [EuclideanPlane P] {F : α P}, carrier F ⊆ (toLine F).carrier
  toLine_toProj_eq_toProj : ∀ {P : Type _} [EuclideanPlane P] {F : α P}, (toLine F).toProj = toProj' F

class DirObj (β : Type _) extends ProjObj β where
  toDir : β → Dir
  toDir_toProj_eq_toProj : ∀ {G : β}, (toDir G).toProj = toProj G

class DirFig (α : (P : Type _) → [EuclideanPlane P] → Type _) extends ProjFig α where
  toDir' : {P : Type _} → [EuclideanPlane P] → α P → Dir
  toDirLine : {P : Type _} → [EuclideanPlane P] → α P → DirLine P
  toDirLine_toDir_eq_toDir : ∀ {P : Type _} [EuclideanPlane P] {F : α P}, (toDirLine F).toDir = toDir' F
  toDir_toProj_eq_toProj : ∀ {P : Type _} [EuclideanPlane P] {F : α P}, (toDir' F).toProj = toProj' F
  toDirLine_toLine_eq_toLine :  ∀ {P : Type _} [EuclideanPlane P] {F : α P}, (toDirLine F).toLine = toLine F
  reverse : {P : Type _} → [EuclideanPlane P] → α P → α P
  rev_rev : {P : Type _} → [EuclideanPlane P] → (F : α P) → (reverse (reverse F) = F)
  toDirLine_rev_eq_to_rev_dirline : {P : Type _} → [EuclideanPlane P] → (F : α P) → ((toDirLine F).reverse = toDirLine (reverse F))

section fig_to_obj

variable {P : Type _} [EuclideanPlane P]

instance [ProjFig α] : ProjObj (α P) where
  toProj := ProjFig.toProj'

instance [DirFig α] : DirObj (α P) where
  toDir := DirFig.toDir'
  toDir_toProj_eq_toProj := DirFig.toDir_toProj_eq_toProj

end fig_to_obj

export ProjFig (toProj' toLine toLine_toProj_eq_toProj carrier_subset_toLine)
export ProjObj (toProj)
export DirFig (toDir' toDirLine toDir_toProj_eq_toProj toDirLine_toLine_eq_toLine)
export DirObj (toDir)

section instances
-- Fun Fact: Vec is none of these. Id is LinFig.

instance : DirObj VecND where
  toProj := VecND.toProj
  toDir := VecND.toDir
  toDir_toProj_eq_toProj := rfl

instance : DirObj Dir where
  toProj := Dir.toProj
  toDir := id
  toDir_toProj_eq_toProj := rfl

instance : ProjObj Proj where
  toProj := id

instance : LinFig Seg where
  colinear' := Seg.colinear_of_lies_on

instance : DirFig SegND where
  carrier s := s.carrier
  colinear' := Seg.colinear_of_lies_on
  toProj' := SegND.toProj
  toLine := SegND.toLine
  carrier_subset_toLine _ _ {s} := s.subset_toLine
  toLine_toProj_eq_toProj := rfl
  toDir' := SegND.toDir
  toDirLine := SegND.toDirLine
  toDirLine_toDir_eq_toDir := rfl
  toDir_toProj_eq_toProj := rfl
  toDirLine_toLine_eq_toLine := rfl
  reverse := SegND.reverse
  rev_rev _ := SegND.rev_rev_eq_self
  toDirLine_rev_eq_to_rev_dirline _ := SegND.toDirLine_rev_eq_rev_toLine

instance : DirFig Ray where
  carrier := Ray.carrier
  colinear' := Ray.colinear_of_lies_on
  toProj' := Ray.toProj
  toLine := Ray.toLine
  carrier_subset_toLine := Or.inl
  toLine_toProj_eq_toProj := rfl
  toDir' := (·.toDir)
  toDirLine := Ray.toDirLine
  toDirLine_toDir_eq_toDir := rfl
  toDir_toProj_eq_toProj := rfl
  toDirLine_toLine_eq_toLine := rfl
  reverse := Ray.reverse
  rev_rev _ := Ray.rev_rev_eq_self
  toDirLine_rev_eq_to_rev_dirline _ := Ray.toDirLine_rev_eq_rev_toLine

instance : DirFig DirLine where
  carrier := DirLine.carrier
  colinear' := DirLine.linear
  toProj' := DirLine.toProj
  toLine := DirLine.toLine
  carrier_subset_toLine := id
  toLine_toProj_eq_toProj := DirLine.toLine_toProj_eq_toProj _
  toDir' := (·.toDir)
  toDirLine := id
  toDirLine_toDir_eq_toDir := rfl
  toDir_toProj_eq_toProj := rfl
  toDirLine_toLine_eq_toLine := rfl
  reverse := DirLine.reverse
  rev_rev _ := DirLine.rev_rev_eq_self
  toDirLine_rev_eq_to_rev_dirline := by simp only [id_eq, implies_true, forall_const]

instance : ProjFig Line where
  carrier := Line.carrier
  colinear' := Line.linear
  toProj' := Line.toProj
  toLine := id
  carrier_subset_toLine := id
  toLine_toProj_eq_toProj := rfl

end instances

section theorems

open Line DirLine

variable {P : Type _} [EuclideanPlane P]

theorem carrier_toProj_eq_toProj {A B : P} [ProjFig α] {F : α P} (h : B ≠ A) (ha : A LiesOn F) (hb : B LiesOn F) : (SEG_nd A B h).toProj = toProj' F :=
  (toProj_eq_seg_nd_toProj_of_lies_on (carrier_subset_toLine ha) (carrier_subset_toLine hb) h).trans toLine_toProj_eq_toProj

theorem line_of_pt_toProj_eq_to_line {A : P} [ProjFig α] {F : α P} (h : A LiesOn F) : Line.mk_pt_proj A (toProj F) = toLine F :=
  mk_pt_proj_eq_of_eq_toProj (carrier_subset_toLine h) toLine_toProj_eq_toProj.symm

theorem DirFig.rev_toDir_eq_neg_toDir {α : (P : Type _) → [EuclideanPlane P] → Type _} [DirFig α] (l : α P) : toDir' (reverse l) = - toDir' l :=
  toDirLine_toDir_eq_toDir.symm.trans <| (congrArg toDir (toDirLine_rev_eq_to_rev_dirline l).symm).trans <|
    rev_toDir_eq_neg_toDir.trans (neg_inj.mpr toDirLine_toDir_eq_toDir)

theorem DirFig.rev_toProj_eq_toProj {α : (P : Type _) → [EuclideanPlane P] → Type _} [DirFig α] (l : α P) : toProj (reverse l) = toProj l :=
  toDir_toProj_eq_toProj.symm.trans <| (congrArg Dir.toProj (rev_toDir_eq_neg_toDir l)).trans <|
    (toDir' l).toProj_neg.trans toDir_toProj_eq_toProj

end theorems

/- to be delete
variable {P : Type _} [EuclideanPlane P] (A B C : P) [h : ProjFig α] (F : α P) (s : SegND P) (d : DirLine P)
example : d.toProj = d.toLine.toProj := rfl
#check toProj F
example : toProj F = toProj' F := rfl
#check A LiesOn F
-/

end EuclidGeom
