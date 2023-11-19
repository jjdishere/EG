import EuclideanGeometry.Foundation.Axiom.Basic.Class
import EuclideanGeometry.Foundation.Axiom.Linear.Line

/-!
# Hierarchy Classes of Linear Objects

Recall we have the following linear objects:
* `Vec` in Basic.Vector
* `Vec_nd` in Basic.Vector
* `Dir` in Basic.Vector
* `Proj` in Basic.Vector
* `Seg` in Linear.Ray
* `Seg_nd` in Linear.Ray DirFig
* `Ray` in Linear.Ray DirFig
* `DirLine` in Linear.Line DirFig
* `Line` in Linear.Line Fig
In this file, we assign linear objects into different abstract classes so that properties holds for the whole classes can be proved in a single theorem.

## Main Definitions

* `LinFig` : The class of linear figures, i.e. every three points in the carrier is colinear.
* `DirObj` : The class of objects with direction, i.e. equipped with a `toDir` method. It does not have to be a plane figure, e.g. `Vec_nd` and `Dir` itself.
* `DirFig` : The class of linear figures with direction. Each figure is equipped with a `toDirLine` method.
* `ProjObj` : The class of objects with projective direction, i.e. equipped with a `toProj` method. It does not have to be a plane figure, e.g. `Vec_nd` and `Proj` itself.
* `ProjFig` : The class of linear figures with projective direction. Each figure is equipped with a `toLine` method.

## Usage of Classes

* `LinFig` : A basic class.
* `DirObj` : Every two objects has a angle between them. This angle should be saved as Dir and has 3 representations, `Real.Angle` (mod 2π), `(-π, π]`, `[0, 2π)`.
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
  carrier_subset_toline : ∀ {P : Type _} [EuclideanPlane P] {F : α P}, carrier F ⊆ (toLine F).carrier
  toline_toproj_eq_toproj : ∀ {P : Type _} [EuclideanPlane P] {F : α P}, (toLine F).toProj = toProj' F

class DirObj (β : Type _) extends ProjObj β where
  toDir : β → Dir
  todir_toproj_eq_toproj : ∀ {G : β}, (toDir G).toProj = toProj G

class DirFig (α : (P : Type _) → [EuclideanPlane P] → Type _) extends ProjFig α where
  toDir' : {P : Type _} → [EuclideanPlane P] → α P → Dir
  toDirLine : {P : Type _} → [EuclideanPlane P] → α P → DirLine P
  todirline_todir_eq_todir : ∀ {P : Type _} [EuclideanPlane P] {F : α P}, (toDirLine F).toDir = toDir' F
  todir_toproj_eq_toproj : ∀ {P : Type _} [EuclideanPlane P] {F : α P}, (toDir' F).toProj = toProj' F
  todirline_toline_eq_toline :  ∀ {P : Type _} [EuclideanPlane P] {F : α P}, (toDirLine F).toLine = toLine F
  reverse : {P : Type _} → [EuclideanPlane P] → α P → α P
  rev_rev : {P : Type _} → [EuclideanPlane P] → (F : α P) → (reverse (reverse F) = F)
  todirline_rev_eq_to_rev_dirline : {P : Type _} → [EuclideanPlane P] → (F : α P) → ((toDirLine F).reverse = toDirLine (reverse F))

section fig_to_obj

variable {P : Type _} [EuclideanPlane P]

instance [ProjFig α] : ProjObj (α P) where
  toProj := ProjFig.toProj'

instance [DirFig α] : DirObj (α P) where
  toDir := DirFig.toDir'
  todir_toproj_eq_toproj := DirFig.todir_toproj_eq_toproj

end fig_to_obj

export ProjFig (toProj' toLine toline_toproj_eq_toproj carrier_subset_toline)
export ProjObj (toProj)
export DirFig (toDir' toDirLine todir_toproj_eq_toproj todirline_toline_eq_toline)
export DirObj (toDir)

section instances
-- Fun Fact: Vec is none of these. Id is LinFig.

instance : DirObj Vec_nd where
  toProj := Vec_nd.toProj
  toDir := Vec_nd.toDir
  todir_toproj_eq_toproj := rfl

instance : DirObj Dir where
  toProj := Dir.toProj
  toDir := id
  todir_toproj_eq_toproj := rfl

instance : ProjObj Proj where
  toProj := id

instance : LinFig Seg where
  colinear' := Seg.colinear_of_lies_on

instance : DirFig Seg_nd where
  carrier s := s.carrier
  colinear' := Seg.colinear_of_lies_on
  toProj' := Seg_nd.toProj
  toLine := Seg_nd.toLine
  carrier_subset_toline _ _ {s} := s.subset_toline
  toline_toproj_eq_toproj := rfl
  toDir' := Seg_nd.toDir
  toDirLine := Seg_nd.toDirLine
  todirline_todir_eq_todir := rfl
  todir_toproj_eq_toproj := rfl
  todirline_toline_eq_toline := rfl
  reverse := Seg_nd.reverse
  rev_rev _ := Seg_nd.rev_rev_eq_self
  todirline_rev_eq_to_rev_dirline _ := Seg_nd.todirline_rev_eq_rev_toline

instance : DirFig Ray where
  carrier := Ray.carrier
  colinear' := Ray.colinear_of_lies_on
  toProj' := Ray.toProj
  toLine := Ray.toLine
  carrier_subset_toline := Or.inl
  toline_toproj_eq_toproj := rfl
  toDir' := (·.toDir)
  toDirLine := Ray.toDirLine
  todirline_todir_eq_todir := rfl
  todir_toproj_eq_toproj := rfl
  todirline_toline_eq_toline := rfl
  reverse := Ray.reverse
  rev_rev _ := Ray.rev_rev_eq_self
  todirline_rev_eq_to_rev_dirline _ := Ray.todirline_rev_eq_rev_toline

instance : DirFig DirLine where
  carrier := DirLine.carrier
  colinear' := DirLine.linear
  toProj' := DirLine.toProj
  toLine := DirLine.toLine
  carrier_subset_toline := id
  toline_toproj_eq_toproj := DirLine.toline_toproj_eq_toproj _
  toDir' := (·.toDir)
  toDirLine := id
  todirline_todir_eq_todir := rfl
  todir_toproj_eq_toproj := rfl
  todirline_toline_eq_toline := rfl
  reverse := DirLine.reverse
  rev_rev := DirLine.rev_rev_eq_self
  todirline_rev_eq_to_rev_dirline := by simp only [id_eq, implies_true, forall_const]

instance : ProjFig Line where
  carrier := Line.carrier
  colinear' := Line.linear
  toProj' := Line.toProj
  toLine := id
  carrier_subset_toline := id
  toline_toproj_eq_toproj := rfl

end instances

section theorems

open Line DirLine

variable {P : Type _} [EuclideanPlane P]

theorem carrier_toproj_eq_toproj {A B : P} [ProjFig α] {F : α P} (h : B ≠ A) (ha : A LiesOn F) (hb : B LiesOn F) : (SEG_nd A B h).toProj = toProj' F :=
  (toproj_eq_seg_nd_toproj_of_lies_on (carrier_subset_toline ha) (carrier_subset_toline hb) h).trans toline_toproj_eq_toproj

theorem line_of_pt_toproj_eq_to_line {A : P} [ProjFig α] {F : α P} (h : A LiesOn F) : Line.mk_pt_proj A (toProj F) = toLine F :=
  mk_pt_proj_eq_of_eq_toproj (carrier_subset_toline h) toline_toproj_eq_toproj.symm

theorem DirFig.rev_toDir_eq_neg_toDir {α : (P : Type _) → [EuclideanPlane P] → Type _} [DirFig α] (l : α P) : toDir' (reverse l) = - toDir' l :=
  todirline_todir_eq_todir.symm.trans <| (congrArg toDir (todirline_rev_eq_to_rev_dirline l).symm).trans <|
    rev_todir_eq_neg_todir.trans (neg_inj.mpr todirline_todir_eq_todir)

theorem DirFig.rev_toProj_eq_toProj {α : (P : Type _) → [EuclideanPlane P] → Type _} [DirFig α] (l : α P) : toProj (reverse l) = toProj l :=
  todir_toproj_eq_toproj.symm.trans <| (congrArg Dir.toProj (rev_toDir_eq_neg_toDir l)).trans <|
    ((toDir' l).neg_toproj_eq).trans todir_toproj_eq_toproj

end theorems

/- to be delete
variable {P : Type _} [EuclideanPlane P] (A B C : P) [h : ProjFig α] (F : α P) (s : Seg_nd P) (d : DirLine P)
example : d.toProj = d.toLine.toProj := rfl
#check toProj F
example : toProj F = toProj' F := rfl
#check A LiesOn F
-/

end EuclidGeom
