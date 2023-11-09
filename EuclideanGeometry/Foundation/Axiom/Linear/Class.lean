import EuclideanGeometry.Foundation.Axiom.Basic.Class'
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
* `DirFig` : The class of linear figures with direction. As a result, each figure is equipped with a `toDirLine` method.
* `ProjObj` : The class of objects with projective direction, i.e. equipped with a `toDir` method. It does not have to be a plane figure, e.g. `Vec_nd` and `Proj` itself.
* `ProjFig` : The class of linear figures with projective direction. As a result, each figure is equipped with a `toLine` method.

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
namespace debug

class LinFig (α : (P : Type _) → [ EuclideanPlane P] → Type _) extends Fig α where
  colinear' : ∀ {P : Type _} [EuclideanPlane P] (A B C : P) (F : α P), A LiesOn F → B LiesOn F → C LiesOn F → colinear A B C

class ProjObj (β : Type _) where
  toProj : β → Proj

class ProjFig (α : (P : Type _) → [ EuclideanPlane P] → Type _) extends LinFig α where
  toProj' : {P : Type _} → [EuclideanPlane P] → α P → Proj
  carrier_toproj_eq_toproj : ∀ {P : Type _} [EuclideanPlane P] (A B : P) (F : α P) (h : B ≠ A), A LiesOn F → B LiesOn F → (SEG_nd A B h).toProj = toProj' F

--Do we need DirObj extends ProjObj, DirFig extends ProjFig ???

class DirObj (β : Type _) where
  toDir : β → Dir

class DirFig (α : (P : Type _) → [ EuclideanPlane P] → Type _) extends LinFig α where
  toDir' : {P : Type _} → [EuclideanPlane P] → α P → Dir
  carrier_toproj_eq_todir_toproj : ∀ {P : Type _} [EuclideanPlane P] (A B : P) (F : α P) (h : B ≠ A), A LiesOn F → B LiesOn F → (SEG_nd A B h).toProj = (toDir' F).toProj

variable {P : Type _} [EuclideanPlane P]
instance [DirFig α] : DirObj (α P) where
  toDir := DirFig.toDir'

instance [ProjFig α] : ProjObj (α P) where
  toProj := ProjFig.toProj'

export ProjFig (toProj')
export ProjObj (toProj)


variable {P : Type _} [EuclideanPlane P] (A B C : P) [h : ProjFig α] (F : α P)
#check toProj F
example : toProj F = toProj' F := rfl
#check A LiesOn F

end debug
end EuclidGeom
