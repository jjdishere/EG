import EuclideanGeometry.Foundation.Axiom.Linear.Line
/-!
# Linear Objects

This file records all linear objects and describe their relation.

## List of Objects
* `Vec` in Basic.Vector `Not Linear`
* `VecND` in Basic.Vector
* `Dir` in Basic.Vector
* `Proj` in Basic.Vector
* `Seg` in Linear.Ray `Not Linear`
* `SegND` in Linear.Ray DirFig
* `Ray` in Linear.Ray DirFig
* `DirLine` in Linear.Line DirFig
* `Line` in Linear.Line Fig

## Coecions
### In Non-Figures
* `VecND` to `Vec`
* `VecND` to `Dir`to `Proj`
* `Dir` to `VecND`
### In Figures
* `SegND` to `Seg`
* `SegND` to `Ray` to `DirLine` to `Line`
### From Figure to Non-Figure
* `SegND` to `VecND`
* `Seg` to `Vec`
* `Ray` to `Dir` to `Proj`
* `DirLine` to `Dir` to `Proj`
* `Line` to `Proj`

## Classes
* `Object` Everything
* `Carrier` -> Maybe rename to `Fig`
* `DirObj`
* `DirFig` -> extends `HasDir` `Fig`, what's their relation? `any 2 ne pts, their dir is +- toDir`
* `Linearobject` -> `ProjObj`, `Coe HasDir HasProj`
* `LinearFigure` -> `ProjFig`, `Coe DirFig ProjFig`

## Usage of classes
* `Carrier` -- LiesOn InxWith IsInx Concurrent
* `DirObj` -- given 2 DirObj, have 3 kind of angle value
* `DirFig` -- Left Right ODist ToDirLine OnLineOf OffLineOf
* `ProjObj` -- parallel perpendicular
* `ProjFig` -- toLine intx_of_toLine (? do we need)

toDirLine toLine carrier compatibility can be shown in general

## Detailed Description of Classes in Axiom/Linear
* `LinFig` : The class of linear figures, i.e. every three points in the carrier is colinear.
* `DirObj` : The class of objects with direction, i.e. equipped with a `toDir` method. It does not have to be a plane figure, e.g. `VecND` and `Dir` itself.
* `DirFig` : The class of linear figures with direction, that is equivalent to say, each figure is equipped with a `toDirLine` method.
* `ProjObj` : The class of objects with projective direction, i.e. equipped with a `toDir` method. It does not have to be a plane figure, e.g. `VecND` and `Proj` itself.
* `ProjFig` : The class of linear figures with projective direction, that is equivalent to say, each figure is equipped with a `toLine` method.

-/


-- Experiments of classes

namespace EuclidGeom
variable {P : Type _} [EuclideanPlane P]

class ProjObj (P : Type _) [EuclideanPlane P] (α : Type _)where
  toProj : α → Proj

instance : ProjObj P (Line P) where
  toProj := Line.toProj

def to_Proj {P: Type _} [EuclideanPlane P] (l : Line P) : Proj := ProjObj.toProj P l

def toProj' ⦃P : Type _⦄ {α: Type _} [EuclideanPlane P] [ProjObj P α] (l : α) : Proj := ProjObj.toProj P l

example {P : Type _} [EuclideanPlane P] (l : Line P) : l.toProj = to_Proj l := rfl

def to_Line {P : Type _ } {α: Type _} [EuclideanPlane P] ⦃h : ProjObj P α⦄ (l : α) : Line P := sorry

variable (l : Line P)
-- same name enables both writing style without overload
-- proof together but still need back to traditional dot notation.
#check to_Proj l
#check toProj' l -- var
#check l.toProj
#check toLine  -- var

postfix : max "to_Proj" => ProjObj.toProj
-- `toProj l`, first check l's type, if it is Line/DirLine/xxx P, convert to ProjObj.toProj P l
syntax "toProj" term:max : term

macro_rules
| `(toProj $x) => `(first)


#check Seg
#check Seg.carrier

-- This is Plane Figure
class PlaneFig (F : (P : Type _) -> [ EuclideanPlane P] -> Type _) where
  carrier : {P : Type _} -> [EuclideanPlane P] -> F P -> Set P

instance : PlaneFig Seg where
  carrier := Seg.carrier
variable (s : Seg P)
#check PlaneFig.carrier s -- ok to infer P

end EuclidGeom
