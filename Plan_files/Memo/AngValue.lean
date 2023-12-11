/-!
# Angle and Angle Value

This file records the ideas and sketchy plan of Basic.Angle.lean, Position.Angle.lean.

## List of Core Definitions
* `Dir` : in Basic.Vector, Geometric Value
* `Proj` : in Basic.Vector, Geometric Value
* `AngValue` : in Basic.Angle, Algebraic Value
* `AngDValue` : in Basic.Angle, Algebraic Value
* `Angle` : in Position.Angle, Figure
* `DirObj` : in Linear.Class, Figure
* `ProjObj` : in Linear.Class, Figure
Note that `ℝ` is also used for representing the value of an angle (Algeraic Value)

## Relations
### Value Coercions
#### Algebraic Value
* `Real` to `AngValue` to `AngDValue` : AddGroupHom, `simp direction always to AngValue?`
* `AngValue` to `Real` : Weird
#### Geometric Value
* `Dir` to `Proj` : GroupHom, Definition of `Proj`
* `Dir` isom to `AngValue` : Mul to Add, need many theorems, simp to `AngValue`, one is another `⁻¹` `.invFun, .symm` if writen in a structure version
* `Proj` isom to `AngDValue` : Mul to Add, simp to `AndDValue`
### Figure to Value
* `DirObj`*2 to `Dir` to `AngValue` : only the composition is exposed to user
* `Angle` to `Dir` to `AngValue` : use previous one
* `ProjObj`*2 to `Proj` to `AngDValue` : only the composition is exposed to user
### Value Acts on Figure
* `Ray` + `Dir` to `Ray` : this is a special case or rotation. We shall do rotation only for ray first. Add `Dir` to `Ray` `Maybe wrap outside a theorem use AngValue instead of Dir is better?`

-- The following suggestions may be bad. They are postponed.
* `Dir` + `DirObj` + `P` to `DirObj` : Rotation of `DirObj`
* `Proj` + `ProjObj` + `P` to `DirObj` : Rotation of `ProjObj`
* `Rotation` : the general rotation's type is `{P : Type _} [EuclideanPlane P] (O : P) (dir : Dir) [Figure α] (F : α P) : α P`  `Maybe wrap outside a theorem use AngValue instead of Dir is better?`

### Detailed Sections

File Basic.Angle :
  section angvalue
  `AngValue` : intances, Real.toAngValue
    section real_angvalue_compatibility
      section composite
      section special_value
      section group_hom `for simp direction`
    section pos_neg_isND
      section trichotomy
      section neg
      section toreal
    -- `Do we prepare is acute, is right, ... here?`
    section trignometric
    section dir_angvalue_compatibility
      section special_value
      section mul_add_isom
  section angdvalue
  `AngDValue` : instances, AngValue.toAngDValue, Real.toAngDValue
    AngDValue.Double : `AngDValue → AngValue`
    section compatibility
      section special_value
      section group_hom `?, use AddCircle, but for Double and proj need thms`
    section proj_angdvalue_compatibility
      section special_value
      section mul_add_isom

  section Cosine_theorem_for_Vec_nd
  section Linear_Algebra
  section sameRay_theorems

File Position.Angle :
  angle_of_dirfigure : add sub unique( parallel implies add parallel )
  angle.value : use angle_of_dirfigure add sub unique



### ToDo List
* Should distinguish `Real.pi` and `AngValue.pi` do we need?  what about `AngValue.pi_div_two`?

-/
