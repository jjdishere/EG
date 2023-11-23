import EuclideanGeometry.Foundation.Axiom.Basic.Vector
import Mathlib.Analysis.Normed.Group.AddCircle
/-!
# Angle Conversions

Recall in Euclidean Geometry, the measure of angle is subtle. The measure of an angle can be treated as a number in `ℝ⧸2π`, `(-π, π]`, `[0, 2π)`, `ℝ⧸π`, or even `[0, π]` (after taking abs). Each of them has their own suitable applications.
* `ℝ⧸2π` : add and sub of angles, angle between dirrcted object;
* `(-π, π]` : measure of oriented angle, angles of a triangle, positions;
* `[0, 2π)` : length of arc, central angle;
* `ℝ⧸π` : measure of directed angle when discussing four points concyclic, angle between lines
* `[0, π]` : cosine theorem, undirected angles.

In this file, we define suitable coversion function between `ℝ⧸2π`,`ℝ⧸π` and `(-π, π]`. Starting from `Dir.toAngValue`, we convert `Dir` to `AngValue`. We shall primarily use `ℝ/2π`, and gives coercion and compatibility theorems with respect to `ℝ⧸π` and `(-π, π]`.

-/
noncomputable section
namespace EuclidGeom

section angvalue
def AngValue := Real.Angle

instance : NormedAddCommGroup AngValue := inferInstanceAs (NormedAddCommGroup (AddCircle (2*π)))

def Real.toAngValue : ℝ → AngValue := Real.Angle.coe

instance : Coe Real AngValue where
  coe := Real.toAngValue

def IsPos (θ : Real.Angle) : Prop := sbtw 0 θ π

def IsNeg (θ : Real.Angle) : Prop := sbtw (π: Real.Angle) θ 0

def AngValue.toReal : Real.Angle → ℝ := Real.Angle.toReal

-- should be isomorphism
def AddDir.toAngValue : Additive Dir →+ AngValue where
  toFun := fun d => (Complex.arg (d : Dir).1 : Real.Angle)
  map_zero' := by simp only [Dir.one_eq_one_toComplex, Complex.arg_one, Real.Angle.coe_zero]
  map_add' _ _:= Complex.arg_mul_coe_angle (Dir.tovec_ne_zero _) (Dir.tovec_ne_zero _)

def Dir.toAngValue (d : Dir) : AngValue := AddDir.toAngValue d

end angvalue

section angdvalue

def AngDValue := AddCircle π

instance : NormedAddCommGroup AngDValue := inferInstanceAs (NormedAddCommGroup (AddCircle π))

def AngValue.toAngDValue : AngValue →+ AngDValue where
  toFun := Quotient.lift (fun x : ℝ => (x : AddCircle π)) sorry
  map_zero' := sorry
  map_add' := sorry

instance : Coe AngValue AngDValue where
  coe := AngValue.toAngDValue

def Real.toAngDValue : ℝ → AngDValue := fun r => (r : AngDValue)

instance : Coe ℝ AngDValue where
  coe := Real.toAngDValue

def AddDir.toAngDValue : Additive Dir →+ AngDValue where
  toFun := fun d => AngValue.toAngDValue (Complex.arg (d : Dir).1 : Real.Angle)
  map_zero' := by simp only [Dir.one_eq_one_toComplex, Complex.arg_one, Real.Angle.coe_zero, map_zero]
  map_add' _ _:= by sorry

def Dir.toAngDValue : Dir → AngDValue := fun d => AddDir.toAngDValue d

-- should be isomorphism
def AddProj.toAngDValue : Additive Proj →+ AngDValue where
  toFun := Quotient.lift (fun p => AngValue.toAngDValue (Complex.arg (p : Dir).1 : Real.Angle)) sorry
  map_zero' := sorry
  map_add' _ _:= by sorry

def Proj.toAngDValue : Proj → AngDValue := fun p => AddProj.toAngDValue p
-- some coercion compatibility
-- special values
-- lift +-
-- pos neg 0

end angdvalue


/-
#check Real.Angle.toReal
variable (a : Real.Angle)
#check a.toReal
-/


end EuclidGeom
