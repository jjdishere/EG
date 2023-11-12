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

In this file, we define suitable coversion function between these values. Starting from `Dir.toValue`, we convert `Dir` to `Real.Angle`. We shall primarily use `ℝ/2π`, and gives coercion and compatibility theorems with respect to `ℝ⧸π` and `(-π, π]`.


-/
noncomputable section
namespace EuclidGeom

def AngValue := Real.Angle

instance : NormedAddCommGroup AngValue := inferInstanceAs (NormedAddCommGroup (AddCircle (2*π)))

def Real.toAngValue := Real.Angle.coe

instance : Coe Real AngValue where
  coe := Real.toAngValue

def AddDir.toValue : Additive Dir →+ AngValue where
  toFun := fun d => (Complex.arg (d : Dir).1 : Real.Angle)
  map_zero' := by simp only [Dir.one_eq_one_toComplex, Complex.arg_one, Real.Angle.coe_zero]
  map_add' _ _:= Complex.arg_mul_coe_angle (Dir.tovec_ne_zero _) (Dir.tovec_ne_zero _)

def Dir.toAngValue (d : Dir) : AngValue := AddDir.toValue d

def AngDValue := AddCircle π

instance : NormedAddCommGroup AngDValue := inferInstanceAs (NormedAddCommGroup (AddCircle π))

def Real.Angle.toDValue : AngValue →+ AngDValue where
  toFun := Quotient.lift (fun x : ℝ => (x : AddCircle π)) sorry
  map_zero' := sorry
  map_add' := sorry

instance : Coe AngValue AngDValue where
  coe := Real.Angle.toDValue.toFun

#check Real.Angle.toReal
variable (a : Real.Angle)
#check a.toReal

def IsPos (θ : Real.Angle) : Prop := sbtw 0 θ π

def IsNeg (θ : Real.Angle) : Prop := sbtw (π: Real.Angle) θ 0

def Value.toDirAngValue : Real.Angle → ℝ := Real.Angle.toReal

def Value.toModValue : ℝ → Real.Angle := Real.Angle.coe


end EuclidGeom
