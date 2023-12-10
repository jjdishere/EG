import EuclideanGeometry.Foundation.Axiom.Basic.Vector

/-!
# Angle Conversions

Recall in Euclidean Geometry, the measure of angle is subtle. The measure of an angle can be treated as a number in `ℝ⧸2π`, `(-π, π]`, `[0, 2π)`, `ℝ⧸π`, or even `[0, π]` (after taking abs). Each of them has their own suitable applications.
* `ℝ⧸2π` : add and sub of angles, angle between dirrcted object;
* `(-π, π]` : measure of oriented angle, angles of a triangle, positions;
* `[0, 2π)` : length of arc, central angle;
* `ℝ⧸π` : measure of directed angle when discussing four points concyclic, angle between lines
* `[0, π]` : cosine theorem, undirected angles.

In this file, we define suitable coversion function between these values.

## Main Definitions
We will use `A.toB` to denote the conversion from `A` to `B`
### List of Values
* `ModValue` : `ℝ⧸2π`, with type `AngValue`
* `RealValue` : `(-π, π]`, with type `ℝ`
* `PosValue` : `[0, 2π)`, with type `ℝ`
* `DAngValue` : `ℝ⧸π`, with type `AddCircle π`
* `AbsValue` : `[0, π]`, with type `ℝ`
### Conversions
* `ModValue` to `RealValue`, `PosValue`, `DAngValue`, `AbsValue`
* `RealValue` to `ModValue`, `PosValue`, `DAngValue`, `AbsValue`
* `PosValue` to `ModValue`, `RealValue`, `DAngValue`, `AbsValue`
* `DAngValue` to Nothing
* `AbsValue` to Nothing
The core is a circle of conversions of `ModValue` `RealValue` `PosValue`, and `ModValue.toDAngValue`, `RealValue.toAbsValue`.

-/
noncomputable section
namespace EuclidGeom

def ModValue.toRealValue : AngValue → ℝ := AngValue.toReal

def RealValue.toModValue : ℝ → AngValue := AngValue.coe


end EuclidGeom
