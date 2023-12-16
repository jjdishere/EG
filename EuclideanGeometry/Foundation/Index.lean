/- Axiom -/
/- Axiom.Basic -/
import EuclideanGeometry.Foundation.Axiom.Basic.Vector
import EuclideanGeometry.Foundation.Axiom.Basic.Plane
import EuclideanGeometry.Foundation.Axiom.Basic.Class
/- Axiom.Linear -/
import EuclideanGeometry.Foundation.Axiom.Linear.Ray
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Colinear
import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Class
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
/- Axiom.Position -/
import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Orientation
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Position.Orientation_ex
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex2
/- Axiom.Isometry -/
import EuclideanGeometry.Foundation.Axiom.Isometry.Rotation
import EuclideanGeometry.Foundation.Axiom.Isometry.Translation_ex
/- Axiom.Triangle -/
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_trash
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence -- `to avoid ambiguous notation, use notation ≅, ≅ₐ`
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_ex
import EuclideanGeometry.Foundation.Axiom.Triangle.Trigonometric
import EuclideanGeometry.Foundation.Axiom.Triangle.Similarity
import EuclideanGeometry.Foundation.Axiom.Triangle.IsocelesTriangle
/- Axiom.Circle -/
import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Circle.CCPosition
import EuclideanGeometry.Foundation.Axiom.Circle.LCPosition
import EuclideanGeometry.Foundation.Axiom.Circle.IncribedAngle

/- Tactic -/
/- Tactic.Congruence -/
import EuclideanGeometry.Foundation.Tactic.Congruence.Attr
import EuclideanGeometry.Foundation.Tactic.Congruence.Congruence
-- import EuclideanGeometry.Foundation.Tactic.Congruence.Congruence' -- `need to avoid some name collision during initialization?`
import EuclideanGeometry.Foundation.Tactic.Colinear.perm_colinear

/- Constuction -/
import EuclideanGeometry.Foundation.Construction.Inversion
/- Construction.ComputationTool-/
import EuclideanGeometry.Foundation.Construction.ComputationTool.Menelaus
import EuclideanGeometry.Foundation.Construction.ComputationTool.Ceva
/- Construction.Triangle -/
import EuclideanGeometry.Foundation.Construction.Triangle.AngleBisector
import EuclideanGeometry.Foundation.Construction.Triangle.PerpendicularBisector
import EuclideanGeometry.Foundation.Construction.Triangle.Orthocenter
import EuclideanGeometry.Foundation.Construction.Triangle.Centroid
/- Construction.Polygon -/
import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral
import EuclideanGeometry.Foundation.Construction.Polygon.Parallelogram
import EuclideanGeometry.Foundation.Construction.Polygon.Trapezoid
import EuclideanGeometry.Foundation.Construction.Polygon.Rhombus
import EuclideanGeometry.Foundation.Construction.Polygon.Rectangle
import EuclideanGeometry.Foundation.Construction.Polygon.Square
import EuclideanGeometry.Foundation.Construction.Polygon.GeneralPolygon
/- Construction.Circle -/
import EuclideanGeometry.Foundation.Construction.Circle.CyclicQuadrilateral
import EuclideanGeometry.Foundation.Construction.Circle.CyclicPolygon
import EuclideanGeometry.Foundation.Construction.Circle.RadicalAxis
import EuclideanGeometry.Foundation.Construction.Circle.SimsonLine

/- Theorem -/
/- Theorem.Triangle-/
import EuclideanGeometry.Foundation.Theorem.Triangle.EulerLine
import EuclideanGeometry.Foundation.Theorem.Triangle.NinePointCircle
/- Theorem.Circle-/
import EuclideanGeometry.Foundation.Theorem.Circle.Power

/-!
# Index of Foundations

`IMPORTANT!`

This file imports all files in Foundation. Please parse this file before create any pull request modifying anything in folder Foundation.
-/
