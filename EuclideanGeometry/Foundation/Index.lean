-- ######## IMPORTANT NOTE ######## --
/- This file imports all files in Foundation. Please parse this file before any pull request modifying anything in folder Foundation. -/

/- Axiom -/
/- Axiom.Basic -/
import EuclideanGeometry.Foundation.Axiom.Basic.Vector
import EuclideanGeometry.Foundation.Axiom.Basic.Plane
import EuclideanGeometry.Foundation.Axiom.Basic.Class
/- Axiom.Linear -/
import EuclideanGeometry.Foundation.Axiom.Linear.Ray
import EuclideanGeometry.Foundation.Axiom.Linear.Colinear
import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex
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
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_ex
import EuclideanGeometry.Foundation.Axiom.Triangle.Trigonometric
import EuclideanGeometry.Foundation.Axiom.Triangle.Similarity
/- Axiom.Circle -/
import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Circle.CCPosition
import EuclideanGeometry.Foundation.Axiom.Circle.LCPosition
import EuclideanGeometry.Foundation.Axiom.Circle.IncribedAngle

/- Constuction -/
/- Constuction.Triangle -/
import EuclideanGeometry.Foundation.Construction.Triangle.IsocelesTriangle
import EuclideanGeometry.Foundation.Construction.Triangle.AngleBisector
/- Constuction.Polygon -/
import EuclideanGeometry.Foundation.Construction.Polygon.Parallelogram
/- Constuction.Circle -/
import EuclideanGeometry.Foundation.Construction.Circle.CyclicPolygon

/- Theorem -/
/- Theorem.Circle-/
import EuclideanGeometry.Foundation.Theorem.Circle.Power