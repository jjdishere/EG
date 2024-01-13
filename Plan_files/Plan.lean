/-Overall structure

Axiom Folder

  Vector -- basics of vectors, indentified with ℂ, Dir (vectors with norm 1), Proj = Dir / {± 1}
  Plane -- torsor structure of Euclidean plane over Vec
  Class -- define class of LiesOn LiesInt (using carrier, interior) and PlaneFigure

  subfolder : Linear
    Ray -- Define segments and rays (including midpoint here)
    Colinear -- Define colinarity
    Line -- Define lines, define the class LinObj and unify their toProj
    Parallel -- Define parallel lines and basic properties
    Perpendicular -- Define the perpendicular lines and perpendicular foot

  subfolder : Position
    Angle -- Define oriented angles
    Orientation -- Define the LHS and RHS of a ray
    Convex -- Define the concept of convexity and basic properties

  subfolder : Triangle
    Basic -- Basic definition of triangle, and its orientation when non-degenerate
    Trigonometric -- Basics of trigonometics for right triangles, Pythagorean theorem, cosine and sine theorem
    Congruence -- Congruence between triangles
    Similarity -- Define similar triangles

  subfolder : Circle
    Basic -- Define circles, inside and outside, arc, chord, diameter, and etc, also describe order of points on a circle
    IncribedAngle -- Discuss central angles and incribed angles
    LCPosition -- Discuss relative position between a line and a circle, tangent; criteria for tangent lines
    CCPosition -- Discuss relative position of two circles

  subfolder : Isometry
    Translation -- Translation by a vector and varoius compatibility
    Rotation -- Rotation around a point with respect to an angle

Tactic Folder

  subfolder : Congruence

  subfolder : Permutation

  subfolder : PointNe

Construction Folder

  subfolder : ComputationTool
    Menelaus -- the Menelaus theorem
    Ceva -- the Ceva theorem

  subfolder : Triangle
    AngleBisector -- Define angle bisector, exbisector and its properties, then define incenter and excenters of a nondegenerate triangle
    PerpendicularBisector -- Define perpendicular bisector and its properties, then define circumcenter of a nondegenerate triangle
    Orthocenter -- Define the orthocenter of a nondegenerate triangle
    Centroid -- Define the medians and centroid of a nondegenerate triangle
    IsocelesTriangle -- Define isoceles triangles and equilateral/regular triangles.

  subfolder : Polygon
    Quadrilatral -- Define basics for quadrilateral; discuss its convexity
    Parallelogram -- Definition and propeties of parallelograms
    Trapezoid -- Definition and propeties of trapezoids, Isoceles Trapezoid
    Rhombus -- Definition and propeties of rhombus
    Rectangle -- Definition and propeties of rectangles
    Square -- Definition and propeties of squares
    GeneralPolygon -- Define general convex polygons, regular polygons.

  subfolder : Circle
    CyclicQuadrilaterial -- Define the relation of four points concyclic, criterion and properties of concyclic
    `What is the good definition of 4 points concyclic s.t. (a) do not use ∃ ; (b) symmetric in 4 points`
    CyclicPolygon -- Define and discuss properties of general cyclic polygons
    RadicalAxis -- Define the radical axis given two circle and discuss it's property
    SimsonLine -- Define the Simson line

  Inversion -- Define the inversion given a inversion center and a radius, discuss properties preserved under inversion

Theorem Folder

  subfolder : Triangle
    EulerLine -- Define the Euler line
    NinePointCircle -- Define the nine point circle

  subfolder : Circle
    Power -- Prove power theorems

  subfolder : Projective -- projective geometry
    (empty for present)

  subfolder : Locus -- theorems about locus of points satisfying some condition is exactly a certain geometric figure
    (empty for present)




-/
