/-Overall structure

Axiom Folder

  Vector.lean -- basics of vectors, Dir (vectors with norm 1), Proj = Dir / {± 1}
  Plane.lean -- torsor structure of Euclidean plane over Vec

  subfolder : Linear_Object 
    Ray -- Define segments and rays (including midpoint here)
    Lines -- Define colinarity and lines, define the class LinObj and their toProj
    Parallel -- Define parallel lines and basic properties
    Perpendicular -- Define the perpendicular lines and perpendicular foot, Pythagorean theorem
  
  subfolder : Position
    Angle -- Define oriented angles
    Orientation -- Define the LHS and RHS of a ray
    Convex -- Define the concept of convexity and basic properties

  subfolder : Triangle
    Basic -- Basic definition of triangle, and its orientation when non-degenerate
    Trigonometric -- Basics of trigonometics for right triangles, cosine and sine theorem
    Congruence -- Congruence between triangles
    Similarity -- Define similar triangles

  subfolder : Circle
    Basic -- Define circles, inside and outside, arc, chord, diameter, and etc
    incribed angle -- Discuss central angles and incribed angles
    LCPosition -- Discuss relative position between a line and a circle, tangent; criteria for tangent lines
    CCPosition -- Discuss relative position of two circles
  
  subfolder : Isometry
    Translation -- Translation by a vector and varoius compatibility
    Rotation -- Rotation around a point with respect to an angle

Construction Folder

  subfolder : Computation tools
    Trigonometic : sine and cosine theorem, 

  subfolder : Triangle
    Angle_bisector -- Define angle bisector and its properties
    Perpendicular_bisector -- Define perpendicular bisector and its properties
    Centers -- Define the orthocenter, incenter and circumcenter of a nondegenerate triangle
    Isoceles_triangle -- Define isoceles triangles and equilateral/regular triangles.

  subfolder : Polygon
    Quadrilatral -- Define basics for quadrilatral; discuss its convexity 
    Parallelogram -- Definition and propeties of parallelograms, rhombus.
    Rectangular -- Define rectangular and squares
    general polygons -- Define general convex polygon, regular n-gon.

  subfolder : Circle
    Circumcircles -- Define the circumcircles of a triangle
    Cyclic polygon -- Define and discuss properties of cyclic polygons

Theorem Folder

  subfolder : Circle
    Power theorems -- Prove power theorems





-/