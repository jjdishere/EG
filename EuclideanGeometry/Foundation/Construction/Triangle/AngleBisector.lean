import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Circle.Basic
/-!

-/
noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

-- Feel free to change the name of the theorems and comments into better ones, or add sections to better organize theorems.
-- `Currently, the theorems are not well-organized, please follow the plan file to write and add theorems in this file into the plan file if they are not already in the plan`

-- we don't need to put the following definitions in the namespace Angle, since we will certainly not use it in the form of `ang.IsBis ray`
-- if only one condition is used, please change `structure : Prop` back to `def : Prop`, if more than one condition is used, please name each condition under structure, please do not use `∧`.
structure IsAngBis (ang : Angle P) (ray : Ray P) : Prop where

structure IsAngBisLine

structure IsExAngBis

structure IsExAngBiscetorLine

namespace Angle

/- when the Angle is flat, bis is on the left side-/
def AngBis (ang : Angle P) : Ray P := sorry

def AngBisLine (ang : Angle P) : Line P := ang.AngBis.toLine

def ExAngBis (ang : Angle P) : Ray P := sorry

def ExAngBisLine (ang : Angle P) : Line P := ang.ExAngBis.toLine

end Angle

namespace Angle

theorem ang_bis_is_ang_bis : sorry := sorry

theorem ang_bis_line_is_ang_bis_line : sorry := sorry

theorem ex_ang_bis_is_ex_ang_bis : sorry := sorry

theorem ex_ang_bis_line_is_ex_ang_bis_line : sorry := sorry

end Angle

/-definition property: lies on the bis means bisect the angle-/
theorem lie_on_ang_bis (ang: Angle P) (A : P): sorry := sorry

/- underlying line of bis as the locus satisfying the sum of distance to each ray of the angle is 0 -/
theorem lie_on_ang_bis_line_of_distance_zero (ang: Angle P) : sorry := sorry

theorem lie_on_ang_bis_of_lie_on_bis_line_inside_angle (ang : Angle P)  : sorry := sorry

/-bis lies inside the angle-/

/-construct the intercentor as the intersection of two bis-/

/-a triangle_nd admit an unique intercenter-/


structure IsIncenter (tri_nd : Triangle_nd P) (I : P) : Prop where

structure IsExcenter1 (tri_nd : Triangle_nd P) (E : P) : Prop where

structure IsIncircle (tri_nd : Triangle_nd P) (cir : Circle P) : Prop where

structure IsExcircle1 (tri_nd : Triangle_nd P) (cir : Circle P) : Prop where

namespace Triangle_nd

def Incenter (tri_nd : Triangle_nd P) : P := sorry

def Excenter1 (tri_nd : Triangle_nd P) : P := sorry

def Incircle (tri_nd : Triangle_nd P) : Circle P := sorry

def Excircle1 (tri_nd : Triangle_nd P) : Circle P := sorry

end Triangle_nd

namespace Triangle_nd

theorem incenter_is_incenter : sorry := sorry

theorem excenter1_is_excenter1 : sorry := sorry

theorem incircle_is_incircle : sorry := sorry

theorem excircle1_is_excircle1 : sorry := sorry

end Triangle_nd

/-the intercenter lies inside of the triangle-/

theorem incenter_lies_int_triangle (triangle_nd : Triangle_nd P): sorry := sorry

end EuclidGeom
