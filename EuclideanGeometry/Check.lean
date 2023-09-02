/- here checks things-/
import Mathlib.Analysis.InnerProductSpace.PiL2

import EuclideanGeometry.Foundation.Axiom.Basic
import EuclideanGeometry.Foundation.Axiom.Ray
import EuclideanGeometry.Foundation.Axiom.Angle

namespace EuclidGeom
/- check instance VAdd-/
section VAddCheck

variable (P : Type _) [EuclidGeom.EuclideanPlane P] (l : Ray P)
#check l.direction.vec
#check @AddAction.toVAdd _ _ _ (@AddTorsor.toAddAction _ _ _ (@NormedAddTorsor.toAddTorsor (ℝ × ℝ) P EuclidGeom.StdR2.SeminormedAddCommGroup _ _))

end VAddCheck

section raymk

#check Ray.mk
#check GDirSeg.mk

end raymk

/- check angle notation-/
section anglecheck

variable {P : Type _} [h : EuclideanPlane P] (O : P) (A : P) (B : P)
#check ∠ A O B

variable (l : GDirSeg P)
#check l.toVec

end anglecheck



end EuclidGeom