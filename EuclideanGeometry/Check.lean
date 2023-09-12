import Mathlib.Analysis.InnerProductSpace.PiL2

import EuclideanGeometry.Foundation.Index
/- here checks things-/

/- 
## Part I: Geometric Playground. 
Check whether geometric constructions, theorems are mathematically correct.
-/


/-
## Part II: Type Reassurance
Check the where a type is behaved as designed 
-/
namespace EuclidGeom
/- check instance VAdd-/
section VAddCheck

variable (P : Type _) [EuclidGeom.EuclideanPlane P] (l : Ray P)
#check l.toDir.toVec
#check @AddAction.toVAdd _ _ _ (@AddTorsor.toAddAction _ _ _ (@NormedAddTorsor.toAddTorsor (ℝ × ℝ) P EuclidGeom.Vec.SeminormedAddCommGroup _ _))

end VAddCheck

section raymk

#check Ray.mk

end raymk

/- check angle notation-/
section anglecheck

variable {P : Type _} [h : EuclideanPlane P] (O : P) (A : P) (B : P)
#check ∠ A O B

variable (l : GDirSeg P)
#check l.toVec

end anglecheck



end EuclidGeom