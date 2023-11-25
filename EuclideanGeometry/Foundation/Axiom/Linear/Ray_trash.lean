import EuclideanGeometry.Foundation.Axiom.Basic.Plane
import EuclideanGeometry.Foundation.Axiom.Basic.Class
import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace length

theorem length_eq_length_of_length_eq_length {A B C D : P} (hb : B LiesOn (SEG A D)) (hc : C LiesOn (SEG A D))
    (h : (SEG A B).length = (SEG C D).length) : (SEG A C).length = (SEG B D).length := by sorry

end length

end EuclidGeom
