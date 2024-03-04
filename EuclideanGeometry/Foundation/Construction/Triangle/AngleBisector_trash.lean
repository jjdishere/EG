import EuclideanGeometry.Foundation.Construction.Triangle.AngleBisector

noncomputable section
namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P]

theorem isAngBisLine_of_value_eq {A B C O : P} [PtNe A O] [PtNe B O] [PtNe C O] (h : ∠ A O C = ∠ C O B) : IsAngBisLine (ANG A O B) (LIN O C) := sorry

end EuclidGeom
