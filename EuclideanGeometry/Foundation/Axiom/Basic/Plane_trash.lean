import EuclideanGeometry.Foundation.Axiom.Basic.Plane

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

@[simp]
theorem neg_vec_norm_eq (A B : P) : Vec.norm (VEC A B) = Vec.norm (VEC B A) := by
  calc
    _ = dist B A := by rw [NormedAddTorsor.dist_eq_norm']; rfl
    _ = dist A B := by apply dist_comm
    _ = Vec.norm (VEC B A) := by rw [NormedAddTorsor.dist_eq_norm']; rfl

end EuclidGeom
