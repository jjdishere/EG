import EuclideanGeometry.Foundation.Axiom.Basic.Plane

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

/- point reflection -/
def pt_flip (A O : P) : P := (VEC A O) +ᵥ O

theorem pt_flip_symm {A B O : P} (h : B = pt_flip A O) : A = pt_flip B O := by
  rw [h]
  unfold pt_flip Vec.mkPtPt
  rw [vsub_vadd_eq_vsub_sub]
  simp

theorem pt_flip_vec_eq {A B O : P} (h : B = pt_flip A O) : VEC A O = VEC O B := by
  rw [h, pt_flip, Vec.mkPtPt, Vec.mkPtPt]
  simp

end EuclidGeom
