import EuclideanGeometry.Foundation.Axiom.Triangle.IsocelesTriangle

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

lemma isoceles_tri_pts_ne {tri : Triangle P} (h : tri.IsIsoceles) (hne : tri.point₂ ≠ tri.point₃) : (tri.point₁ ≠ tri.point₂) ∧ (tri.point₁ ≠ tri.point₃) := sorry

theorem is_isoceles_tri_ang_eq_ang_of_tri {tri : Triangle P} (h : tri.IsIsoceles) (hne : tri.point₂ ≠ tri.point₃) : ∠ tri.point₃ tri.point₂ tri.point₁ hne.symm (isoceles_tri_pts_ne h hne).1 = ∠ tri.point₁ tri.point₃ tri.point₂ (isoceles_tri_pts_ne h hne).2 hne := by sorry

end EuclidGeom
