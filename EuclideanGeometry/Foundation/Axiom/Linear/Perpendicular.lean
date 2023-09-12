import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

def perpendicular (l₁ l₂: LinearObj P) : Prop := l₁.toProj = l₂.toProj.perp

scoped infix : 50 "IsPerpendicularTo" => perpendicular
scoped infix : 50 "⟂" => perpendicular

namespace perpendicular

@[simp]
protected theorem irrefl (l : LinearObj P)  : ¬ (l ⟂ l) := by sorry

protected theorem symm (l₁ l₂ : LinearObj P) : (l₁ ⟂ l₂) → (l₂ ⟂ l₁) := sorry

end perpendicular

section Perpendicular_and_parallel

theorem parallel_of_perp_perp (l₁ l₂ l₃ : LinearObj P) : (l₁ ⟂ l₂) → (l₂ ⟂ l₃) → (l₁ ∥ l₃) := by
  unfold perpendicular parallel
  intro h₁ h₂
  rw [h₂] at h₁
  simp at h₁
  exact h₁

theorem perp_of_parallel_perp (l₁ l₂ l₃ : LinearObj P) : (l₁ ∥ l₂) → (l₂ ⟂ l₃) → (l₁ ⟂ l₃) := sorry 

theorem perp_of_perp_parallel (l₁ l₂ l₃ : LinearObj P) : (l₁ ⟂ l₂) → (l₂ ∥ l₃) → (l₁ ⟂ l₃) := sorry 

theorem toProj_ne_toProj_of_perp (l₁ l₂: LinearObj P) : (l₁ ⟂ l₂) → (l₁.toProj ≠ l₂.toProj) := sorry

end Perpendicular_and_parallel

section Perpendicular_constructions

def perp_line (A : P) (l : Line P) := Line.mk_pt_proj A (l.toProj.perp)

@[simp]
theorem toProj_of_perp_line_eq_toProj_perp (A : P) (l : Line P) : (perp_line A l).toProj = l.toProj.perp := by
  sorry

theorem perp_foot_preparation (A : P) (l : Line P) : l.toProj ≠ (perp_line A l).toProj := by
  sorry

def perp_foot (A : P) (l : Line P) : P := intersection_of_nonparallel_line l (perp_line A l) (perp_foot_preparation A l)

end Perpendicular_constructions

section Pythagoras

theorem length_sq_eq_inner_toVec_toVec (seg : Seg P) : seg.length ^ 2 = Vec.InnerProductSpace.Core.inner seg.toVec seg.toVec := by
  have l : seg.length = Real.sqrt (Vec.InnerProductSpace.Core.inner seg.toVec seg.toVec) := by rfl
  rw [l]
  have n : 0 ≤ Vec.InnerProductSpace.Core.inner seg.toVec seg.toVec := by 
    exact Vec.InnerProductSpace.Core.nonneg_re seg.toVec
  rw [Real.sq_sqrt n]

theorem Pythagoras_of_ne_ne_perp {A B C : P} (hab : B ≠ A) (hac : C ≠ A) (h : (Seg_nd.toProj ⟨SEG A B, hab⟩).perp = (Seg_nd.toProj ⟨SEG A C, hac⟩)) : (SEG A B).length ^ 2 + (SEG A C).length ^ 2 = (SEG B C).length ^ 2 := by
  have i : Vec.InnerProductSpace.Core.inner (VEC A B) (VEC A C) = 0 := inner_eq_zero_of_Vec_nd_toProj_eq_Vec_nd_toProj (Seg_nd.toVec_nd ⟨SEG A B, hab⟩) (Seg_nd.toVec_nd ⟨SEG A C, hac⟩) h
  rw [length_sq_eq_inner_toVec_toVec (SEG A B), length_sq_eq_inner_toVec_toVec (SEG A C), length_sq_eq_inner_toVec_toVec (SEG B C)]
  simp only [Seg.seg_toVec_eq_vec]
  rw [← vec_sub_vec A B C]
  unfold Vec.InnerProductSpace.Core at i
  simp only at i 
  unfold Vec.InnerProductSpace.Core
  simp only [HSub.hSub, Sub.sub]
  rw [← zero_add ((VEC A B).fst * (VEC A B).fst), ← zero_add ((VEC A B).fst * (VEC A B).fst), ← neg_zero, ← i]
  ring

theorem Pythagoras_of_perp_foot (A B : P) {l : Line P} (h : B LiesOn l) : (SEG A (perp_foot A l)).length ^ 2 + (SEG B (perp_foot A l)).length ^ 2 = (SEG A B).length ^ 2 := by
  sorry

end Pythagoras

end EuclidGeom