import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

def perpendicular (l₁ l₂: LinearObj P) : Prop := l₁.toProj = l₂.toProj.perp

scoped infix : 50 "IsPerpendicularTo" => perpendicular
scoped infix : 50 "⟂" => perpendicular

namespace perpendicular

@[simp]
protected theorem irrefl {l : LinearObj P}  : ¬ (l ⟂ l) := by 
  intro h
  dsimp only [perpendicular] at h
  dsimp only [Proj.perp] at h
  have h0: 1=Proj.I := by
    nth_rw 1 [←one_mul (LinearObj.toProj l)] at h
    exact mul_right_cancel h
  exact Proj.one_ne_I h0

protected theorem symm {l₁ l₂ : LinearObj P} (h :l₁ ⟂ l₂) : (l₂ ⟂ l₁) := by
  unfold perpendicular; dsimp only [Proj.perp]
  unfold perpendicular at h; dsimp only [Proj.perp] at h
  have h0 : (Proj.I)*(Proj.I) = 1 := by 
     exact Proj.I_mul_I_eq_one_of_Proj
  rw[h,←mul_assoc,h0,one_mul]

end perpendicular

section Perpendicular_and_parallel

theorem parallel_of_perp_perp {l₁ l₂ l₃ : LinearObj P} : (l₁ ⟂ l₂) → (l₂ ⟂ l₃) → (l₁ ∥ l₃) := by
  unfold perpendicular parallel
  intro h₁ h₂
  rw [h₂] at h₁
  simp at h₁
  exact h₁

theorem perp_of_parallel_perp {l₁ l₂ l₃ : LinearObj P} : (l₁ ∥ l₂) → (l₂ ⟂ l₃) → (l₁ ⟂ l₃) := by
  unfold perpendicular parallel
  intro h1 h2
  rw[h1,h2]

theorem perp_of_perp_parallel {l₁ l₂ l₃ : LinearObj P} : (l₁ ⟂ l₂) → (l₂ ∥ l₃) → (l₁ ⟂ l₃) := by
  unfold perpendicular parallel
  intro h1 h2
  rw[h1,h2]  

theorem toProj_ne_toProj_of_perp {l₁ l₂: LinearObj P} : (l₁ ⟂ l₂) → (l₁.toProj ≠ l₂.toProj) := by
  intro h0
  unfold perpendicular at h0
  by_contra h1
  rw[h1] at h0
  dsimp only [Proj.perp] at h0
  have h2 : 1=Proj.I:= by
    nth_rw 1 [←one_mul (LinearObj.toProj l₂)] at h0
    exact mul_right_cancel h0
  exact Proj.one_ne_I h2

theorem not_parallel_of_perp {l₁ l₂: LinearObj P} : (l₁⟂l₂) → ¬(l₁∥l₂) := by
  unfold parallel
  exact toProj_ne_toProj_of_perp

end Perpendicular_and_parallel

section Perpendicular_constructions

def perp_line (A : P) (l : Line P) := Line.mk_pt_proj A (l.toProj.perp)

@[simp]
theorem toProj_of_perp_line_eq_toProj_perp (A : P) (l : Line P) : (perp_line A l).toProj = l.toProj.perp := (proj_eq_of_mk_pt_proj A _)

theorem perp_foot_preparation (A : P) (l : Line P) : l.toProj ≠ (perp_line A l).toProj := by
  rw[toProj_of_perp_line_eq_toProj_perp]
  unfold Proj.perp
  by_contra h0
  have h1 : 1=Proj.I:= by
    nth_rw 1 [←one_mul (Line.toProj l)] at h0
    exact mul_right_cancel h0
  exact Proj.one_ne_I h1

def perp_foot (A : P) (l : Line P) : P := Line.inx l (perp_line A l) (perp_foot_preparation A l).symm

def dist_pt_line (A : P) (l : Line P) := Seg.length (SEG A (perp_foot A l))

theorem perp_foot_eq_self_iff_lies_on (A : P) (l : Line P) : perp_foot A l = A ↔ A LiesOn l := by
  constructor
  .
    intro h
    unfold perp_foot at h
    rw [← h]
    apply (Line.inx_is_inx _).1
  .
    intro A_on_l
    have A_on_perp_line_A_l:(A LiesOn perp_line A l) := by
      unfold perp_line
      exact (pt_lies_on_of_mk_pt_proj A (Proj.perp (Line.toProj l)))
    have h:(perp_foot A l LiesOn l) := by
      unfold perp_foot
      apply (Line.inx_is_inx _).1
    have h':(perp_foot A l LiesOn perp_line A l) := by
      unfold perp_foot
      apply (Line.inx_is_inx _).2
    by_contra n
    have e : l = perp_line A l := by
      nth_rw 1 [← eq_line_of_pt_pt_of_ne n A_on_l h]
      rw [← eq_line_of_pt_pt_of_ne n A_on_perp_line_A_l h']
    have t : (l.toProj ≠ (perp_line A l).toProj) := by
      apply perp_foot_preparation
    apply t
    nth_rw 1 [e]

theorem line_of_self_perp_foot_eq_perp_line_of_not_lies_on {A : P} {l : Line P} (h : ¬ A LiesOn l) : LIN A (perp_foot A l) ((perp_foot_eq_self_iff_lies_on A l).mp.mt  h) = perp_line A l := by
  have h0 : A LiesOn perp_line A l := by 
    dsimp only [perp_line]
    apply (pt_lies_on_of_mk_pt_proj A l.toProj.perp)
  have h1 : perp_foot A l LiesOn perp_line A l := (Line.inx_is_inx (perp_foot_preparation A l).symm).2
  have h2 : perp_foot A l≠A := by
    rw[←perp_foot_eq_self_iff_lies_on A l] at h
    exact h
  apply eq_line_of_pt_pt_of_ne h2 h0 h1

theorem dist_eq_zero_iff_lies_on (A : P) (l : Line P) : dist_pt_line A l = 0 ↔ A LiesOn l := by
  rw[←perp_foot_eq_self_iff_lies_on A l]
  unfold dist_pt_line
  rw[←triv_iff_length_eq_zero]
  simp

end Perpendicular_constructions

end EuclidGeom