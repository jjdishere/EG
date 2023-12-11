import EuclideanGeometry.Foundation.Axiom.Linear.Line

noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P]

section ratio

/-
Below is the definition of divratio using ddist, which I think might not be a good idea.

def divratio (A B C : P) (colin : colinear A B C) (cnea : C ≠ A) : ℝ := (DirLine.ddist (B := B) (DirLine.pt_pt_maximal cnea (flip_colinear_snd_trd (triv_colinear A C))) (DirLine.pt_pt_maximal cnea (flip_colinear_snd_trd colin))) / (DirLine.ddist (DirLine.pt_pt_maximal cnea (flip_colinear_snd_trd (triv_colinear A C))) (DirLine.pt_pt_maximal cnea (perm_colinear_trd_fst_snd (triv_colinear C A))))
-/

def divratio (A B C : P) : ℝ := ((VEC A B)/(VEC A C)).1

theorem ratio_is_real' (A B C : P) (colin : colinear A B C) (cnea : C ≠ A) : ((VEC A B)/(VEC A C)).2 = 0 := by
  have h0 : colinear A C B := flip_colinear_snd_trd colin
  rw [colinear_iff_eq_smul_vec_of_ne cnea] at h0
  rcases h0 with ⟨r , h1⟩
  have h2 : VEC A C ≠ 0 := (ne_iff_vec_ne_zero A C).mp cnea
  rw [h1]
  calc
    (r • VEC A C / VEC A C).im = ((r : ℂ) • VEC A C / VEC A C).im := rfl
    _ = 0 := by
      rw [Vec.smul_cdiv_cancel _ h2]
      rfl

theorem ratio_is_real (A B C : P) (colin : colinear A B C) (cnea : C ≠ A) : (VEC A B)/(VEC A C) = divratio A B C := by
  have h0 : (divratio A B C : ℂ).re = ((VEC A B)/(VEC A C)).re := rfl
  have h1 : (divratio A B C : ℂ).im = ((VEC A B)/(VEC A C)).im := by
    rw [ratio_is_real' A B C colin cnea]
    simp
  exact Complex.ext h0 h1.symm

theorem vec_eq_vec_smul_ratio (A B C : P) (colin : colinear A B C) (cnea : C ≠ A) : VEC A B = (divratio A B C) • (VEC A C) := by
  have h0 : VEC A C ≠ 0 := (ne_iff_vec_ne_zero A C).mp cnea
  have h1 : VEC A B = ((VEC A B) / (VEC A C)) • VEC A C := by
    field_simp
  rw [h1, ratio_is_real A B C colin cnea]
  field_simp

theorem ratio_eq_ratio_div_ratio_minus_one (A B C : P) (cnea : C ≠ A) (colin : colinear A B C) : divratio B A C = (divratio A B C) / (divratio A B C - 1) := by
  have h0 : VEC B A = (-divratio A B C) • VEC A C := by
    rw [← neg_vec A B, vec_eq_vec_smul_ratio A B C colin cnea]
    field_simp
  have h1 : VEC B C = (1 - divratio A B C) • VEC A C := by
    rw [← vec_add_vec B A C, h0]
    have h2 : VEC A C = (1 : ℝ) • VEC A C := by
      field_simp
    nth_rw 2 [h2]
    rw[← add_smul]
    have h3 : -divratio A B C + 1 = 1 - divratio A B C := by
      ring
    rw[h3]
  have h4 : VEC B A / VEC B C = (((divratio A B C / (divratio A B C - 1)) : ℝ ) : ℂ) := by
    rw [h0, h1]
    have h5 : VEC A C ≠ 0 := (ne_iff_vec_ne_zero A C).mp cnea
    field_simp
    norm_cast
    rw [Vec.neg_cdiv, Vec.smul_cdiv, Vec.cdiv_self h5, neg_div, ← div_neg]
    simp
  conv =>
    lhs
    unfold divratio
  rw [h4]
  rw [Complex.ofReal_re]

theorem pt_eq_of_ratio_eq_of_ne_ne (A B C D : P) (cned : C ≠ D) (dnea : D ≠ A) (dneb : D ≠ B) (colinacd : colinear A C D) (colinbcd : colinear B C D) (req : divratio A C D = divratio B C D) : A = B := by
  have h0 : divratio C A D = divratio C B D := by
    rw [ratio_eq_ratio_div_ratio_minus_one A C D dnea colinacd, req, ratio_eq_ratio_div_ratio_minus_one B C D dneb colinbcd]
  have h1 : VEC C A = VEC C B := by
    rw [vec_eq_vec_smul_ratio C A D (flip_colinear_fst_snd colinacd) cned.symm, vec_eq_vec_smul_ratio C B D (flip_colinear_fst_snd colinbcd) cned.symm, h0]
  rw [← start_vadd_vec_eq_end C A, h1, start_vadd_vec_eq_end C B]

theorem ratio_eq_zero_of_point_eq1 (A B : P) : divratio A A B = 0 := by
  unfold divratio
  rw [vec_same_eq_zero]
  field_simp

theorem ratio_eq_zero_of_point_eq2 (A B : P) : divratio A B A = 0 := by
  unfold divratio
  rw [vec_same_eq_zero]
  field_simp

end ratio

end EuclidGeom
