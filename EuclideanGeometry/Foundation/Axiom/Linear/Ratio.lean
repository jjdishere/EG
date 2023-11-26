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
  field_simp

theorem ratio_is_real (A B C : P) (colin : colinear A B C) (cnea : C ≠ A) : (VEC A B)/(VEC A C) = divratio A B C := by
  have h0 : (divratio A B C : ℂ).re = ((VEC A B)/(VEC A C)).re := rfl
  have h1 : (divratio A B C : ℂ).im = ((VEC A B)/(VEC A C)).im := by
    rw [ratio_is_real' A B C colin cnea]
    field_simp
  exact Complex.ext h0 h1.symm

theorem vec_eq_vec_smul_ratio (A B C : P) (colin : colinear A B C) (cnea : C ≠ A) : VEC A B = (divratio A B C) • (VEC A C) := by
  have h0 : VEC A C ≠ 0 := (ne_iff_vec_ne_zero A C).mp cnea
  have h1 : VEC A B = (VEC A B)/(VEC A C) * VEC A C := by
    field_simp
  rw [h1, ratio_is_real A B C colin cnea]
  field_simp

end ratio

end EuclidGeom
