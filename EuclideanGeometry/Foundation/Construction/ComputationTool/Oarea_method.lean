import EuclideanGeometry.Foundation.Axiom.Linear.Ratio
import EuclideanGeometry.Foundation.Axiom.Position.Orientation

noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type _} [EuclideanPlane P]

section oarea_method

theorem wedge_add_wedge_eq_wedge_add_wedge (A B C D : P) : wedge A B C + wedge C D A = wedge B C D + wedge D A B := by
  unfold wedge
  rw[←vec_sub_vec A C D, ←neg_vec A C, ←vec_sub_vec A B C, ←vec_sub_vec A B D, ←neg_vec A D, ←vec_sub_vec A D B, det_neg_right_eq_neg_det, det_sub_eq_det, det_sub_left_eq_det_sub_det, det_sub_right_eq_det_sub_det, det_sub_right_eq_det_sub_det, det_sub_right_eq_det_sub_det,← det_eq_neg_det,det_self_eq_zero,det_neg_self_eq_zero,det_eq_neg_det (VEC A C) (VEC A B),det_neg_eq_neg_det,←det_eq_neg_det (VEC A B) (VEC A D)]
  ring

theorem wedge_eq_wedge_add_wedge_of_colinear (A B C D : P) (colin : colinear A B C) : wedge D A C = wedge D B C + wedge D A B := by
  rw[← wedge231 D B C, ← wedge_add_wedge_eq_wedge_add_wedge,← wedge231 C D A, (colinear_iff_wedge_eq_zero A B C).mp colin]
  field_simp

theorem wedge_eq_divratio_mul_wedge_of_colinear (A B C D : P) (colin : colinear A B C) (cnea : C ≠ A) : wedge A B D = (divratio A B C) * wedge A C D := by
  unfold wedge
  rw [vec_eq_vec_smul_ratio A B C colin cnea, det_smul_left_eq_mul_det]

theorem odist_eq_divratio_mul_odist (A B C : P) (dl : DirLine P) (colin : colinear A B C) (cnea : C ≠ A) (aisondl : A LiesOn dl) : odist B dl = (divratio A B C) * odist C dl := by
  have h0 : odist' B (Ray.mk_pt_dirline A dl aisondl)= odist B (Ray.mk_pt_dirline A dl aisondl).toDirLine := rfl
  have h1 : odist B dl = odist' B (Ray.mk_pt_dirline A dl aisondl) := by
    rw[h0,ray_of_pt_dirline_todirline_eq_dirline A dl aisondl]
  have h2 : odist' C (Ray.mk_pt_dirline A dl aisondl) = odist C (Ray.mk_pt_dirline A dl aisondl).toDirLine := rfl
  have h3 : odist C dl = odist' C (Ray.mk_pt_dirline A dl aisondl) := by
    rw [h2,ray_of_pt_dirline_todirline_eq_dirline A dl aisondl]
  rw [h1, h3]
  unfold odist'
  have h4 : (Ray.mk_pt_dirline A dl aisondl).source = A := rfl
  rw [h4, vec_eq_vec_smul_ratio A B C colin cnea, det_smul_right_eq_mul_det]

theorem  wedge_eq_divratio_mul_wedge_of_colinear_colinear (A B C D E : P) (colin : colinear A B C) (cnea : C ≠ A) (colin' : colinear A D E) : wedge D B E = (divratio A B C) * wedge D C E := by
  rw[← wedge231 D B E, wedge_eq_wedge_add_wedge_of_colinear E A D B (perm_colinear_trd_fst_snd colin'), ← wedge231 D C E, wedge_eq_wedge_add_wedge_of_colinear E A D C (perm_colinear_trd_fst_snd colin'), wedge213 A B D, wedge231 A B E, wedge213 A C D, wedge231 A C E,wedge_eq_divratio_mul_wedge_of_colinear A B C D colin cnea,wedge_eq_divratio_mul_wedge_of_colinear A B C E colin cnea]
  ring

theorem ratio_eq_wedge_div_wedge_of_colinear_colinear_notcoliear (A B C D E : P) (colin : colinear A B C) (cnea : C ≠ A) (colin' : colinear A D E) (ncolin : ¬ colinear D C E) : divratio A B C = (wedge D B E) / (wedge D C E) := by
  rw [wedge_eq_divratio_mul_wedge_of_colinear_colinear A B C D E colin cnea colin']
  have h0 : ¬ wedge D C E = 0 := by
    rw[(colinear_iff_wedge_eq_zero D C E).symm]
    exact ncolin
  field_simp

end oarea_method

end EuclidGeom
