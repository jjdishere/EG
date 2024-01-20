import EuclideanGeometry.Foundation.Axiom.Linear.Ratio
import EuclideanGeometry.Foundation.Axiom.Position.Orientation

noncomputable section
namespace EuclidGeom

open Classical

variable {P : Type*} [EuclideanPlane P]

section oarea_method

theorem wedge_add_wedge_eq_wedge_add_wedge (A B C D : P) : wedge A B C + wedge C D A = wedge B C D + wedge D A B := by
  unfold wedge
  rw[←vec_sub_vec A C D, ←neg_vec A C, ←vec_sub_vec A B C, ←vec_sub_vec A B D, ←neg_vec A D, ←vec_sub_vec A D B]
  simp only [map_neg, LinearMap.neg_apply, map_sub]
  simp only [LinearMap.sub_apply, Vec.det_self, sub_zero, neg_zero]
  rw [← Vec.det_skew (VEC A C) (VEC A B),← Vec.det_skew (VEC A D) (VEC A B), ← Vec.det_skew (VEC A D) (VEC A C)]
  ring

theorem wedge_eq_wedge_add_wedge_of_collinear (A B C D : P) (colin : Collinear A B C) : wedge D A C = wedge D B C + wedge D A B := by
  rw[← wedge312 D B C, ← wedge_add_wedge_eq_wedge_add_wedge,← wedge312 C D A, (collinear_iff_wedge_eq_zero A B C).mp colin]
  field_simp

theorem wedge_eq_divratio_mul_wedge_of_collinear (A B C D : P) (colin : Collinear A B C) [cnea : PtNe C A] : wedge A B D = (divratio A B C) * wedge A C D := by
  unfold wedge
  rw [vec_eq_vec_smul_ratio A B C colin]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem odist_eq_divratio_mul_odist (A B C : P) (dl : DirLine P) (colin : Collinear A B C) [cnea : PtNe C A] (aisondl : A LiesOn dl) : odist B dl = (divratio A B C) * odist C dl := by
  have h0 : odist' B (Ray.mk_pt_dirline A dl aisondl)= odist B (Ray.mk_pt_dirline A dl aisondl).toDirLine := rfl
  have h1 : odist B dl = odist' B (Ray.mk_pt_dirline A dl aisondl) := by
    rw[h0,ray_of_pt_dirline_toDirLine_eq_dirline A dl aisondl]
  have h2 : odist' C (Ray.mk_pt_dirline A dl aisondl) = odist C (Ray.mk_pt_dirline A dl aisondl).toDirLine := rfl
  have h3 : odist C dl = odist' C (Ray.mk_pt_dirline A dl aisondl) := by
    rw [h2,ray_of_pt_dirline_toDirLine_eq_dirline A dl aisondl]
  rw [h1, h3]
  unfold odist'
  have h4 : (Ray.mk_pt_dirline A dl aisondl).source = A := rfl
  rw [h4, vec_eq_vec_smul_ratio A B C colin]
  simp only [map_smul, smul_eq_mul]

theorem  wedge_eq_divratio_mul_wedge_of_collinear_collinear (A B C D E : P) (colin : Collinear A B C) [cnea : PtNe C A] (colin' : Collinear A D E) : wedge D B E = (divratio A B C) * wedge D C E := by
  rw[← wedge312 D B E, wedge_eq_wedge_add_wedge_of_collinear E A D B (Collinear.perm₃₁₂ colin'), ← wedge312 D C E, wedge_eq_wedge_add_wedge_of_collinear E A D C (Collinear.perm₃₁₂ colin'), wedge213 A B D, wedge312 A B E, wedge213 A C D, wedge312 A C E,wedge_eq_divratio_mul_wedge_of_collinear A B C D colin,wedge_eq_divratio_mul_wedge_of_collinear A B C E colin]
  ring

theorem ratio_eq_wedge_div_wedge_of_collinear_collinear_notcoliear (A B C D E : P) (colin : Collinear A B C) [cnea : PtNe C A] (colin' : Collinear A D E) (ncolin : ¬ Collinear D C E) : divratio A B C = (wedge D B E) / (wedge D C E) := by
  rw [wedge_eq_divratio_mul_wedge_of_collinear_collinear A B C D E colin colin']
  have h0 : ¬ wedge D C E = 0 := by
    rw[(collinear_iff_wedge_eq_zero D C E).symm]
    exact ncolin
  field_simp

end oarea_method

end EuclidGeom
