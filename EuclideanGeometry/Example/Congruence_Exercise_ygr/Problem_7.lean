import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Wuwowuji_Problem_1_7
/-
Segment $AD$ and $BC$ intersect at $O$, $∠ ACB = ∠ ADB$, $OA = OB$.

Prove that $AD = BC$.
-/
-- $AD$ and $BC$ intersect at $O$.
variable {A B C D O: P} {h1 : O LiesInt (SEG A D)} {h2 : O LiesInt (SEG B C)}
-- nondegenerate
variable {hnd1 : ¬ collinear C B A} {hnd2 : ¬ collinear D A B}
lemma a_ne_b : A ≠ B := by sorry
lemma a_ne_c : A ≠ C := by sorry
lemma a_ne_d : A ≠ D := by sorry
lemma b_ne_c : B ≠ C := by sorry
lemma b_ne_d : B ≠ D := by sorry
lemma c_ne_d : C ≠ D := by sorry
-- $∠ ACB = ∠ ADB$.
variable {hang : ∠ A C B a_ne_c.symm b_ne_c.symm = ∠ A D B a_ne_d.symm b_ne_d.symm}
-- $OA = OB$.
variable {hseg : (SEG O A).length = (SEG O B).length}
-- State the main goal.
theorem Wuwowuji_Problem_1_7 : (SEG A D).length = (SEG B C).length := by
  -- nondegenerate
  have o_ne_a : O ≠ A := by sorry
  have o_ne_b : O ≠ B := by sorry
  have o_ne_c : O ≠ C := by sorry
  have o_ne_d : O ≠ D := by sorry
  have hnd3 : ¬ collinear O A B := by sorry
  -- $▵ OAB$ is isoceles because $OA = OB$.
  have hisoc : (TRI_nd O A B hnd3).1.IsIsoceles := by
    calc
      _ = (SEG O B).length := length_of_rev_eq_length'
      _ = _ := hseg.symm
  -- Use AAS to prove $▵ CBA ≅ₐ ▵ DAB$.
  have h : (TRI_nd C B A hnd1) ≅ₐ (TRI_nd D A B hnd2) := by
    apply Triangle_nd.acongr_of_AAS
    · -- $∠ BCA = -∠ ADB$ because $∠ ACB = ∠ ADB$.
      calc
        _ = -∠ A C B a_ne_c.symm b_ne_c.symm := by apply neg_value_of_rev_ang
        _ = -∠ A D B a_ne_d.symm b_ne_d.symm := by rw [hang]
    · -- $∠ ABC = ∠ ABO = -∠ OBA = -∠ BAO = -∠ BAD$.
      calc
        _ = ∠ A B O a_ne_b o_ne_b := by
          unfold value_of_angle_of_three_point_nd
          congr
          apply eq_ang_of_liesint_liesint
          · apply Seg_nd.target_lies_int_toray (seg_nd := (SEG_nd B A a_ne_b))
          · exact Seg_nd.lies_int_toray_of_lies_int (seg_nd := (SEG_nd B C b_ne_c.symm)) h2
        _ = -∠ O B A o_ne_b a_ne_b := by apply neg_value_of_rev_ang
        _ = -∠ B A O a_ne_b.symm o_ne_a := by
          have : ∠ O B A o_ne_b a_ne_b = ∠ B A O a_ne_b.symm o_ne_a := (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri.mp hisoc).symm
          rw [this]
        _ = _ := by
          have : ANG B A O a_ne_b.symm o_ne_a = ANG B A D a_ne_b.symm a_ne_d.symm := by
            apply eq_ang_of_liesint_liesint
            · apply Seg_nd.target_lies_int_toray (seg_nd := (SEG_nd A B a_ne_b.symm))
            · apply (pt_lies_int_ray_of_pt_pt_iff_pt_lies_int_ray_of_pt_pt a_ne_d.symm o_ne_a).mpr
              exact Seg_nd.lies_int_toray_of_lies_int (seg_nd := (SEG_nd A D a_ne_d.symm)) h1
          unfold value_of_angle_of_three_point_nd
          rw [this]
          rfl
    · -- $BA = AB$ is trivial.
      exact length_of_rev_eq_length'
  -- $AD = BC$ follows from the congruence.
  calc
    _ = (SEG D A).length := length_of_rev_eq_length'
    _ = (SEG C B).length := h.edge₃.symm
    _ = _ := length_of_rev_eq_length'

end Wuwowuji_Problem_1_7
