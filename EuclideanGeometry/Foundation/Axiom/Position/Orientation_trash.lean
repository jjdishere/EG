import EuclideanGeometry.Foundation.Axiom.Position.Orientation

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem liesonleft_iff_liesonright_reverse {A : P} {l : DirLine P} : A LiesOnLeft l ↔ A LiesOnRight l.reverse := by
  have : odist A l.reverse = -odist A l := by
    apply odist_reverse_eq_neg_odist A l
  unfold IsOnLeftSide
  unfold IsOnRightSide
  constructor
  · intro P
    simp only [this]
    linarith
  · intro P
    simp only [this] at P
    linarith

theorem DirLine.lieson_or_liesonleft_or_liesonright (A : P) (l : DirLine P) : (A LiesOn l) ∨ (A LiesOnLeft l) ∨ (A LiesOnRight l) := by sorry
--Guan Nailin

lemma eq_toDir_of_parallel_and_IsOnLL {A B C D : P} [bnea : PtNe B A] [cnea : PtNe C A] [dneb : PtNe D B] (para : (SEG_nd A C) ∥ (SEG_nd B D)) (side : C LiesOnLeft (SEG_nd A B) ∧ D LiesOnLeft (SEG_nd A B)) : (SEG_nd A C).toDir = (SEG_nd B D).toDir := by
  have Proj : (SEG_nd A C ).toProj = (SEG_nd B D ).toProj := by
    exact para
  have eq_or_neg : ((SEG_nd A C ).toDir = (SEG_nd B D ).toDir) ∨ ((SEG_nd A C ).toDir = -(SEG_nd B D ).toDir) := by
    apply Dir.toProj_eq_toProj_iff.mp
    exact Proj
  rcases eq_or_neg with eq|neg
  · exact eq
  · unfold IsOnLeftSide at side
    have _ : (SEG A B).length > 0 := (SEG_nd A B).length_pos
    have c : odist C (SEG_nd A B) > 0 := side.1
    have d : odist D (SEG_nd A B) > 0 := side.2
    have w1 : wedge A B C > 0 := by
      calc
      _= (SEG A B).length * odist' C (RAY A B) := by exact wedge_eq_length_mul_odist' A B C
        _= (SEG A B).length * odist C (SEG_nd A B) := by rfl
        _>0 := by positivity
    have w2 : wedge A B D > 0 := by
      calc
        _= (SEG A B).length * odist' D (RAY A B) := by exact wedge_eq_length_mul_odist' A B D
        _= (SEG A B).length * odist D (SEG_nd A B) := by rfl
        _>0 := by positivity
    have det1 : Vec.det (VEC A B) (VEC A C) > 0 := by
      exact w1
    have det2 : Vec.det (VEC B A) (VEC B D) < 0 := by
      calc
        _= wedge B A D := by rfl
        _= -wedge A B D := by exact wedge213 A B D
        _<0 := by
          simp only [Left.neg_neg_iff]
          exact w2
    have dir : (VEC_nd A C ).toDir = (VEC_nd D B).toDir := by
      have : (SEG_nd A C).toDir = (SEG_nd D B).toDir := by
        simp only [neg]
        symm
        calc
          _=(SEG_nd B D).reverse.toDir := by congr
          _=_ := by exact EuclidGeom.SegND.toDir_of_rev_eq_neg_toDir
      exact this
    have dir' : (VEC_nd A C ).SameDir (VEC_nd D B ) := by
      apply VecND.toDir_eq_toDir_iff.mp
      exact dir
    unfold VecND.SameDir at dir'
    rcases dir' with ⟨x,h⟩
    have x_pos : x > 0 := h.1
    have h : Vec.det (VEC A B) (VEC A C) = x * Vec.det (VEC B A) (VEC B D) := by
      calc
        _= Vec.det (VEC A B) (x • (VEC D B)) := by
          congr
          exact h.2
        _= x * Vec.det (VEC A B) (VEC D B) := by
          simp only [LinearMap.map_smul]
          rfl
        _= x * Vec.det (VEC A B) (-(VEC B D)) := by
          congr
          simp
        _= x * -Vec.det (VEC A B) (VEC B D) := by
          have n: Vec.det (VEC A B) (-(VEC B D)) = -Vec.det (VEC A B) (VEC B D) := by
            simp only [LinearMap.map_neg]
          simp only [n]
        _= x * -Vec.det (-(VEC B A)) (VEC B D) := by
          congr
          simp
        _= x * Vec.det (VEC B A) (VEC B D) := by
          have m: Vec.det (-(VEC B A)) (VEC B D) = -Vec.det (VEC B A) (VEC B D) := by
            simp only [LinearMap.map_neg]
            rfl
          simp only [m]
          simp only [neg_neg]
    absurd det1
    simp only [gt_iff_lt, not_lt]
    simp only [h]
    have : x * (-Vec.det (VEC B A) (VEC B D)) > 0 := by
      have : -Vec.det (VEC B A) (VEC B D) > 0 := by
        linarith
      positivity
    linarith

lemma eq_toDir_of_parallel_and_IsOnRR {A B C D : P} [bnea : PtNe B A] [cnea : PtNe C A] [dneb : PtNe D B] (para : (SEG_nd A C) ∥ (SEG_nd B D)) (side : C LiesOnRight (SEG_nd A B) ∧ D LiesOnRight (SEG_nd A B)) : (SEG_nd A C).toDir = (SEG_nd B D).toDir := by
  have Proj : (SEG_nd A C ).toProj = (SEG_nd B D ).toProj := by
    exact para
  have eq_or_neg : ((SEG_nd A C ).toDir = (SEG_nd B D ).toDir) ∨ ((SEG_nd A C ).toDir = -(SEG_nd B D ).toDir) := by
    apply Dir.toProj_eq_toProj_iff.mp
    exact Proj
  rcases eq_or_neg with eq|neg
  · exact eq
  · unfold IsOnRightSide at side
    have _ : (SEG A B).length > 0 := (SEG_nd A B).length_pos
    have c : odist C (SEG_nd A B) < 0 := side.1
    have d : odist D (SEG_nd A B) < 0 := side.2
    have w1 : wedge A B C < 0 := by
      calc
      _= (SEG A B).length * odist' C (RAY A B) := by exact wedge_eq_length_mul_odist' A B C
        _= (SEG A B).length * odist C (SEG_nd A B) := by rfl
        _= -((SEG A B).length * -odist C (SEG_nd A B)) := by simp only [Seg.length_eq_dist, mul_neg,neg_neg]
        _<0 := by
          have : (SEG A B).length * -odist C (SEG_nd A B) > 0 := by
            have : -odist C (SEG_nd A B) > 0 := by linarith
            positivity
          linarith
    have w2 : wedge A B D < 0 := by
      calc
        _= (SEG A B).length * odist' D (RAY A B) := by exact wedge_eq_length_mul_odist' A B D
        _= (SEG A B).length * odist D (SEG_nd A B) := by rfl
        _<0 := by
          have : (SEG A B).length * (-odist D (SEG_nd A B)) > 0 := by
            have : -odist D (SEG_nd A B) > 0 := by linarith
            positivity
          have : (SEG A B).length * odist D (SEG_nd A B) = - ((SEG A B).length * (-odist D (SEG_nd A B))) := by simp only [Seg.length_eq_dist,mul_neg, neg_neg]
          simp only [this]
          linarith
    have det1 : Vec.det (VEC A B) (VEC A C) < 0 := by
      exact w1
    have det2 : Vec.det (VEC B A) (VEC B D) > 0 := by
      calc
        _= wedge B A D := by rfl
        _= -wedge A B D := by exact wedge213 A B D
        _>0 := by
          simp only [gt_iff_lt, Left.neg_pos_iff]
          exact w2
    have dir : (VEC_nd A C ).toDir = (VEC_nd D B).toDir := by
      have : (SEG_nd A C).toDir = (SEG_nd D B).toDir := by
        simp only [neg]
        symm
        calc
          _=(SEG_nd B D).reverse.toDir := by congr
          _=_ := by exact EuclidGeom.SegND.toDir_of_rev_eq_neg_toDir
      exact this
    have dir' : (VEC_nd A C ).SameDir (VEC_nd D B ) := by
      apply VecND.toDir_eq_toDir_iff.mp
      exact dir
    unfold VecND.SameDir at dir'
    rcases dir' with ⟨x,h⟩
    have x_pos : x > 0 := h.1
    have h : Vec.det (VEC A B) (VEC A C) = x * Vec.det (VEC B A) (VEC B D) := by
      calc
        _= Vec.det (VEC A B) (x • (VEC D B)) := by
          congr
          exact h.2
        _= x * Vec.det (VEC A B) (VEC D B) := by
          simp only [LinearMap.map_smul]
          rfl
        _= x * Vec.det (VEC A B) (-(VEC B D)) := by
          congr
          simp
        _= x * -Vec.det (VEC A B) (VEC B D) := by
          have n: Vec.det (VEC A B) (-(VEC B D)) = -Vec.det (VEC A B) (VEC B D) := by
            simp only [LinearMap.map_neg]
          simp only [n]
        _= x * -Vec.det (-(VEC B A)) (VEC B D) := by
          congr
          simp
        _= x * Vec.det (VEC B A) (VEC B D) := by
          have m: Vec.det (-(VEC B A)) (VEC B D) = -Vec.det (VEC B A) (VEC B D) := by
            simp only [LinearMap.map_neg]
            rfl
          simp only [m]
          simp only [neg_neg]
    absurd det1
    simp only [not_lt]
    simp only [h]
    have : x * (Vec.det (VEC B A)) (VEC B D) > 0 := by
      positivity
    linarith

theorem eq_toDir_of_parallel_and_IsOnSameSide {A B C D : P} [bnea : PtNe B A] [cnea : PtNe C A] [dneb : PtNe D B] (para : (SEG_nd A C) ∥ (SEG_nd B D)) (side : IsOnSameSide C D (SEG_nd A B)) : (SEG_nd A C).toDir = (SEG_nd B D).toDir := by
  unfold IsOnSameSide at side
  unfold IsOnSameSide' at side
  have h : C LiesOnLeft (SEG_nd A B) ∧ D LiesOnLeft (SEG_nd A B) ∨ C LiesOnRight (SEG_nd A B) ∧ D LiesOnRight (SEG_nd A B) := by exact side
  rcases h with ll|rr
  · exact (eq_toDir_of_parallel_and_IsOnLL para ll)
  · exact (eq_toDir_of_parallel_and_IsOnRR para rr)


--Guan Nailin
lemma neg_toDir_of_parallel_and_IsOnLR {A B C D : P} [bnea : PtNe B A] [cnea : PtNe C A] [dneb : PtNe D B] (para : (SEG_nd A C) ∥ (SEG_nd B D)) (side : C LiesOnLeft (SEG_nd A B ) ∧ D LiesOnRight (SEG_nd A B)) : (SEG_nd A C).toDir = -(SEG_nd B D).toDir := by
  have Proj : (SEG_nd A C ).toProj = (SEG_nd B D ).toProj := by
    exact para
  have eq_or_neg : ((SEG_nd A C ).toDir = (SEG_nd B D ).toDir) ∨ ((SEG_nd A C ).toDir = -(SEG_nd B D ).toDir) := by
    apply Dir.toProj_eq_toProj_iff.mp
    exact Proj
  rcases eq_or_neg with eq|neg
  · unfold IsOnLeftSide at side
    unfold IsOnRightSide at side
    have _ : (SEG A B).length > 0 := (SEG_nd A B).length_pos
    have c : odist C (SEG_nd A B) > 0 := side.1
    have d : odist D (SEG_nd A B) < 0 := side.2
    have w1 : wedge A B C > 0 := by
      calc
      _= (SEG A B).length * odist' C (RAY A B) := by exact wedge_eq_length_mul_odist' A B C
        _= (SEG A B).length * odist C (SEG_nd A B) := by rfl
        _>0 := by positivity
    have w2 : wedge A B D < 0 := by
      calc
        _= (SEG A B).length * odist' D (RAY A B) := by exact wedge_eq_length_mul_odist' A B D
        _= (SEG A B).length * odist D (SEG_nd A B) := by rfl
        _<0 := by
          have : (SEG A B).length * (-odist D (SEG_nd A B)) > 0 := by
            have : -odist D (SEG_nd A B) > 0 := by linarith
            positivity
          have : (SEG A B).length * odist D (SEG_nd A B) = - ((SEG A B).length * (-odist D (SEG_nd A B))) := by simp only [Seg.length_eq_dist,mul_neg, neg_neg]
          simp only [this]
          linarith
    have det1 : Vec.det (VEC A B) (VEC A C) > 0 := by
      exact w1
    have det2 : Vec.det (VEC B A) (VEC B D) > 0 := by
      calc
        _= wedge B A D := by rfl
        _= -wedge A B D := by exact wedge213 A B D
        _>0 := by
          simp only [gt_iff_lt, Left.neg_pos_iff]
          exact w2
    have dir : (VEC_nd A C ).toDir = (VEC_nd B D ).toDir := by exact eq
    have dir' : (VEC_nd A C ).SameDir (VEC_nd B D ) := by
      apply VecND.toDir_eq_toDir_iff.mp
      exact dir
    unfold VecND.SameDir at dir'
    rcases dir' with ⟨x,h⟩
    have x_pos : x > 0 := h.1
    have h : Vec.det (VEC A B) (VEC A C) = -x * Vec.det (VEC B A) (VEC B D) := by
      calc
        _= Vec.det (VEC A B) (x • (VEC B D)) := by
          congr
          exact h.2
        _= x * Vec.det (VEC A B) (VEC B D) := by
          simp only [LinearMap.map_smul]
          rfl
        _= x * Vec.det (-(VEC B A)) (VEC B D) := by
          congr
          simp
        _= x * -Vec.det (VEC B A) (VEC B D) := by
          have m: Vec.det (-(VEC B A)) (VEC B D) = -Vec.det (VEC B A) (VEC B D) := by
            simp only [LinearMap.map_neg]
            rfl
          simp only [m]
        _=_ := by simp only [mul_neg, neg_mul]
    absurd det1
    simp only [gt_iff_lt, not_lt]
    simp only [h]
    simp only [neg_mul, Left.neg_nonpos_iff]
    positivity
  · exact neg

lemma neg_toDir_of_parallel_and_IsOnRL {A B C D : P} [bnea : PtNe B A] [cnea : PtNe C A] [dneb : PtNe D B] (para : (SEG_nd A C) ∥ (SEG_nd B D)) (side : C LiesOnRight (SEG_nd A B ) ∧ D LiesOnLeft (SEG_nd A B)) : (SEG_nd A C).toDir = -(SEG_nd B D).toDir := by
  have Proj : (SEG_nd A C ).toProj = (SEG_nd B D ).toProj := by
    exact para
  have eq_or_neg : ((SEG_nd A C ).toDir = (SEG_nd B D ).toDir) ∨ ((SEG_nd A C ).toDir = -(SEG_nd B D ).toDir) := by
    apply Dir.toProj_eq_toProj_iff.mp
    exact Proj
  rcases eq_or_neg with eq|neg
  · unfold IsOnLeftSide at side
    unfold IsOnRightSide at side
    have _ : (SEG A B).length > 0 := (SEG_nd A B).length_pos
    have c : odist C (SEG_nd A B) < 0 := side.1
    have d : odist D (SEG_nd A B) > 0 := side.2
    have w1 : wedge A B C < 0 := by
      calc
      _= (SEG A B).length * odist' C (RAY A B) := by exact wedge_eq_length_mul_odist' A B C
        _= (SEG A B).length * odist C (SEG_nd A B) := by rfl
        _= -((SEG A B).length * -odist C (SEG_nd A B)) := by simp only [Seg.length_eq_dist, mul_neg,neg_neg]
        _<0 := by
          have : (SEG A B).length * -odist C (SEG_nd A B) > 0 := by
            have : -odist C (SEG_nd A B) > 0 := by linarith
            positivity
          linarith
    have w2 : wedge A B D > 0 := by
      calc
        _= (SEG A B).length * odist' D (RAY A B) := by exact wedge_eq_length_mul_odist' A B D
        _= (SEG A B).length * odist D (SEG_nd A B) := by rfl
        _>0 := by positivity
    have det1 : Vec.det (VEC A B) (VEC A C) < 0 := by
      exact w1
    have det2 : Vec.det (VEC B A) (VEC B D) < 0 := by
      calc
        _= wedge B A D := by rfl
        _= -wedge A B D := by exact wedge213 A B D
        _<0 := by
          simp only [Left.neg_neg_iff]
          exact w2
    have dir : (VEC_nd A C ).toDir = (VEC_nd B D ).toDir := by exact eq
    have dir' : (VEC_nd A C ).SameDir (VEC_nd B D ) := by
      apply VecND.toDir_eq_toDir_iff.mp
      exact dir
    unfold VecND.SameDir at dir'
    rcases dir' with ⟨x,h⟩
    have x_pos : x > 0 := h.1
    have h : Vec.det (VEC A B) (VEC A C) = -x * Vec.det (VEC B A) (VEC B D) := by
      calc
        _= Vec.det (VEC A B) (x • (VEC B D)) := by
          congr
          exact h.2
        _= x * Vec.det (VEC A B) (VEC B D) := by
          simp only [LinearMap.map_smul]
          rfl
        _= x * Vec.det (-(VEC B A)) (VEC B D) := by
          congr
          simp
        _= x * -Vec.det (VEC B A) (VEC B D) := by
          have m: Vec.det (-(VEC B A)) (VEC B D) = -Vec.det (VEC B A) (VEC B D) := by
            simp only [LinearMap.map_neg]
            rfl
          simp only [m]
        _=_ := by simp only [mul_neg, neg_mul]
    absurd det1
    simp only [gt_iff_lt, not_lt]
    simp only [h]
    have : -x * Vec.det (VEC B A) (VEC B D) > 0 := by
      have : -Vec.det (VEC B A) (VEC B D) > 0 := by linarith
      calc
        _= x * (-Vec.det (VEC B A) (VEC B D)) := by simp
        _>0 := by positivity
    linarith
  · exact neg

theorem neg_toDir_of_parallel_and_IsOnOppositeSide {A B C D : P} [bnea : PtNe B A] [cnea : PtNe C A] [dneb : PtNe D B] (para : (SEG_nd A C) ∥ (SEG_nd B D)) (side : IsOnOppositeSide C D (SEG_nd A B)) : (SEG_nd A C).toDir = -(SEG_nd B D).toDir := by
  unfold IsOnOppositeSide at side
  unfold IsOnOppositeSide' at side
  have h : C LiesOnLeft (SEG_nd A B) ∧ D LiesOnRight (SEG_nd A B) ∨ C LiesOnRight (SEG_nd A B) ∧ D LiesOnLeft (SEG_nd A B) := by exact side
  rcases h with lr|rl
  · exact (neg_toDir_of_parallel_and_IsOnLR para lr)
  · exact (neg_toDir_of_parallel_and_IsOnRL para rl)

end EuclidGeom
