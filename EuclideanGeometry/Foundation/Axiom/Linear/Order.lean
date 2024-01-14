import EuclideanGeometry.Foundation.Axiom.Linear.Class

noncomputable section

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

-- Definition
def DirObj.le {α : Type*} [DirObj α] (l : α) (A B : P)  : Prop := (0 : ℝ) ≤ inner (VEC A B) (toDir l).unitVecND

def DirObj.lt {α : Type*} [DirObj α] (l : α) (A B : P) : Prop := (0 : ℝ) < inner (VEC A B) (toDir l).unitVecND

notation A : max "≤[" l : max "]" B : max => DirObj.le l A B
notation A : max "<[" l : max "]" B : max => DirObj.lt l A B
-- Proof of Preorder
def DirObj.instPreorder {α : Type*} [DirObj α] (l : α) : Preorder P where
  le := DirObj.le l
  lt := DirObj.lt l
  le_refl := by
    rintro a; simp only; unfold le
    simp only [vec_same_eq_zero, ne_eq, Dir.coe_unitVecND, inner_zero_left, le_refl]
  le_trans := by
    rintro a b c; simp only; unfold le; rintro h1 h2
    calc
    _≤ inner (VEC a b) ↑(toDir l).unitVecND + inner (VEC b c) ↑(toDir l).unitVecND := by positivity
    _= inner (VEC a c) ↑(toDir l).unitVecND := by
      symm;
      have : (VEC a c) = (VEC a b) + (VEC b c) := by simp only [vec_add_vec]
      simp only [this]
      apply InnerProductSpace.add_left
  lt_iff_le_not_le := by
    rintro a b; simp only; unfold le; unfold lt
    constructor
    · rintro h1
      constructor
      · positivity
      · simp only [ne_eq, Dir.coe_unitVecND, not_le]
        have : (VEC b a) = (-1 : ℝ) • (VEC a b) := by simp only [neg_smul, one_smul, neg_vec]
        simp only [this]
        have : inner ((-1 : ℝ) • VEC a b) (toDir l).unitVec = (-1 : ℝ) * (inner (VEC a b) (toDir l).unitVec) := by
          exact InnerProductSpace.smul_left (VEC a b) ((toDir l).unitVec) (-1 : ℝ)
        simp only [this]
        simp only [neg_mul, one_mul, Left.neg_neg_iff, gt_iff_lt]
        positivity
    · rintro ⟨_, h2⟩
      simp only [ne_eq, Dir.coe_unitVecND, not_le] at h2
      have : (VEC b a) = (-1 : ℝ) • (VEC a b) := by simp only [neg_smul, one_smul, neg_vec]
      simp only [this] at h2
      have : inner ((-1 : ℝ) • VEC a b) (toDir l).unitVec = (-1 : ℝ) * (inner (VEC a b) (toDir l).unitVec) := by
        exact InnerProductSpace.smul_left (VEC a b) ((toDir l).unitVec) (-1 : ℝ)
      simp only [this] at h2
      simp only [neg_mul, one_mul, Left.neg_neg_iff, gt_iff_lt] at h2
      exact h2

@[aesop unsafe]
theorem lt_of_le_not_le {α : Type*} [DirObj α] (l : α) {a : P} {b : P} :
a ≤[l] b → ¬b ≤[l] a → a <[l] b :=
  @_root_.lt_of_le_not_le P (DirObj.instPreorder l) a b


end EuclidGeom
