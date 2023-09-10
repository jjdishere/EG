import EuclideanGeometry.Foundation.Axiom.Position

noncomputable section
namespace EuclidGeom

class Line (P : Type _) [EuclideanPlane P] where 
  carrier : Set P
  linear : ∀ (A B C : P), (A ∈ carrier) → (B ∈ carrier) → (C ∈ carrier) → colinear A B C  
  maximal : ∀ (A B : P), (A ∈ carrier) → (B ∈ carrier) → (B ≠ A) → (∀ (C : P), colinear A B C → (C ∈ carrier))
  nontriv : ∃ (A B : P), (A ∈ carrier) ∧ (B ∈ carrier) ∧ (B ≠ A)

namespace Line

variable  {P : Type _} [EuclideanPlane P] 

-- define a line from two points 

theorem pt_eq_pt_of_eq_smul_smul {O A B : P} {v : Vec} {tA tB : ℝ} (h : tA = tB) (hA : VEC O A = tA • v) (hB : VEC O B = tB • v) : A = B := by
  have hAB : tB - tA = 0 := Iff.mpr sub_eq_zero (Eq.symm h)
  have hc : VEC A B = VEC O B - VEC O A := by
    unfold Vec.mk_pt_pt
    simp only [vsub_sub_vsub_cancel_right]
  rw [hA, hB, ← sub_smul, hAB, zero_smul] at hc
  symm
  exact (eq_iff_vec_eq_zero A B).2 hc

def mk_pt_pt (A B : P) (h : B ≠ A) : Line P where
  carrier := {C : P | ∃ t : ℝ, VEC A C = t • VEC A B}
  linear x y z:= by
    unfold Membership.mem Set.instMembershipSet Set.Mem setOf
    simp only [forall_exists_index]
    intro tx hx ty hy tz hz
    by_cases ty ≠ tx ∧ tz ≠ tx ∧ ty ≠ tz
    · rcases h with ⟨h₁, _, _⟩
      have w₂ : ∃ t : ℝ, VEC x z = t • VEC x y := by
        use (ty - tx)⁻¹ * (tz - tx)
        rw [mul_smul]
        symm
        apply ((inv_smul_eq_iff₀ (Iff.mpr sub_ne_zero h₁)).2)
        rw [← vec_sub_vec A x y, ← vec_sub_vec A x z, hx, hy, hz]
        rw [← sub_smul, ← sub_smul, ← mul_smul, ← mul_smul, mul_comm]
      apply colinear_of_vec_eq_smul_vec'
      exact w₂
    · unfold colinear
      have h' : (ty = tx) ∨ (tz = tx) ∨ (ty = tz) := by tauto
      by_cases ty = tx
      · rw [pt_eq_pt_of_eq_smul_smul h hy hx]
        tauto
      · by_cases tz = tx
        · rw [pt_eq_pt_of_eq_smul_smul h hz hx]
          tauto
        · have h : ty = tz := by tauto
          rw [pt_eq_pt_of_eq_smul_smul h hy hz]
          tauto
  maximal x y := by
    unfold Membership.mem Set.instMembershipSet Set.Mem setOf
    simp only [forall_exists_index]
    intro tx hx ty hy hne z c
    have e : VEC x y = (ty - tx) • VEC A B := by
      rw [← vec_sub_vec A x y, hx, hy, sub_smul]
    rcases (eq_mul_vec_iff_colinear_of_ne hne).1 c with ⟨t, ht⟩
    use tx + t * (ty - tx)
    rw [← vec_add_vec A x z, ht, e, hx, ← mul_smul, ← add_smul]
  nontriv := by
    use A
    use B
    unfold Membership.mem Set.instMembershipSet Set.Mem setOf
    simp only [forall_exists_index]
    constructor
    use 0
    simp only [vec_same_eq_zero, zero_smul]
    constructor
    use 1
    simp only [one_smul]
    exact h

end Line

scoped notation "LIN" => Line.mk_pt_pt 

variable {P : Type _} [EuclideanPlane P]

/- Def of point lies on a line -/
def IsOnLine (a : P) (l : Line P) : Prop :=
  a ∈ l.carrier

instance : HasLiesOn P (Line P) where
  lies_on := IsOnLine

theorem vec_eq_smul_vec_of_lies_on {l : Line P} {A B X Y : P} (ha : A LiesOn l) (hb : B LiesOn l) (hx : X LiesOn l) (hy : Y LiesOn l) (hab : B ≠ A) : ∃ t : ℝ, VEC X Y = t • VEC A B := by
  sorry


/- def coe from ray to line-/

def Ray.toLine (r : Ray P) := LIN r.source (r.toDir.toVec +ᵥ r.source) (by 
  by_contra h
  exact (Dir.dir_toVec_ne_zero r.toDir) (vec_eq_zero_of_vadd_eq_self h))

instance : Coe (Ray P) (Line P) where
  coe := Ray.toLine

/- def coe from non trivial segment to line-/

def Seg.toLine_of_nontriv (s : Seg P) (hs : s.is_nontriv) := (LIN s.source s.target hs)

section Compaitiblity_of_coersions
-- If a point lies on a ray, then it lies on the line associated to the ray.
theorem lies_on_line_of_ray_of_lies_on_ray {a : P} {l : Ray P} (h : a LiesOn l) : a LiesOn l := sorry

-- If A and B are two distinct points, they lie on the line AB
theorem source_or_ray_lies_on_line_of_ray (l : Ray P) : l.source LiesOn l := sorry

theorem pt_lies_on_line_of_pt_pt_of_ne {A B : P} (h: B ≠ A) : A LiesOn LIN A B h ∧ B LiesOn LIN A B h := sorry

-- The line defined from a nontrivial segment is equal to the line defined from the ray associated this nontriial segment

theorem line_of_nontriv_seg_eq_line_of_ray_of_nontriv_seg {seg : Seg P} (nontriv : seg.is_nontriv) : seg.toLine_of_nontriv nontriv = (seg.toRay_of_nontriv nontriv).toLine := sorry

theorem line_eq_line_of_seg_of_pt_pt_of_ne {A B : P} (h : B ≠ A) : LIN A B h = Seg.toLine_of_nontriv (SEG A B) h := sorry

theorem line_eq_line_of_pt_pt_of_ne {A B : P} {l : Line P} (h : B ≠ A) (hA : A LiesOn l) (hB : B LiesOn l) : l = Line.mk_pt_pt A B h := sorry

theorem lies_on_iff_colinear_of_ne {A B C : P}  (h : B ≠ A) : (C LiesOn LIN A B h) ↔ colinear A B C:= sorry

end Compaitiblity_of_coersions

section Archimedean_property
-- there are two distinct points on a line
theorem exists_ne_pt_pt_lies_on_of_line (l : Line P) : ∃ A B : P, B ≠ A ∧ A LiesOn l ∧ B LiesOn l  := sorry

-- Given distinct A B on a line, there exist C s.t. C LiesOn AB (a cor of Archimedean_property in Seg) and there exist D s.t. B LiesOn AD
end Archimedean_property

-- where should this theorem be placed?
theorem vec_eq_mul_vec_of_pt_pt_on_line (l : Line P) (A B C D : P) (hA : A LiesOn l) (hB : B LiesOn l) (hC : C LiesOn l) (hD : D LiesOn l) (h : B ≠ A) : ∃ (t : ℝ), VEC C D = t • VEC A B := sorry

-- def Line.toProj' (l : Line P) : Proj := by
--  choose A B h _ _ using (exists_ne_pt_pt_lies_on_of_line l)
--  exact (SEG A B).toProj_of_nontriv h

-- theorem eq_toProj_of_four_pt_on_line (l : Line P) (A B C D : P) (hA : A LiesOnLine l) (hB : B LiesOnLine l) (hC : C LiesOnLine l) (hD : D LiesOnLine l) (h₁ : B ≠ A) (h₂ : D ≠ C) : (SEG A B).toProj_of_nontriv h₁ = (SEG C D).toProj_of_nontriv h₂ := sorry

 theorem exist_unique_proj_of_line (l : Line P) : ∃! proj : Proj, ∀ (A B : P) (ha : A LiesOn l) (hb : B LiesOn l) (nontriv : B ≠ A), (SEG A B).toProj_of_nontriv nontriv = proj := by sorry

def Line.toProj (l : Line P) : Proj := by 
  choose proj _ using (exist_unique_proj_of_line l)
  use proj

end EuclidGeom