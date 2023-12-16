import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Class

/-!
In this file, we define the concept for two lines to be parallel. A more precise plan is the following:

We define a class called linear objects, consisting of one of the five types: nondegenerate vector, direction, ray, nondegenerate segment, and line.

We define the meaning of any pair of linear objects to be parallel.

We prove that coercion among linear objects generates linear objects that are parallel to the original ones.

We prove theorems related to that non-parallel lines intersection, and define the intersections.

## Future Work
`Comments about LinearObj is outdated. Now we use ProjObj`
-/
noncomputable section
namespace EuclidGeom

open Line

variable {P : Type _} [EuclideanPlane P]
/-
/-- A linear object is one of the following five types: a nondegenerate vector, a direction, a ray, a nondegenerate segment, or a line.
In the following, we define natural ways to view a nondegenerate vector, a direction, a ray, a nondegenerate segment or a line, as a linear object.
Given a linear object, we return its associated projective direction, which is the associated projective direction in each of the five instances of a linear object. -/
instance : LinearObj VecND where
  toProj := fun l ↦ l.toProj

instance : LinearObj Dir where
  toProj := fun l ↦ l.toProj

instance : LinearObj (Ray P) where
  toProj := fun l ↦ l.toProj

instance : LinearObj (SegND P) where
  toProj := fun l ↦ l.toProj

instance : LinearObj (DirLine P) where
  toProj := fun l ↦ l.toProj

instance : LinearObj (Line P) where
  toProj := fun l ↦ l.toProj
-/

-- Our definition of parallel for LinearObj is very general. Not only can it apply to different types of Objs, but also include degenerate cases, such as ⊆(inclusions), =(equal).
/-- Given two linear objects $l_1$ and $l_2$ (not necessarily of the same type), this function returns whether they are parallel, defined as having the same associated projective direction. -/
def parallel {α β : Type*} [ProjObj α] [ProjObj β] (l₁ : α) (l₂ : β) : Prop :=
  toProj l₁ = toProj l₂

/-- Being parallel defines an equivalence relation among all linear objects, that is they satisfy the three conditions: (1) reflexive: every linear object $l$ is parallel to itself; (2) symmetric: if the linear object $l_1$ is parallel to the linear object $l_2$, then $l_2$ is $l_1$; (3) transitive: if the linear object $l_1$ is parallel to the linear object $l_2$, and if the linear object $l_2$ is parallel to the linear object $l_3$, then $l_1$ is parallel to $l_3$. -/
instance (α : Type*) [ProjObj α] : IsEquiv α parallel where
  refl _ := rfl
  symm _ _ := Eq.symm
  trans _ _ _ := Eq.trans

/-- This is to rewrite \verb|parallel l l'| as \verb|l ParallelTo l'| -/
scoped infix : 50 " ParallelTo " => parallel

/-- This is to rewrite \verb|parallel l l'| as $l \parallel l'$. -/
scoped infix : 50 " ∥ " => parallel

/- lots of trivial parallel relation of vec of 2 pt lies on Line, coercions, ... -/

section coercion_theorem

-- `Should this section eq_toProj really exist?? outside this file only parallel is allowed, not eq_toProj, or maybe this section should be marked as private`
section eq_toProj

---- eq_toProj theorems should be relocate to this file, they are in Line_ex now.
/-- The projective direction of a ray is same as the projective direction of the extension line of the ray. -/
theorem Ray.toProj_eq_toLine_toProj (ray : Ray P): ray.toProj = ray.toLine.toProj := rfl

/-- The projective direction of a nondegenerate segment is same as the projective direction of the extension line of it. -/
theorem SegND.toProj_eq_toLine_toProj (seg_nd : SegND P) : seg_nd.toProj = seg_nd.toLine.toProj := rfl

end eq_toProj

section fig_coecion_parallel

/-- Given a nondegenate segment, it is parallel to the ray associated to this nondegenerate segment. -/
theorem SegND.para_toray (seg_nd : SegND P) : seg_nd ∥ seg_nd.toRay := rfl

theorem SegND.para_toDirLine (seg_nd : SegND P) : seg_nd ∥ seg_nd.toDirLine := rfl

/-- Given a nondegenate segment, it is parallel to the extension line of this nondegenerate segment. -/
theorem SegND.para_toLine (seg_nd : SegND P) : seg_nd ∥ seg_nd.toLine := rfl

theorem Ray.para_toDirLine (ray : Ray P) : ray ∥ ray.toDirLine := rfl

/-- Given a ray, the ray is parallel to the line associated to the ray. -/
theorem Ray.para_toLine (ray : Ray P) : ray ∥ ray.toLine := rfl

theorem DirLine.para_toLine (dlin : DirLine P) : dlin ∥ dlin.toLine := (DirLine.toLine_toProj_eq_toProj dlin).symm

end fig_coecion_parallel

section mk_parallel
-- parallel from mk methods

end mk_parallel

-- 6 theorems for each coercion, 6 coercion
section parallel_iff_coercion_parallel

theorem SegND.para_toray_of_para (seg_nd seg_nd' : SegND P) : seg_nd ∥ seg_nd' → seg_nd.toRay ∥ seg_nd'.toRay := id

theorem SegND.para_of_para_toray (seg_nd seg_nd' : SegND P) : seg_nd.toRay ∥ seg_nd'.toRay → seg_nd ∥ seg_nd' := id

theorem SegND.para_iff_para_toray (seg_nd seg_nd' : SegND P) : seg_nd.toRay ∥ seg_nd'.toRay ↔ seg_nd ∥ seg_nd' := ⟨id, id⟩

theorem SegND.not_para_toray_of_not_para (seg_nd seg_nd' : SegND P) : ¬ seg_nd ∥ seg_nd' → ¬ seg_nd.toRay ∥ seg_nd'.toRay := id

theorem SegND.not_para_of_not_para_toray (seg_nd seg_nd' : SegND P) : ¬ seg_nd.toRay ∥ seg_nd'.toRay → ¬ seg_nd ∥ seg_nd' := id

theorem SegND.not_para_iff_not_para_toray (seg_nd seg_nd' : SegND P) : ¬ seg_nd ∥ seg_nd' ↔ ¬ seg_nd.toRay ∥ seg_nd'.toRay  := ⟨id, id⟩

theorem SegND.para_toDirLine_of_para (seg_nd seg_nd' : SegND P) : seg_nd ∥ seg_nd' → seg_nd.toDirLine ∥ seg_nd'.toDirLine := id

theorem SegND.para_of_para_toDirLine (seg_nd seg_nd' : SegND P) : seg_nd.toDirLine ∥ seg_nd'.toDirLine → seg_nd ∥ seg_nd' := id

theorem SegND.para_iff_para_toDirLine (seg_nd seg_nd' : SegND P) : seg_nd.toDirLine ∥ seg_nd'.toDirLine ↔ seg_nd ∥ seg_nd' := ⟨id, id⟩

theorem SegND.not_para_toDirLine_of_not_para (seg_nd seg_nd' : SegND P) : ¬ seg_nd ∥ seg_nd' → ¬ seg_nd.toDirLine ∥ seg_nd'.toDirLine := id

theorem SegND.not_para_of_not_para_toDirLine (seg_nd seg_nd' : SegND P) : ¬ seg_nd.toDirLine ∥ seg_nd'.toDirLine → ¬ seg_nd ∥ seg_nd' := id

theorem SegND.not_para_iff_not_para_toDirLine (seg_nd seg_nd' : SegND P) : ¬ seg_nd ∥ seg_nd' ↔ ¬ seg_nd.toDirLine ∥ seg_nd'.toDirLine := ⟨id, id⟩

theorem SegND.para_toLine_of_para (seg_nd seg_nd' : SegND P) : seg_nd ∥ seg_nd' → seg_nd.toLine ∥ seg_nd'.toLine := id

theorem SegND.para_of_para_toLine (seg_nd seg_nd' : SegND P) : seg_nd.toLine ∥ seg_nd'.toLine → seg_nd ∥ seg_nd' := id

theorem SegND.para_iff_para_toLine (seg_nd seg_nd' : SegND P) : seg_nd.toLine ∥ seg_nd'.toLine ↔ seg_nd ∥ seg_nd' := ⟨id, id⟩

theorem SegND.not_para_toLine_of_not_para (seg_nd seg_nd' : SegND P) : ¬ seg_nd ∥ seg_nd' → ¬ seg_nd.toLine ∥ seg_nd'.toLine := id

theorem SegND.not_para_of_not_para_toLine (seg_nd seg_nd' : SegND P) : ¬ seg_nd.toLine ∥ seg_nd'.toLine → ¬ seg_nd ∥ seg_nd' := id

theorem SegND.not_para_iff_not_para_toLine (seg_nd seg_nd' : SegND P) : ¬ seg_nd ∥ seg_nd' ↔ ¬ seg_nd.toLine ∥ seg_nd'.toLine  := ⟨id, id⟩

theorem Ray.para_of_para_toDirLine (ray ray' : Ray P) : ray.toDirLine ∥ ray'.toDirLine → ray ∥ ray' := id

theorem Ray.para_iff_para_toDirLine (ray ray' : Ray P) : ray.toDirLine ∥ ray'.toDirLine ↔ ray ∥ ray' := ⟨id, id⟩

theorem Ray.not_para_toDirLine_of_not_para (ray ray' : Ray P) : ¬ ray ∥ ray' → ¬ ray.toDirLine ∥ ray'.toDirLine := id

theorem Ray.not_para_of_not_para_toDirLine (ray ray' : Ray P) : ¬ ray.toDirLine ∥ ray'.toDirLine → ¬ ray ∥ ray' := id

theorem Ray.not_para_iff_not_para_toDirLine (ray ray' : Ray P) : ¬ ray ∥ ray' ↔ ¬ ray.toDirLine ∥ ray'.toDirLine := ⟨id, id⟩

/-- Given two parallel rays, their extension lines are parallel -/
theorem Ray.para_toLine_of_para (ray ray' : Ray P) : ray ∥ ray' → ray.toLine ∥ ray'.toLine := id

theorem Ray.para_of_para_toLine (ray ray' : Ray P) : ray.toLine ∥ ray'.toLine → ray ∥ ray' := id

theorem Ray.para_iff_para_toLine (ray ray' : Ray P) : ray.toLine ∥ ray'.toLine ↔ ray ∥ ray' := ⟨id, id⟩

/-- Given two rays, if their extension lines are not parallel, they are not parallel -/
theorem Ray.not_para_toLine_of_not_para (ray ray' : Ray P) : ¬ ray ∥ ray' → ¬ ray.toLine ∥ ray'.toLine := id

theorem Ray.not_para_of_not_para_toLine (ray ray' : Ray P) : ¬ ray.toLine ∥ ray'.toLine → ¬ ray ∥ ray' := id

theorem Ray.not_para_iff_not_para_toLine (ray ray' : Ray P) : ¬ ray ∥ ray' ↔ ¬ ray.toLine ∥ ray'.toLine  := ⟨id, id⟩

theorem DirLine.para_toLine_of_para (dirline dirline' : DirLine P) : dirline ∥ dirline' → dirline.toLine ∥ dirline'.toLine := Quotient.ind₂ (fun _ _ => id) dirline dirline'

theorem DirLine.para_of_para_toLine (dirline dirline' : DirLine P) : dirline.toLine ∥ dirline'.toLine → dirline ∥ dirline' := Quotient.ind₂ (fun _ _ => id) dirline dirline'

theorem DirLine.para_iff_para_toLine (dirline dirline' : DirLine P) : dirline.toLine ∥ dirline'.toLine ↔ dirline ∥ dirline' := ⟨Quotient.ind₂ (fun _ _ => id) dirline dirline', Quotient.ind₂ (fun _ _ => id) dirline dirline'⟩

theorem DirLine.not_para_toLine_of_not_para (dirline dirline' : DirLine P) : ¬ dirline ∥ dirline' → ¬ dirline.toLine ∥ dirline'.toLine := Quotient.ind₂ (fun _ _ => id) dirline dirline'

theorem DirLine.not_para_of_not_para_toLine (dirline dirline' : DirLine P) : ¬ dirline.toLine ∥ dirline'.toLine → ¬ dirline ∥ dirline' := Quotient.ind₂ (fun _ _ => id) dirline dirline'

theorem DirLine.not_para_iff_not_para_toLine (dirline dirline' : DirLine P) : ¬ dirline ∥ dirline' ↔ ¬ dirline.toLine ∥ dirline'.toLine  := ⟨Quotient.ind₂ (fun _ _ => id) dirline dirline', Quotient.ind₂ (fun _ _ => id) dirline dirline'⟩

end parallel_iff_coercion_parallel

section reverse

variable {α β : Type*} [DirFig α P] [DirFig β P] {l₁ : α} {l₂ : β}

theorem DirFig.para_rev_of_para (h : l₁ ∥ l₂) : l₁ ∥ reverse l₂ :=
  h.trans (rev_toProj_eq_toProj l₂).symm

theorem SegND.para_rev_of_para {s s' : SegND P} (h : s ∥ s') : s ∥ s'.reverse :=
  DirFig.para_rev_of_para h

theorem Ray.para_rev_of_para {r r' : Ray P} (h : r ∥ r') : r ∥ r'.reverse :=
  DirFig.para_rev_of_para h

theorem DirLine.para_rev_of_para {l l' : DirLine P} (h : l ∥ l') : l ∥ l'.reverse :=
  DirFig.para_rev_of_para h

theorem DirFig.not_para_rev_of_not_para (h : ¬ l₁ ∥ l₂) : ¬ l₁ ∥ reverse l₂ :=
  fun hn ↦ h ((para_rev_of_para hn).trans (congrArg ProjObj.toProj (rev_rev)))

theorem SegND.not_para_rev_of_not_para {s s' : SegND P} (h : ¬ s ∥ s') : ¬ s ∥ s'.reverse :=
  DirFig.not_para_rev_of_not_para h

theorem Ray.not_para_rev_of_not_para {r r' : Ray P} (h : ¬ r ∥ r') : ¬ r ∥ r'.reverse :=
  DirFig.not_para_rev_of_not_para h

theorem DirLine.not_para_rev_of_not_para {l l' : DirLine P} (h : ¬ l ∥ l') : ¬ l ∥ l'.reverse :=
  DirFig.not_para_rev_of_not_para h

theorem DirFig.rev_para_of_para (h : l₁ ∥ l₂) : reverse l₁ ∥ l₂ :=
  (rev_toProj_eq_toProj l₁).trans h

theorem SegND.rev_para_of_para {s s' : SegND P} (h : s ∥ s') : s.reverse ∥ s' :=
  DirFig.rev_para_of_para h

theorem Ray.rev_para_of_para {r r' : Ray P} (h : r ∥ r') : r.reverse ∥ r' :=
  DirFig.rev_para_of_para h

theorem DirLine.rev_para_of_para {l l' : DirLine P} (h : l ∥ l') : l.reverse ∥ l' :=
  DirFig.rev_para_of_para h

theorem DirFig.not_rev_para_of_not_para (h : ¬ l₁ ∥ l₂) : ¬ reverse l₁ ∥ l₂ :=
  fun hn ↦ h ((congrArg ProjObj.toProj rev_rev).symm.trans (rev_para_of_para hn) )

theorem SegND.not_rev_para_of_not_para {s s' : SegND P} (h : ¬ s ∥ s') : ¬ s.reverse ∥ s' :=
  DirFig.not_rev_para_of_not_para h

theorem Ray.not_rev_para_of_not_para {r r' : Ray P} (h : ¬ r ∥ r') : ¬ r.reverse ∥ r' :=
  DirFig.not_rev_para_of_not_para h

theorem DirLine.not_rev_para_of_not_para {l l' : DirLine P} (h : ¬ l ∥ l') : ¬ l.reverse ∥ l' :=
  DirFig.not_rev_para_of_not_para h

theorem DirFig.rev_para_rev_of_para (h : l₁ ∥ l₂) : reverse l₁ ∥ reverse l₂ :=
  rev_para_of_para (para_rev_of_para h)

theorem SegND.rev_para_rev_of_para {s s' : SegND P} (h : s ∥ s') : s.reverse ∥ s'.reverse :=
  DirFig.rev_para_rev_of_para h

theorem Ray.rev_para_rev_of_para {r r' : Ray P} (h : r ∥ r') : r.reverse ∥ r'.reverse :=
  DirFig.rev_para_rev_of_para h

theorem DirLine.rev_para_rev_of_para {l l' : DirLine P} (h : l ∥ l') : l.reverse ∥ l'.reverse :=
  DirFig.rev_para_rev_of_para h

theorem DirFig.not_rev_para_rev_of_not_para (h : ¬ l₁ ∥ l₂) : ¬ reverse l₁ ∥ reverse l₂ :=
  not_rev_para_of_not_para (not_para_rev_of_not_para h)

theorem SegND.not_rev_para_rev_of_not_para {s s' : SegND P} (h : ¬ s ∥ s') : ¬ s.reverse ∥ s'.reverse :=
  DirFig.not_rev_para_rev_of_not_para h

theorem Ray.not_rev_para_rev_of_not_para {r r' : Ray P} (h : ¬ r ∥ r') : ¬ r.reverse ∥ r'.reverse :=
  DirFig.not_rev_para_rev_of_not_para h

theorem DirLine.not_rev_para_rev_of_not_para {l l' : DirLine P} (h : ¬ l ∥ l') : ¬ l.reverse ∥ l'.reverse :=
  DirFig.not_rev_para_rev_of_not_para h

end reverse

end coercion_theorem

section intersection_of_line

section construction

def cu (u v w: Vec) : ℝ := (Vec.det u v)⁻¹ * (Vec.det w v)

def cv (u v w: Vec) : ℝ := (Vec.det u v)⁻¹ * (Vec.det u w)

theorem cu_cv (u v w : Vec) : cu u v w = cv v u w := by
  rw [cu, cv, ← Vec.det_skew v u, inv_neg, Vec.det_apply w v, Vec.det_apply v w]
  field_simp
  ring

theorem cu_neg (u v w : Vec) : cu u v (- w) = - cu u v w := by
  rw [cu, cu, neg_mul_eq_mul_neg, map_neg]
  rfl

theorem Vec.linear_combination_of_not_colinear' {u v w : Vec} (hu : v ≠ 0) (h' : ¬(∃ (t : ℝ), u = t • v)) : w = cu u v w • u + cv u v w • v := by
  have : u.fst * v.snd - u.snd * v.fst ≠ 0 := (det_eq_zero_iff_eq_smul_right.not.mpr (not_or.mpr ⟨hu, h'⟩))
  dsimp [cu, cv, det_apply]
  apply Vec.ext <;>
  · field_simp
    ring

theorem Vec.linear_combination_of_not_colinear_vecND {u v : VecND} (w : Vec) (h' : VecND.toProj u ≠ VecND.toProj v) : w = (cu u.1 v.1 w) • u.1 + (cv u.1 v.1 w) • v.1 := by
  have h₁ : ¬(∃ (t : ℝ), u.1 = t • v.1)
  · by_contra h₂
    let _ := VecND.toProj_eq_toProj_iff.2 h₂
    tauto
  exact @linear_combination_of_not_colinear' u.1 v.1 w v.2 h₁

theorem Vec.linear_combination_of_not_colinear_dir {u v : Dir} (w : Vec) (h' : u.toProj ≠ v.toProj) : w = (cu u.unitVec v.unitVec w) • u.unitVec + (cv u.unitVec v.unitVec w) • v.unitVec := by
  have h₁ : (u.toProj ≠ v.toProj) → ¬(∃ (t : ℝ), u.unitVec = t • v.unitVec)
  · by_contra h
    push_neg at h
    let u' := u.unitVecND
    let v' := v.unitVecND
    have hu1 : u = u'.toDir := u.unitVecND_toDir.symm
    have hu2 : VecND.toProj u' = u.toProj := by
      unfold VecND.toProj
      rw [hu1]
    have hu3 : u.unitVec = u'.1 := rfl
    have hv1 : v = v'.toDir := v.unitVecND_toDir.symm
    have hv2 : VecND.toProj v' = v.toProj := by
      unfold VecND.toProj
      rw [hv1]
    have hv3 : v.unitVec = v'.1 := rfl
    rw [hu3, hv3, ←hu2, ←hv2, ← VecND.toProj_eq_toProj_iff] at h
    tauto
  exact @linear_combination_of_not_colinear' u.unitVec v.unitVec w (VecND.ne_zero _) (h₁ h')

/-- Given two unparallel rays, this function gives the intersection of their extension lines. -/
def inx_of_extn_line (r₁ r₂ : Ray P) (h : ¬ r₁ ∥ r₂) : P := (cu r₁.toDir.unitVecND r₂.toDir.unitVecND (VEC r₁.source r₂.source) • r₁.toDir.unitVec +ᵥ r₁.source)

/-- Given two unparallel rays, we define the intersection of their extension lines. -/
theorem inx_of_extn_line_symm (r₁ r₂ : Ray P) (h : ¬ r₁ ∥ r₂) :
    inx_of_extn_line r₁ r₂ h = inx_of_extn_line r₂ r₁ (Ne.symm h) := by
  have hsymm : cu r₁.toDir.unitVecND r₂.toDir.unitVecND (VEC r₁.source r₂.source) • r₁.toDir.unitVec =
      cu r₂.toDir.unitVecND r₁.toDir.unitVecND (VEC r₂.source r₁.source) • r₂.toDir.unitVec +
      (r₂.source -ᵥ r₁.source)
  · have h := Vec.linear_combination_of_not_colinear_dir (VEC r₁.source r₂.source) (Ne.symm h)
    nth_rw 1 [← cu_cv, Vec.mkPtPt] at h
    rw [h, ← neg_vec r₁.source r₂.source, cu_neg, neg_smul]
    exact eq_neg_add_of_add_eq rfl
  rw [inx_of_extn_line, inx_of_extn_line, hsymm, add_vadd, vsub_vadd]

/-- Given two unparallel rays $r_1$ and $r_2$, the point given by function "inx_of_extn_line" lies on the extension line of $r_1$ -/
theorem inx_lies_on_fst_extn_line (r₁ r₂ : Ray P) (h : ¬ r₁ ∥ r₂) : ((inx_of_extn_line r₁ r₂ h) ∈ r₁.carrier ∪ r₁.reverse.carrier) := by
  rw [inx_of_extn_line]
  by_cases hn : cu r₁.toDir.unitVecND r₂.toDir.unitVecND (VEC r₁.source r₂.source) ≥ 0
  · left
    use cu r₁.toDir.unitVecND r₂.toDir.unitVecND (VEC r₁.source r₂.source)
    exact ⟨hn, vec_of_pt_vadd_pt_eq_vec _ _⟩
  · right
    use - cu r₁.toDir.unitVecND r₂.toDir.unitVecND (VEC r₁.source r₂.source)
    constructor
    linarith
    dsimp [Ray.reverse]
    rw [vec_of_pt_vadd_pt_eq_vec, Dir.neg_unitVec, smul_neg, neg_smul, neg_neg]

/-- Given two unparallel rays $r_1$ and $r_2$, the point given by function "inx_of_extn_line" lies on the extension line of $r_2$ -/
theorem inx_lies_on_snd_extn_line (r₁ r₂ : Ray P) (h : ¬ r₁ ∥ r₂) : ((inx_of_extn_line r₁ r₂ h) ∈ r₂.carrier ∪ r₂.reverse.carrier) := by
  rw [inx_of_extn_line_symm]
  exact inx_lies_on_fst_extn_line r₂ r₁ (Ne.symm h)

/-- Given two rays $r_1$ $r_2$, if they have same projective directions and the source of $r_1$ lies on the extension line of $r_2$, then the two rays have same extension lines. -/
theorem ray_toLine_eq_of_same_extn_line {r₁ r₂ : Ray P} (h : same_extn_line r₁ r₂) : r₁.toLine = r₂.toLine := (Quotient.eq (r := same_extn_line.setoid)).mpr h

-- `key theorem`
/-- Given four rays $a_1$ $a_2$ $b_1$ $b_2$, if $a_1$ $a_2$ have the same extension line, $b_1$ $b_2$ have the same extension line , $a_1$ $b_1$ have different projective directions and $a_2$ $b_2$ have different projective directions, then the intersection of extension lines of $a_1$ $b_1$ is same as that of $a_2$ $b_2$ -/
theorem inx_eq_of_same_extn_line {a₁ b₁ a₂ b₂ : Ray P} (g₁ : same_extn_line a₁ a₂) (g₂ : same_extn_line b₁ b₂) (h₁ : ¬ a₁ ∥ b₁ ) (h₂ : ¬ a₂ ∥ b₂) : inx_of_extn_line a₁ b₁ h₁ = inx_of_extn_line a₂ b₂ h₂ := by
  have ha1 : inx_of_extn_line a₁ b₁ h₁ LiesOn a₁.toLine := inx_lies_on_fst_extn_line a₁ b₁ h₁
  have hb1 : inx_of_extn_line a₁ b₁ h₁ LiesOn b₁.toLine := inx_lies_on_snd_extn_line a₁ b₁ h₁
  rw [ray_toLine_eq_of_same_extn_line g₁] at ha1
  rw [ray_toLine_eq_of_same_extn_line g₂] at hb1
  by_contra hn
  have heq : a₂.toLine = b₂.toLine := eq_of_pt_pt_lies_on_of_ne hn
    (inx_lies_on_fst_extn_line a₂ b₂ h₂) ha1 (inx_lies_on_snd_extn_line a₂ b₂ h₂) hb1
  exact h₂ (congrArg Line.toProj heq)

-- This theorem deals only with `HEq`
theorem heq_funext {c₁ c₂ d: Sort _} (e : c₁ = c₂) {f₁ : c₁ → d} {f₂ : c₂ → d} (h : ∀ (s : c₁) (t : c₂), f₁ s = f₂ t) : HEq f₁ f₂ := Function.hfunext e (fun _ _ _ => (heq_of_eq (h _ _)))

theorem heq_of_inx_of_extn_line (a₁ b₁ a₂ b₂ : Ray P) (h₁ : same_extn_line a₁ a₂) (h₂ : same_extn_line b₁ b₂) : HEq (fun h => inx_of_extn_line a₁ b₁ h) (fun h => inx_of_extn_line a₂ b₂ h) := by
  have e : (Ray.toProj a₁ ≠ Ray.toProj b₁) = (Ray.toProj a₂ ≠ Ray.toProj b₂) := by
    rw [h₁.1, h₂.1]
  exact @heq_funext (Ray.toProj a₁ ≠ Ray.toProj b₁) (Ray.toProj a₂ ≠ Ray.toProj b₂) P e (fun h => inx_of_extn_line a₁ b₁ h) (fun h => inx_of_extn_line a₂ b₂ h) (inx_eq_of_same_extn_line h₁ h₂)

/-- Given two lines with different projective directions, this function gives the intersection point of these two lines. -/
def Line.inx (l₁ l₂ : Line P) (h : ¬ l₁ ∥ l₂) : P := @Quotient.hrecOn₂ (Ray P) (Ray P) same_extn_line.setoid same_extn_line.setoid (fun l l' => (Line.toProj l ≠ Line.toProj l') → P) l₁ l₂ inx_of_extn_line heq_of_inx_of_extn_line h

/-- Given two unparallel line $l_1$ $l_2$, the point given by function "Line.inx" lies on $l_1$ -/
theorem Line.inx_lies_on_fst {l₁ l₂ : Line P} (h : ¬ l₁ ∥ l₂) :
    Line.inx l₁ l₂ h LiesOn l₁ := by
  rcases Quotient.exists_rep l₁ with ⟨r1, hr1⟩
  rcases Quotient.exists_rep l₂ with ⟨r2, hr2⟩
  simp only [← hr1, ← hr2]
  exact inx_lies_on_fst_extn_line r1 r2 (by rw [← hr1, ← hr2] at h; exact h)

/-- Given two unparallel line $l_1$ $l_2$, the point given by function "Line.inx" lies on $l_1$ -/
theorem Line.inx_lies_on_snd {l₁ l₂ : Line P} (h : ¬ l₁ ∥ l₂) :
    Line.inx l₁ l₂ h LiesOn l₂ := by
  rcases Quotient.exists_rep l₁ with ⟨r1, hr1⟩
  rcases Quotient.exists_rep l₂ with ⟨r2, hr2⟩
  simp only [← hr1, ← hr2]
  exact inx_lies_on_snd_extn_line r1 r2 (by rw [← hr1, ← hr2] at h; exact h)

/-- Given two unparallel line $l_1$ $l_2$, the point given by function "Line.inx" is exactly the intersection of these two lines -/
theorem Line.inx_is_inx {l₁ l₂ : Line P} (h : ¬ l₁ ∥ l₂) : is_inx (Line.inx l₁ l₂ h) l₁ l₂ :=
  ⟨inx_lies_on_fst h, inx_lies_on_snd h⟩

end construction

section property

-- In this section, we discuss the property of intersection point using `is_inx` instead of `Line.inx`. As a corollory, we deduce the symmetry of Line.inx.

/-- Two unparallel lines have only one intersection point -/
theorem unique_of_inx_of_line_of_not_para {A B : P} {l₁ l₂ : Line P} (h : ¬ l₁ ∥ l₂) (a : is_inx A l₁ l₂) (b : is_inx B l₁ l₂) : B = A :=
  Classical.byContradiction fun d ↦ h (congrArg Line.toProj (eq_of_pt_pt_lies_on_of_ne d a.1 b.1 a.2 b.2))

/-- Given two unparallel line $l_1$ $l_2$, the point given by function "Line.inx" is exactly the intersection of these two lines -/
theorem inx_of_line_eq_inx {A : P} {l₁ l₂ : Line P} (h : ¬ l₁ ∥ l₂) (ha : is_inx A l₁ l₂) :
  A = l₁.inx l₂ h := unique_of_inx_of_line_of_not_para h (Line.inx_is_inx h) ha

/-- The symmetry of Line.inx -/
theorem Line.inx.symm {l₁ l₂ : Line P} (h : ¬ l₁ ∥ l₂) : Line.inx l₂ l₁ (Ne.symm h) = Line.inx l₁ l₂ h :=
  unique_of_inx_of_line_of_not_para h (Line.inx_is_inx h) (is_inx.symm (Line.inx_is_inx (Ne.symm h)))

/-- If two parallel lines share a same point, they are exactly the same line -/
theorem eq_of_parallel_and_pt_lies_on {A : P} {l₁ l₂ : Line P} (h₁ : A LiesOn l₁) (h₂ : A LiesOn l₂)
  (h : l₁ ∥ l₂) : l₁ = l₂ := eq_of_same_toProj_and_pt_lies_on h₁ h₂ h

/-- If two lines are not parallel, then their intersection is not empty -/
theorem exists_intersection_of_nonparallel_lines {l₁ l₂ : Line P} (h : ¬ l₁ ∥ l₂) : ∃ p : P, p LiesOn l₁ ∧ p LiesOn l₂ := by
  rcases l₁.nontriv with ⟨A, ⟨B, hab⟩⟩
  rcases l₂.nontriv with ⟨C, ⟨D, hcd⟩⟩
  have e' : (SEG_nd A B hab.2.2).toProj ≠ (SEG_nd C D hcd.2.2).toProj := by
    rw [toProj_eq_seg_nd_toProj_of_lies_on hab.1 hab.2.1 hab.2.2, toProj_eq_seg_nd_toProj_of_lies_on hcd.1 hcd.2.1 hcd.2.2]
    exact h
  let x := cu (VEC A B) (VEC C D) (VEC A C)
  let y := cv (VEC A B) (VEC C D) (VEC A C)
  have e : VEC A C = x • VEC A B + y • VEC C D := by
    apply Vec.linear_combination_of_not_colinear_vecND (VEC A C) e'
  have h : VEC C (x • VEC A B +ᵥ A) = - y • VEC C D := by
    rw [← vec_sub_vec A _ _, vec_of_pt_vadd_pt_eq_vec _ _, e]
    simp only [Complex.real_smul, sub_add_cancel', neg_smul]
  exact ⟨x • VEC A B +ᵥ A, (lies_on_iff_colinear_of_ne_lies_on_lies_on hab.2.2 hab.1 hab.2.1 _).2
    (colinear_of_vec_eq_smul_vec (vec_of_pt_vadd_pt_eq_vec A _)),
    (lies_on_iff_colinear_of_ne_lies_on_lies_on hcd.2.2 hcd.1 hcd.2.1 _).2 (colinear_of_vec_eq_smul_vec h)⟩

/-- If two lines are not parallel, then there exists a unique point in their intersection -/
theorem exists_unique_intersection_of_nonparallel_lines {l₁ l₂ : Line P} (h : ¬ l₁ ∥ l₂) : ∃! p : P, p LiesOn l₁ ∧ p LiesOn l₂ := by
  rcases exists_intersection_of_nonparallel_lines h with ⟨X, ⟨h₁, h₂⟩⟩
  use X
  simp only [h₁, h₂, and_self, and_imp, true_and]
  exact fun _ h₁' h₂' ↦ Classical.byContradiction fun n ↦
    h (congrArg toProj (eq_of_pt_pt_lies_on_of_ne n h₁ h₁' h₂ h₂'))

scoped notation "LineInx" => Line.inx

/-
-- `why do we creat a version using choose???`
/-- Given two unparallel lines, this function gives the unique intersection point of these two lines -/
def intersection_of_nonparallel_line (l₁ l₂ : Line P) (h : ¬ l₁ ∥ l₂) : P :=
  Classical.choose (exists_unique_intersection_of_nonparallel_lines h)

scoped notation "LineInt" => intersection_of_nonparallel_line

/-- Given two unparallel line $l_1$ $l_2$, the point given by function "Line.inx" lies on $l_1$ -/
theorem intersection_of_nonparallel_line_lies_on_fst_line {l₁ l₂ : Line P} (h : ¬ l₁ ∥ l₂) : LineInt l₁ l₂ h LiesOn l₁ :=
  (Classical.choose_spec (exists_unique_intersection_of_nonparallel_lines h)).1.1

/-- Given two unparallel line $l_1$ $l_2$, the point given by function "Line.inx" lies on $l_2$ -/
theorem intersection_of_nonparallel_line_lies_on_snd_line {l₁ l₂ : Line P} (h : ¬ l₁ ∥ l₂) : LineInt l₁ l₂ h LiesOn l₂ :=
  (Classical.choose_spec (exists_unique_intersection_of_nonparallel_lines h)).1.2
-/

/-!
-- Now let's come to rays.
-- If ray₁ and ray₂ are two rays that are not parallel, then the following function returns the unique point of the intersection of the associated two lines. This function is a bit tricky, will come back to this.
-- `Should we define this concept? Why don't we just use Intersection of Lines and use coercion (ray : Line)`
def Intersection_of_Lines_of_Rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : P := sorry

scoped notation "RayInx" => Intersection_of_Lines_of_Rays

theorem ray_intersection_lies_on_lines_of_rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : (RayInx h) LiesOn ray₁.toLine ∧ (RayInx h) LiesOn ray₂.toLine := by sorry

-- theorem ray_intersection_eq_line_intersection_of_rays {ray₁ ray₂ : Ray P} (h : ¬ (LinearObj.ray ray₁) ∥ ray₂) : RayInt h = LineInt (Ne.trans (ray_parallel_toLine_assoc_ray ray₁) h) := sorry
-/

-- `the new solution is to define a class ProjFig, which has a unified method toLine, then define inx_of_toLine all together`
end property

end intersection_of_line

end EuclidGeom
