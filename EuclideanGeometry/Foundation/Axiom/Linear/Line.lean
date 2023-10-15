import EuclideanGeometry.Foundation.Axiom.Linear.Colinear
import EuclideanGeometry.Foundation.Axiom.Linear.Ray
import EuclideanGeometry.Foundation.Axiom.Linear.Ray_ex

noncomputable section
namespace EuclidGeom

section setoid

variable {P : Type _} [EuclideanPlane P]

def same_extn_line : Ray P → Ray P → Prop := fun r₁ r₂ => r₁.toProj = r₂.toProj ∧ (r₂.source LiesOn r₁ ∨ r₂.source LiesOn r₁.reverse)

namespace same_extn_line

theorem dir_eq_or_eq_neg {x y : Ray P} (h : same_extn_line x y) : (x.toDir = y.toDir ∨ x.toDir = - y.toDir) := (Dir.eq_toProj_iff _ _).mp h.1

theorem vec_parallel_of_same_extn_line {x y : Ray P} (h : same_extn_line x y) : ∃t : ℝ, y.toDir.toVec = t • x.toDir.toVec := by
  rcases (Dir.eq_toProj_iff _ _).mp h.1 with xy | xy
  · use 1
    rw [one_smul, xy]
  · use -1
    rw [xy, Dir.toVec_neg_eq_neg_toVec, smul_neg, neg_smul, one_smul, neg_neg]

protected theorem refl (x : Ray P) : same_extn_line x x := ⟨rfl, Or.inl (Ray.source_lies_on)⟩

protected theorem symm {x y : Ray P} (h : same_extn_line x y) : same_extn_line y x := by
  constructor
  · exact h.1.symm
  · have g := dir_eq_or_eq_neg h
    cases g with
    | inl h₁ => sorry
    | inr h₂ => sorry


protected theorem trans {x y z : Ray P} (h₁ : same_extn_line x y) (h₂ : same_extn_line y z) : same_extn_line x z where
  left := Eq.trans h₁.1 h₂.1
  right := by
    rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h₁.2 with ⟨a, dyx⟩
    rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h₂.2 with ⟨b, dzy⟩
    apply pt_lies_on_line_from_ray_iff_vec_parallel.mpr
    let ⟨t, xpary⟩ := vec_parallel_of_same_extn_line h₁
    use a + b * t
    rw [xpary] at dzy
    rw [(vec_add_vec _ _ _).symm, dyx, dzy]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_add]
    ring_nf

protected def setoid : Setoid (Ray P) where
  r := same_extn_line
  iseqv := {
    refl := same_extn_line.refl
    symm := same_extn_line.symm
    trans := same_extn_line.trans
  }

instance : Setoid (Ray P) := same_extn_line.setoid

end same_extn_line

theorem same_extn_line_of_PM (A : P) (x y : Dir) (h : PM x y) : same_extn_line (Ray.mk A x) (Ray.mk A y) := by
  constructor
  · simp only [Ray.toProj, Dir.eq_toProj_iff', h]
  · exact Or.inl Ray.source_lies_on

theorem same_extn_line.eq_carrier_union_rev_carrier (ray ray' : Ray P) (h : same_extn_line ray ray') : ray.carrier ∪ ray.reverse.carrier = ray'.carrier ∪ ray'.reverse.carrier := by
  ext p
  simp only [Set.mem_union, Ray.in_carrier_iff_lies_on, pt_lies_on_line_from_ray_iff_vec_parallel]
  let ⟨a, ha⟩ := pt_lies_on_line_from_ray_iff_vec_parallel.mp h.symm.2
  let ⟨b, hb⟩ := vec_parallel_of_same_extn_line h.symm
  constructor
  · intro hc
    rcases hc with ⟨c, hc⟩
    use a + c * b
    calc
      VEC ray'.source p = VEC ray'.source ray.source + VEC ray.source p := (vec_add_vec _ _ _).symm
      _ = a • ray'.toDir.toVec + c • ray.toDir.toVec := by rw [ha, hc]
      _ = a • ray'.toDir.toVec + (c * b) • ray'.toDir.toVec := by
        simp only [hb, Complex.real_smul, Complex.ofReal_mul, add_right_inj]
        ring_nf
      _ = (a + c * b) • ray'.toDir.toVec := (add_smul _ _ _).symm
  · sorry
  /-
  Proof for the second case is almost the same with the first case.
  I suppose it better to write a tactic for this kind of proof ?
  (i.e., reducing arguments about `•` and `VEC`) 

  Another issue is that, `Lean Infoview` doesn't show enough info about the type. 
  e.g., there could be `Dir.toVec = b • Dir.toVec` in `Infoview`, but moving cursor to `Dir.toVec` doesn't tells me which is the argument of this function.
  -/

end setoid

def Line (P : Type _) [EuclideanPlane P] := Quotient (@same_extn_line.setoid P _)

variable {P : Type _} [EuclideanPlane P]

section make

namespace Line

-- define a line from two points
def mk_pt_pt (A B : P) (h : B ≠ A) : Line P := ⟦RAY A B h⟧

-- define a line from a point and a proj
def mk_pt_proj (A : P) (proj : Proj) : Line P := Quotient.map (sa := PM.con.toSetoid) (fun x : Dir => Ray.mk A x) (same_extn_line_of_PM A) proj

-- define a line from a point and a direction
def mk_pt_dir (A : P) (dir : Dir) : Line P := mk_pt_proj A dir.toProj

-- define a line from a point and a nondegenerate vector
def mk_pt_vec_nd (A : P) (vec_nd : Vec_nd) : Line P := mk_pt_proj A vec_nd.toProj

end Line

scoped notation "LIN" => Line.mk_pt_pt

end make

section coercion

def Line.toProj (l : Line P) : Proj := Quotient.lift (fun ray : Ray P => ray.toProj) (fun _ _ h => And.left h) l

def Ray.toLine (ray : Ray P) : Line P := ⟦ray⟧

theorem ray_toLine_eq_of_same_extn_line {r₁ r₂ : Ray P} (h : same_extn_line r₁ r₂) : r₁.toLine = r₂.toLine := Quotient.eq.mpr h

def Seg_nd.toLine (seg_nd : Seg_nd P) : Line P := ⟦seg_nd.toRay⟧

instance : Coe (Ray P) (Line P) where
  coe := Ray.toLine

section carrier

namespace Line

protected def carrier (l : Line P) : Set P := Quotient.lift (fun ray : Ray P => ray.carrier ∪ ray.reverse.carrier) (same_extn_line.eq_carrier_union_rev_carrier) l

/- Def of point lies on a line, LiesInt is not defined -/
protected def IsOn (a : P) (l : Line P) : Prop :=
  a ∈ l.carrier

instance : Carrier P (Line P) where
  carrier := fun l => l.carrier

theorem linear (l : Line P) {A B C : P} (h₁ : A LiesOn l) (h₂ : B LiesOn l) (h₃ : C LiesOn l) : colinear A B C := by
  unfold Line at l
  revert l
  rw [Quotient.forall (p := fun k : Line P => A LiesOn k → B LiesOn k → C LiesOn k → colinear A B C)]
  unfold lies_on instCarrierLine Carrier.carrier Line.carrier at *
  simp only
  intro ray a b c
  rw [@Quotient.lift_mk _ _ same_extn_line.setoid _ _ _] at *
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      cases c with
      | inl c =>
        exact Ray.colinear_of_lies_on a b c
      | inr c =>
        let ray' := Ray.mk C ray.toDir
        have a' : A ∈ ray'.carrier := lies_on_pt_toDir_of_pt_lies_on_rev a c
        have b' : B ∈ ray'.carrier := lies_on_pt_toDir_of_pt_lies_on_rev b c
        exact Ray.colinear_of_lies_on a' b' (Ray.source_lies_on)
    | inr b =>
      cases c with
      | inl c => sorry
      | inr c => sorry
  | inr a =>
    cases b with
    | inl b =>
      cases c with
      | inl c => sorry
      | inr c => sorry
    | inr b =>
      cases c with
      | inl c => sorry
      | inr c => sorry

theorem maximal (l : Line P) {A B : P} (h₁ : A ∈ l.carrier) (h₂ : B ∈ l.carrier) (h : B ≠ A) : (∀ (C : P), colinear A B C → (C ∈ l.carrier)) := sorry

theorem nontriv (l : Line P) : ∃ (A B : P), (A ∈ l.carrier) ∧ (B ∈ l.carrier) ∧ (B ≠ A) := sorry

end Line

-- A point lies on a line associated to a ray if and only if it lies on the ray or the reverse of the ray

theorem Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev (A : P) (ray : Ray P) : (A LiesOn ray.toLine) ↔ (A LiesOn ray) ∨ (A LiesOn ray.reverse) := sorry

theorem Ray.lies_on_toLine_iff_lies_int_or_lies_int_rev_or_eq_source (A : P) (ray : Ray P) : (A LiesOn ray.toLine) ↔ (A LiesInt ray) ∨ (A LiesInt ray.reverse) ∨ (A = ray.source) := sorry

end carrier

end coercion

end EuclidGeom