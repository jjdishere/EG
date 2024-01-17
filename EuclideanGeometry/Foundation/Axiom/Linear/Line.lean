import EuclideanGeometry.Foundation.Axiom.Linear.Collinear
import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section
namespace EuclidGeom

section setoid

variable {P : Type _} [EuclideanPlane P]

-- `Future change plan` Change this to "structure" instead of "and".
/-- We say that rays $r$ and $r'$ \emph{induce the same directed line} if, (1) they have the same direction, and (2) the source of $r'$ lies on $r$ or the reverse range of $r$.-/
def same_dir_line : Ray P → Ray P → Prop :=
  fun r r' => r.toDir = r'.toDir ∧ (r'.source LiesOn r ∨ r'.source LiesOn r.reverse)

namespace same_dir_line

/-- Rays $r$ and $r$ induce the same directed line. -/
protected theorem refl (r : Ray P) : same_dir_line r r := ⟨rfl, .inl r.source_lies_on⟩

/-- If $r$ and $r'$ induce the same directed line, then $r'$ and $r$ induce the same directed line. -/
protected theorem symm {r r' : Ray P} (h : same_dir_line r r') : same_dir_line r' r := by
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h.2 with ⟨a, dxy⟩
  refine' ⟨h.1.symm, pt_lies_on_line_from_ray_iff_vec_parallel.mpr ⟨- a, _⟩⟩
  rw [← neg_vec, dxy, neg_smul, neg_inj]
  congr 2
  exact h.1

/-- If $r$, $r'$, and $r''$ are rays such that $r$ and $r'$ induce the same directed line, and $r'$ and $r''$ induce the same directed line, then $r$ and $r''$ induce the same directed line. -/
protected theorem trans {r r' r'' : Ray P} (h₁ : same_dir_line r r') (h₂ : same_dir_line r' r'') : same_dir_line r r'' := by
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h₁.2 with ⟨a, dr⟩
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h₂.2 with ⟨b, dr'⟩
  refine' ⟨h₁.1.trans h₂.1, pt_lies_on_line_from_ray_iff_vec_parallel.mpr ⟨a + b, _⟩⟩
  rw [← vec_add_vec, dr, dr', ← h₁.1]
  exact (add_smul a b _).symm

/-- Define an equivalence relation of rays with the same directed line, consisting of reflexive, symmetric, and transitivity conditions. -/
protected def setoid : Setoid (Ray P) where
  r := same_dir_line
  iseqv := {
    refl := same_dir_line.refl
    symm := same_dir_line.symm
    trans := same_dir_line.trans
  }

end same_dir_line

/-- We say two rays $r$ and $r'$ \emph{have the same extension line} if, (1) they have the same projective direction, and (2) if the sourse of $r'$ lies either on $r$ or the reverse ray of $r$. -/
def same_extn_line : Ray P → Ray P → Prop := fun r r' => r.toProj = r'.toProj ∧ (r'.source LiesOn r ∨ r'.source LiesOn r.reverse)

namespace same_extn_line

/-- If two rays $r$ and $r'$ have the same extension line, then either they have the same direction or opposite direction. -/
theorem dir_eq_or_eq_neg {r r' : Ray P} (h : same_extn_line r r') : (r.toDir = r'.toDir ∨ r.toDir = - r'.toDir) :=
  Dir.toProj_eq_toProj_iff.mp h.1

/-- If two rays $r$ and $r'$ have the same extension line, then the unit vector determined by $r'$ is some real multiple of the unit vecgtor determined by $r$. -/
theorem vec_parallel_of_same_extn_line {r r' : Ray P} (h : same_extn_line r r') : ∃ t : ℝ, r'.toDir.unitVec = t • r.toDir.unitVec :=
  Or.casesOn (dir_eq_or_eq_neg h) (fun rr' ↦ ⟨1, by rw [one_smul, rr']⟩)
    fun rr' ↦ ⟨- 1, by rw [rr']; simp⟩

/-- The reverse of a ray have the same extension line as the ray. -/
theorem ray_rev_of_same_extn_line {r : Ray P} : same_extn_line r r.reverse :=
  ⟨Ray.toProj_of_rev_eq_toProj.symm, .inr Ray.source_lies_on⟩


/-- For two distinct points $A$ and $B$, if $A$ lies on a ray $r$ or its reverse ray and $B$ also lies on $r$ or its reverse ray, then the ray $r$ and the ray $\overline{AB}$ have the same extension line. -/
theorem pt_pt_ray_same_extn_line_of_pt_pt_lies_on_line {A B : P} {r : Ray P} [_h : PtNe B A] (ha : A LiesOn r ∨ A LiesOn r.reverse) (hb : B LiesOn r ∨ B LiesOn r.reverse) : same_extn_line r (RAY A B) :=
  ⟨ray_toProj_eq_mk_pt_pt_toProj ha hb, ha⟩

/-- A ray $r$ has the same extension line as itself.-/
protected theorem refl (r : Ray P) : same_extn_line r r := ⟨rfl, .inl Ray.source_lies_on⟩

/-- The symmetric property of same_extn_line. It states that if two rays $r$ and $r'$ have the same extension line, then $r'$ and $r$ also have the same extension line. -/
protected theorem symm {r r' : Ray P} (h : same_extn_line r r') : same_extn_line r' r := by
  refine' ⟨h.1.symm, pt_lies_on_line_from_ray_iff_vec_parallel.mpr _⟩
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h.2 with ⟨a, dxy⟩
  rcases dir_eq_or_eq_neg h with xy | xy
  · use -a
    rw [← neg_vec, dxy, ← neg_smul, xy]
  · use a
    rw [← neg_vec, dxy, xy]
    simp

/-- The transitivity of the same extension line relation. If $r$, $r'$, and $r''$ are rays such that $r$ and $r'$ have the same extension line, and $r'$ and $r''$ have the same extension line, then $r$ and $r''$ have the same extension line. -/
protected theorem trans {r r' r'' : Ray P} (h₁ : same_extn_line r r') (h₂ : same_extn_line r' r'') : same_extn_line r r'' := by
  refine' ⟨h₁.1.trans h₂.1, pt_lies_on_line_from_ray_iff_vec_parallel.mpr _⟩
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h₁.2 with ⟨a, dr⟩
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h₂.2 with ⟨b, dr'⟩
  let ⟨t, rparr'⟩ := vec_parallel_of_same_extn_line h₁
  use a + b * t
  rw [← vec_add_vec, dr, dr', rparr', smul_smul, ← add_smul]

protected def setoid : Setoid (Ray P) where
  r := same_extn_line
  iseqv := {
    refl := same_extn_line.refl
    symm := same_extn_line.symm
    trans := same_extn_line.trans
  }

-- instance : Setoid (Ray P) := same_extn_line.setoid

end same_extn_line

/-- Given two directions, either the same or opposite, the rays starting from a same point with the two directions have the same extension line. -/
theorem same_extn_line_of_PM (A : P) {x y : Dir} (h : x = y ∨ x = -y) : same_extn_line (Ray.mk A x) (Ray.mk A y) :=
  ⟨by simp only [Ray.toProj, Dir.toProj_eq_toProj_iff, h], .inl Ray.source_lies_on⟩

/-- If two rays $r$ and $r'$ have the same extension lines, then the union of the set of $r'$ and its reverse is contained in the union of the set of $r$ and its reverse. -/
theorem same_extn_line.subset_carrier_union_rev_carrier {r r' : Ray P} (h : same_extn_line r r') : r'.carrier ∪ r'.reverse.carrier ⊆ r.carrier ∪ r.reverse.carrier := by
  intro p hp
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp h.2 with ⟨a, ha⟩
  rcases dir_parallel_of_same_proj h.1 with ⟨b, hb⟩
  rcases pt_lies_on_line_from_ray_iff_vec_parallel.mp hp with ⟨c, hc⟩
  refine' pt_lies_on_line_from_ray_iff_vec_parallel.mpr ⟨a + c * b, _⟩
  rw [← vec_add_vec, ha, hc, hb, smul_smul, ← add_smul]

/-- If two rays $r$ and $r'$ have the same extension lines, then the union of the set of $r'$ and its reverse is the same as the union of the set of $r$ and its reverse. -/
theorem same_extn_line.eq_carrier_union_rev_carrier (r r' : Ray P) (h : same_extn_line r r') : r.carrier ∪ r.reverse.carrier = r'.carrier ∪ r'.reverse.carrier :=
  Set.Subset.antisymm_iff.mpr ⟨h.symm.subset_carrier_union_rev_carrier, h.subset_carrier_union_rev_carrier⟩


/-- This theorem gives the relation between two equivalence relations: having the same directed line implies having the same extension line. -/
theorem same_dir_line_le_same_extn_line : same_dir_line.setoid (P := P) ≤ same_extn_line.setoid :=
  fun _ _ h => ⟨congr_arg Dir.toProj h.1, h.2⟩

end setoid

/-- A \emph{directed line} is the equivalence class of rays with the same directed lines. -/
def DirLine (P : Type _) [EuclideanPlane P] := Quotient (@same_dir_line.setoid P _)

/-- A \emph{line} is the equivalence class of rays with the same exetnsion lines. -/
def Line (P : Type _) [EuclideanPlane P] := Quotient (@same_extn_line.setoid P _)

variable {P : Type _} [EuclideanPlane P]

section make

namespace DirLine

/-- Given two distinct points $A$ and $B$,  this function returns the directed line starting
from $A$ in the direction of $B$. We use $\verb|DLIN| A B$ or $\verb|DLIN| A B h$ to abbreviate
$\verb|DLine.mk_pt_pt| A B h$, where $h$ is a statement that $A \neq B$. When such statement $h$
is missing, we search it in all the known facts. -/
def mk_pt_pt (A B : P) (h : B ≠ A) : DirLine P := Quotient.mk same_dir_line.setoid (RAY A B h)

/-- Given a point $A$ and a direction, this function returns the directed line starting from $A$ in the given direction. -/
def mk_pt_dir (A : P) (dir : Dir) : DirLine P := Quotient.mk same_dir_line.setoid (Ray.mk A dir)

/-- Given a point $A$ and a nondegenerate vector, this function returns the directed line starting from $A$ in the same direction of the nondegenerate vector. -/
def mk_pt_vec_nd (A : P) (vec_nd : VecND) : DirLine P := mk_pt_dir A vec_nd.toDir

end DirLine

namespace Line

/-- Given two distinct points $A$ and $B$, this function returns the line passing through
$A$ and $B$. We use $\verb|LIN| A B$ or $\verb|LIN| A B h$ to abbreviate
$\verb|Line.mk_pt_pt| A B h$, where $h$ is a statement that $A \neq B$. When such statement $h$
is missing, we search it in all the known facts. -/
def mk_pt_pt (A B : P) (h : B ≠ A) : Line P := Quotient.mk same_extn_line.setoid (RAY A B h)

/-- Given a point $A$ and a projective direction, this function returns the line through $A$ along the given projective direction. -/
def mk_pt_proj (A : P) (proj : Proj) : Line P :=
  proj.lift (fun x : Dir => Quotient.mk (@same_extn_line.setoid P _) <| Ray.mk A x : Dir → Line P)
    (fun _ ↦ Quotient.sound <| same_extn_line_of_PM A (.inr rfl))

/-- Given a point $A$ and a direction, this function returns the line through $A$ along the given direction. -/
def mk_pt_dir (A : P) (dir : Dir) : Line P := mk_pt_proj A dir.toProj

@[simp]
lemma mkPtProj_toProj (A : P) (dir : Dir) : mk_pt_proj A dir.toProj = mk_pt_dir A dir := rfl

/-- Given a point $A$ and a nondegenerate vector, this function returns the line through $A$ along the nondegenerate vector. -/
def mk_pt_vec_nd (A : P) (vec_nd : VecND) : Line P := mk_pt_proj A vec_nd.toProj

end Line

@[inherit_doc Line.mk_pt_pt]
scoped syntax "LIN" ws term:max ws term:max (ws term:max)? : term

macro_rules
  | `(LIN $A $B) => `(Line.mk_pt_pt $A $B (@Fact.out _ inferInstance))
  | `(LIN $A $B $h) => `(Line.mk_pt_pt $A $B $h)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `Line.mk_pt_pt` -/
@[delab app.EuclidGeom.Line.mk_pt_pt]
def delabLineMkPtPt : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``Line.mk_pt_pt 5
  let A ← withNaryArg 2 delab
  let B ← withNaryArg 3 delab
  withNaryArg 4 do
    if (← getExpr).isAppOfArity' ``Fact.out 2 then
      `(LIN $A $B)
    else
      `(LIN $A $B $(← delab))

@[inherit_doc DirLine.mk_pt_pt]
scoped syntax "DLIN" ws term:max ws term:max (ws term:max)? : term

macro_rules
  | `(DLIN $A $B) => `(DirLine.mk_pt_pt $A $B (@Fact.out _ inferInstance))
  | `(DLIN $A $B $h) => `(DirLine.mk_pt_pt $A $B $h)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `DirLine.mk_pt_pt` -/
@[delab app.EuclidGeom.DirLine.mk_pt_pt]
def delabDirLineMkPtPt : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``DirLine.mk_pt_pt 5
  let A ← withNaryArg 2 delab
  let B ← withNaryArg 3 delab
  withNaryArg 4 do
    if (← getExpr).isAppOfArity' ``Fact.out 2 then
      `(DLIN $A $B)
    else
      `(DLIN $A $B $(← delab))

end make

section coercion

/-- Given a directed line, this function returns its direction. -/
@[pp_dot]
def DirLine.toDir (l : DirLine P) : Dir :=
  Quotient.lift (s := same_dir_line.setoid) (fun ray => ray.toDir) (fun _ _ h => h.left) l

/-- Given a directed line, this function returns its projected direction. -/
@[pp_dot]
abbrev DirLine.toProj (l : DirLine P) : Proj := l.toDir.toProj

/-- Given a directed line, this function returns the associated line. -/
@[pp_dot]
def DirLine.toLine (l : DirLine P) : Line P :=
  Quotient.lift (⟦·⟧) (fun _ _ h => Quotient.sound $ same_dir_line_le_same_extn_line h) l

/-- Given a ray, this function returns the associated directed line. -/
@[pp_dot]
abbrev Ray.toDirLine (ray : Ray P) : DirLine P := ⟦ray⟧

/-- Given a nondegenerate segment, this function returns the directed line in the direction of the segment. -/
@[pp_dot]
abbrev SegND.toDirLine (seg_nd : SegND P) : DirLine P := seg_nd.toRay.toDirLine

/-- Given a line, this function returns its projective direction. -/
@[pp_dot]
def Line.toProj (l : Line P) : Proj :=
  Quotient.lift (s := same_extn_line.setoid) (fun ray : Ray P => ray.toProj) (fun _ _ h => h.left) l

/-- Given a ray, this function returns the line associated with the ray. -/
@[pp_dot]
abbrev Ray.toLine (ray : Ray P) : Line P := ⟦ray⟧

/-- Given a nondegenerate segment, this function returns the line associated with the ray. -/
@[pp_dot]
abbrev SegND.toLine (seg_nd : SegND P) : Line P := ⟦seg_nd.toRay⟧

/-- An induction principle to deduce results for directed lines from those for rays,
used with `induction l using DirLine.ind` or `induction' l using DirLine.ind with r`. -/
@[elab_as_elim]
protected theorem DirLine.ind {C : DirLine P → Prop} (h : ∀ (r : Ray P), C r.toDirLine) (l : DirLine P) : C l :=
  Quotient.ind h l

/-- An induction principle to deduce results for lines from those for rays,
used with `induction l using Line.ind` or `induction' l using Line.ind with r`. -/
@[elab_as_elim]
protected theorem Line.ind {C : Line P → Prop} (h : ∀ (r : Ray P), C r.toLine) (l : Line P) : C l :=
  Quotient.ind h l

end coercion

/-- Given a point $A$ and a direction $dir$, the line associated to the ray starting at $A$ in the direction of $dir$ is the same as the line through $A$ in the direction of $dir$. -/
@[simp]
lemma mkPtProj_toLine (A : P) (dir : Dir) : (Ray.mk A dir).toLine = Line.mk_pt_dir A dir :=
  rfl

section coercion_compatibility

/-- Given a directed line $l$, its projective direction is the same as the projective direction of the line associated to $l$. -/
theorem DirLine.toLine_toProj_eq_toProj (l : DirLine P) : l.toLine.toProj = l.toProj := by
  induction l using DirLine.ind
  rfl

/-- The line associated to a ray is the same as the line associated to the directed line of the ray. -/
theorem Ray.toLine_eq_toDirLine_toLine (ray : Ray P) : ray.toLine = ray.toDirLine.toLine := rfl

/-- For coercion purpose, a ray can induce a directed line. -/
instance : Coe (Ray P) (DirLine P) where
  coe := Ray.toDirLine

/-- For coercion purpose, a directed line can induce a line. -/
instance : Coe (DirLine P) (Line P) where
  coe := DirLine.toLine

/-- For coercion purpose, a ray can induce a line. -/
instance : Coe (Ray P) (Line P) where
  coe := Ray.toLine

end coercion_compatibility

open Classical

section carrier

namespace Line

/-- Given a line $l$, this function returns the set of points that lies on the line $l$. -/
protected def carrier (l : Line P) : Set P := Quotient.lift (fun ray : Ray P => ray.carrier ∪ ray.reverse.carrier) (same_extn_line.eq_carrier_union_rev_carrier) l

/-- This function returns whether a point $A$ lies on a line $l$ or not.  `Note that no definition of LiesInt is given.` -/
protected def IsOn (A : P) (l : Line P) : Prop :=
  A ∈ l.carrier

/-- A line is a figure in the Euclidean geometry, meaning that one can talk about its underlying subset of points. -/
instance : Fig (Line P) P where
  carrier := Line.carrier

end Line

namespace DirLine

/-- For a directed line, this function returns its underlying subset. -/
protected abbrev carrier (l : DirLine P) : Set P := l.toLine.carrier

/-- A directed line is a figure in the Euclidean geometry, meaning that one can talk about its underlying subset of points. -/
instance : Fig (DirLine P) P where
  carrier := DirLine.carrier

end DirLine

/-- The underlying set of the line associated to a ray is teh union of the underlying set of the ray and the underlying set of the reverse of the ray. -/
theorem Ray.toLine_carrier_eq_ray_carrier_union_rev_carrier (r : Ray P) : r.toLine.carrier = r.carrier ∪ r.reverse.carrier := rfl


/-- A point lies on a line associated to a ray if and only if it lies on the ray or the reverse of the ray. -/
theorem Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev {A : P} {r : Ray P} : (A LiesOn r.toLine) ↔ (A LiesOn r) ∨ (A LiesOn r.reverse) :=
  Iff.rfl

/-- This theorem states that a point A lies on the directed line associated to a ray r if and only if A lies on the ray r or A lies on the reverse of the ray r. -/
theorem Ray.lies_on_toDirLine_iff_lies_on_or_lies_on_rev {A : P} {r : Ray P} : (A LiesOn r.toDirLine) ↔ (A LiesOn r) ∨ (A LiesOn r.reverse) :=
  Iff.rfl

/-- A point lies on the line associated to a directed line if and only if it lies on the line. -/
theorem DirLine.lies_on_iff_lies_on_toLine {A : P} {l : DirLine P} : (A LiesOn l.toLine) ↔ (A LiesOn l) :=
  Iff.rfl

/-- If a point lies on a ray, then it lies on the line associated to the ray. -/
theorem Ray.lies_on_toLine_of_lie_on {A : P} {r : Ray P} (h : A LiesOn r) : A LiesOn r.toLine := .inl h

/-- Given a point A lying on a nondegenerate segment s, the point A also lies on the line associated to s. -/
theorem SegND.lies_on_toLine_of_lie_on {A : P} {s : SegND P}(h : A LiesOn s.1) : A LiesOn s.toLine :=
  .inl (lies_on_toRay_of_lies_on h)

/-- The source of a ray lies on the line associated to the ray. -/
theorem Ray.source_lies_on_toLine {r : Ray P} : r.source LiesOn r.toLine :=
  r.lies_on_toLine_of_lie_on r.source_lies_on

/-- The source of a nondegenerate segment lies on the line associated to the segment. -/
theorem SegND.source_lies_on_toLine {s : SegND P}: s.1.source LiesOn s.toLine :=
  s.toRay.source_lies_on_toLine

/-- The target point of a nondegenerate segment lies on the line associated to the segment. -/
theorem SegND.target_lies_on_toLine {s: SegND P} : s.1.target LiesOn s.toLine :=
  s.lies_on_toLine_of_lie_on s.1.target_lies_on

/-- If a point lies on a ray, then it lies on the directed line associated to the ray. -/
theorem Ray.lies_on_toDirLine_of_lie_on {A : P} {r : Ray P}(h : A LiesOn r) : A LiesOn r.toDirLine := .inl h

/-- This theorem states that if a point A lies on a nondegenerate segment s, then A also lies on the directed line associated to s. -/
theorem SegND.lies_on_toDirLine_of_lie_on {A : P} {s : SegND P} (h : A LiesOn s.1) : A LiesOn s.toDirLine :=
  .inl (lies_on_toRay_of_lies_on h)

/-- The source of a ray lies on the directed line associated to the ray. -/
theorem Ray.source_lies_on_toDirLine {r : Ray P} : r.source LiesOn r.toDirLine :=
  r.lies_on_toLine_of_lie_on r.source_lies_on

/-- The source of a nondegenerate segment lies on the directed line associated to the segment. -/
theorem SegND.source_lies_on_toDirLine {s : SegND P} : s.1.source LiesOn s.toDirLine :=
  s.toRay.source_lies_on_toLine

/-- The target point of a nondegenerate segment lies on the directed line associated to the segment. -/
theorem SegND.target_lies_on_toDirLine {s : SegND P} : s.1.target LiesOn s.toDirLine :=
  s.lies_on_toLine_of_lie_on s.1.target_lies_on

end carrier

section dirline_toRay

-- the assumption h is for properties, not for construction
/-- Given a point $A$ lying on a directed line $l$, this function returns the ray starting from $A$ in the direction of $l$. -/
def Ray.mk_pt_dirline (A : P) (l : DirLine P) (_h : A LiesOn l) : Ray P := Ray.mk A l.toDir

/-- Given a point $A$ lying on a directed line $l$, the directed line associated to the ray from $A$ in the direction of $l$ is precisely $l$ itself. -/
theorem ray_of_pt_dirline_toDirLine_eq_dirline (A : P) (l : DirLine P) (h : A LiesOn l) : (Ray.mk_pt_dirline A l h).toDirLine = l := by
  induction l using DirLine.ind
  exact Quotient.sound (same_dir_line.symm ⟨rfl, h⟩)

-- `change to {A : P} and {l : DirLine P}`?
/-- Given a point A lying on a directed line l, the direction of the ray starting from A in the direction of l is the same as the direction of l. -/
theorem ray_of_pt_dirline_toDirLine_toDir_eq_dirline_toDir {A : P} {l : DirLine P} (h : A LiesOn l) : (Ray.mk_pt_dirline A l h).toDir = l.toDir := rfl

end dirline_toRay

namespace DirLine

section reverse

/-- Given a directed line, the function returns the reverse of the directed line. -/
@[pp_dot]
def reverse (l : DirLine P) : DirLine P := by
  refine' Quotient.lift (⟦·.reverse⟧) (fun a b h ↦ _) l
  exact (@Quotient.eq _ same_dir_line.setoid _ _).mpr ⟨neg_inj.mpr h.1, Ray.lies_on_rev_or_lies_on_iff.mp h.2⟩

/-- Given a directed line $l$, the direction of its reverse is the opposite of its direction. -/
theorem rev_toDir_eq_neg_toDir {l : DirLine P} : l.reverse.toDir = - l.toDir := by
  induction l using DirLine.ind
  rfl

/-- The reverse of the reverse of a directed line is the line itself. -/
theorem rev_rev_eq_self {l : DirLine P} : l.reverse.reverse = l := by
  induction' l using DirLine.ind with r
  exact congrArg (@Quotient.mk _ same_dir_line.setoid) r.rev_rev_eq_self

/-- A point lies on the reverse of a directed line if and only if it lies on the directed line. -/
theorem lies_on_rev_iff_lies_on {A : P} {l : DirLine P} : A LiesOn l.reverse ↔ A LiesOn l := by
  induction' l using DirLine.ind with r
  exact (r.lies_on_rev_or_lies_on_iff).symm

end reverse

section line_dirline_compatibility

/-- Given a directed line $l$, the line associted to the reverse of $l$ is the same as the line associated to $l$. -/
theorem rev_toLine_eq_toLine (l : DirLine P) : l.reverse.toLine = l.toLine := by
  induction l using DirLine.ind
  exact (@Quotient.eq _ same_extn_line.setoid _ _).mpr same_extn_line.ray_rev_of_same_extn_line.symm

/-- Given two directed lines $l_1$ and $l_2$ with the same associated line, if they have the same direcdtion, they are equal. -/
theorem eq_of_toDir_eq_of_toLine_eq {l₁ l₂ : DirLine P} (h : l₁.toLine = l₂.toLine) (hd : l₁.toDir = l₂.toDir) : l₁ = l₂ := by
  induction l₁ using DirLine.ind
  induction l₂ using DirLine.ind
  exact (@Quotient.eq _ same_dir_line.setoid _ _).2 ⟨hd, ((@Quotient.eq _ same_extn_line.setoid _ _).1 h).2⟩

/-- Given two directed lines $l_1$ and $l_2$ with the same associated line, if they have the opposite direction, they are reverse of each other. -/
theorem eq_rev_of_toDir_eq_neg_of_toLine_eq {l₁ l₂ : DirLine P} (h : l₁.toLine = l₂.toLine) (hd : l₁.toDir = - l₂.toDir) : l₁ = l₂.reverse := by
  induction l₁ using DirLine.ind
  induction l₂ using DirLine.ind
  exact (@Quotient.eq _ same_dir_line.setoid _ _).2 ⟨hd, ((@Quotient.eq _ same_extn_line.setoid _ _).1 h).2⟩

/-- Given two directed lines $l_1$ and $l_2$ with the same associated line, if they have different directions, then $l_1$ is the reverse of $l_2$. -/
theorem eq_rev_of_toDir_ne_of_toLine_eq {l₁ l₂ : DirLine P} (h : l₁.toLine = l₂.toLine) (hd : l₁.toDir ≠ l₂.toDir) : l₁ = l₂.reverse :=
  have hp : l₁.toProj = l₂.toProj := by rw [← l₁.toLine_toProj_eq_toProj, h, l₂.toLine_toProj_eq_toProj]
  eq_rev_of_toDir_eq_neg_of_toLine_eq h ((Dir.toProj_eq_toProj_iff.mp hp).resolve_left hd)

/-- Given two directed lines $l_1$ and $l_2$, if their associated lines are equal, then either the directed lines are equal or one is the reverse of the other. -/
theorem eq_or_eq_rev_of_toLine_eq {l₁ l₂ : DirLine P} (h : l₁.toLine = l₂.toLine) : l₁ = l₂ ∨ l₁ = l₂.reverse :=
  if hd : l₁.toDir = l₂.toDir then .inl (eq_of_toDir_eq_of_toLine_eq h hd)
  else .inr (eq_rev_of_toDir_ne_of_toLine_eq h hd)

end line_dirline_compatibility

end DirLine

namespace Line

section pt_pt

/-- Let $A$ and $B$ be two distinct points, the line through $A$ and $B$ is the same as the line through $B$ and $A$. -/
theorem line_of_pt_pt_eq_rev {A B : P} [_h : PtNe B A] : LIN A B = LIN B A :=
  (Quotient.eq (r := same_extn_line.setoid)).mpr
    ⟨Ray.toProj_eq_toProj_of_mk_pt_pt, .inl (Ray.snd_pt_lies_on_mk_pt_pt (B := B))⟩

/-- For two distinct points $A$ and $B$, $A$ lies on the line through $A$ and $B$. -/
theorem fst_pt_lies_on_mk_pt_pt {A B : P} [_h : PtNe B A] : A LiesOn LIN A B :=
  .inl Ray.source_lies_on

/-- The point $B$ lies on the line through $A$ and $B$. -/
theorem snd_pt_lies_on_mk_pt_pt {A B : P} [_h : PtNe B A] : B LiesOn LIN A B := by
  rw [line_of_pt_pt_eq_rev]
  exact fst_pt_lies_on_mk_pt_pt

/-- The first point and the second point in `Line.mk_pt_pt` LiesOn the line it makes. -/
theorem pt_lies_on_line_of_pt_pt_of_ne {A B : P} [_h : PtNe B A] : A LiesOn LIN A B ∧ B LiesOn LIN A B :=
  ⟨fst_pt_lies_on_mk_pt_pt, snd_pt_lies_on_mk_pt_pt⟩

/-- Two point determines a line, i.e. given two distinct points $A$ and $B$ on a line $l$, the line through $A$ and $B$ is the same as $l$. -/
theorem eq_line_of_pt_pt_of_ne {A B : P} {l : Line P} [_h : PtNe B A] (ha : A LiesOn l) (hb : B LiesOn l) : LIN A B = l := by
  induction' l using Line.ind with r
  exact (Quotient.eq (r := same_extn_line.setoid)).mpr <|
    same_extn_line.symm ⟨ray_toProj_eq_mk_pt_pt_toProj ha hb, ha⟩

/-- If two lines have two distinct intersection points, then these two lines are identical. -/
theorem eq_of_pt_pt_lies_on_of_ne {A B : P} [_h : PtNe B A] {l₁ l₂ : Line P} (hA₁ : A LiesOn l₁) (hB₁ : B LiesOn l₁) (hA₂ : A LiesOn l₂) (hB₂ : B LiesOn l₂) : l₁ = l₂ := by
  rw [← eq_line_of_pt_pt_of_ne hA₁ hB₁]
  exact eq_line_of_pt_pt_of_ne hA₂ hB₂

/-- The theorem states that two distinct points A and B lie on a line $l$ if and only if the line through $A$ and $B$ is equal to $l$. -/
theorem eq_pt_pt_line_iff_lies_on {A B : P} {l : Line P} [_h : PtNe B A] : A LiesOn l ∧ B LiesOn l ↔ LIN A B = l := by
  refine' ⟨fun ⟨ha, hb⟩ ↦ eq_line_of_pt_pt_of_ne ha hb, fun lAB ↦ _⟩
  rw [← lAB]
  exact pt_lies_on_line_of_pt_pt_of_ne

/-- The theorem states that two distinct points $A$ and $B$ lie on a line $l$ if and only if the line associated to the ray from $A$ to $B$ is equal to $l$. -/
theorem pt_pt_lies_on_iff_ray_toLine {A B : P} {l : Line P} [_h : PtNe B A] : A LiesOn l ∧ B LiesOn l ↔ (RAY A B).toLine = l :=
  eq_pt_pt_line_iff_lies_on

/-- The theorem states that two distinct points $A$ and $B$ lies on a line $l$ if and only if the line associated with the nondegenerate segment $AB$ is the same as line $l$. -/
theorem pt_pt_lies_on_iff_seg_toLine {A B : P} {l : Line P} [_h : PtNe B A] : A LiesOn l ∧ B LiesOn l ↔ (SEG_nd A B).toLine = l :=
  eq_pt_pt_line_iff_lies_on

/-- Given two distinct points $A$ and $B$ lying on a line $l$, the projective direction of the nondegenerate segment $AB$ is the same as the projective direction of the line $l$. -/
theorem toProj_eq_seg_nd_toProj_of_lies_on {A B : P} {l : Line P} (ha : A LiesOn l) (hb : B LiesOn l) [_hab : PtNe B A] : (SEG_nd A B).toProj = l.toProj := by
  rw [← eq_line_of_pt_pt_of_ne ha hb]
  rfl

end pt_pt

section pt_proj

/-- Given a point $A$ and a projective direction, $A$ lies on the line through $A$ in the direction of the projective direction. -/
theorem pt_lies_on_of_mk_pt_proj (A : P) (proj : Proj) : A LiesOn Line.mk_pt_proj A proj := by
  induction proj using Proj.ind
  exact Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mpr (.inl Ray.source_lies_on)

/-- Given a point $A$ and a direction, $A$ lies on the line through $A$ along the given direction. -/
theorem pt_lies_on_of_mk_pt_dir (A : P) (dir : Dir) : A LiesOn Line.mk_pt_dir A dir :=
  pt_lies_on_of_mk_pt_proj A dir.toProj

/-- Given a point $A$ and a nondegenerate vector, then $A$ lies on the line through $A$ in the direction of the given vector. -/
theorem pt_lies_on_of_mk_pt_vec_nd (A : P) (vec_nd : VecND) : A LiesOn Line.mk_pt_vec_nd A vec_nd :=
  pt_lies_on_of_mk_pt_proj A vec_nd.toProj

/-- Given a point $A$ and a projective direction $proj$, the projective direction of the line through $A$ and in the projective direction $proj$ is exactly $proj$. -/
theorem proj_eq_of_mk_pt_proj (A : P) (proj : Proj) : (Line.mk_pt_proj A proj).toProj = proj := by
  induction proj using Proj.ind
  rfl

/-- Given a point $A$ lying on a line $l$, the line through $A$ along the projective direction of $l$ is precisely $l$. -/
theorem mk_pt_proj_eq {A : P} {l : Line P} (h : A LiesOn l) : Line.mk_pt_proj A l.toProj = l := by
  induction' l using Line.ind with r
  exact (@Quotient.map_mk _ _ ((RayVector.Setoid ℝ Vec).correspondence ⟨projectivizationSetoid ℝ Vec, _⟩)
    same_extn_line.setoid (fun x ↦ Ray.mk A x)
      (fun _ _ h ↦ same_extn_line_of_PM A (Dir.toProj_eq_toProj_iff.mp (Quotient.sound h))) r.2).trans <|
        (@Quotient.eq _ same_extn_line.setoid _ _).mpr (same_extn_line.symm ⟨rfl, h⟩)

/-- Given a projective direction $x$ and a point $A$ on a line $l$, if $x$ is the same as the projective direction of $l$, then the line through $A$ in the direction of $x$ is equal to $l$. -/
theorem mk_pt_proj_eq_of_eq_toProj {A : P} {l : Line P} (h : A LiesOn l) {x : Proj} (hx : x = l.toProj) : Line.mk_pt_proj A x = l := by
  rw [hx]
  exact mk_pt_proj_eq h

/-- Given two lines $l_1$ and $l_2$ with the same projective direction, if there is a point $A$ that lies on both lines, then $l_1 = l_2$. -/
theorem eq_of_same_toProj_and_pt_lies_on {A : P} {l₁ l₂ : Line P} (h₁ : A LiesOn l₁) (h₂ : A LiesOn l₂) (h : l₁.toProj = l₂.toProj) : l₁ = l₂ := by
  rw [← mk_pt_proj_eq h₁, mk_pt_proj_eq_of_eq_toProj h₂ h]

/-- Given a point $A$, there exists a line through $A$. -/
theorem exist_line_pt_lies_on (A : P) : ∃ l : Line P, A LiesOn l :=
  ⟨Line.mk_pt_vec_nd A (Classical.arbitrary _), pt_lies_on_of_mk_pt_vec_nd _ _⟩

theorem exist_rep_ray_source_eq_pt {l : Line P} {A : P} (ha : A LiesOn l) : ∃ r : Ray P , r.source = A ∧ r.toLine = l := by
  rcases (Quotient.exists_rep l.toProj) with ⟨d , _⟩
  let r : Ray P := ⟨A, d⟩
  refine' ⟨r, rfl, _⟩
  calc
    _= mk_pt_proj A r.toProj := rfl
    _= mk_pt_proj A l.toProj := by congr
    _= l := mk_pt_proj_eq_of_eq_toProj ha rfl

end pt_proj

end Line

section pt_dir

namespace DirLine

/-- Given two distinct points, the directed line from $B$ to $A$ is the reverse of the directed line from $A$ to $B$. -/
theorem pt_pt_rev_eq_rev {A B : P} [_h : PtNe B A] : DLIN B A = (DLIN A B).reverse := by
  refine' (Quotient.eq (r := same_dir_line.setoid)).mpr ⟨_, .inl (Ray.snd_pt_lies_on_mk_pt_pt (B := A))⟩
  rw [Ray.toDir_of_rev_eq_neg_toDir, Ray.toDir_eq_neg_toDir_of_mk_pt_pt]

/-- For two distinct points $A$ and $B$, $A$ lies on the directed line from $A$ to $B$. -/
theorem fst_pt_lies_on_mk_pt_pt {A B : P} [_h : PtNe B A] : A LiesOn DLIN A B := .inl Ray.source_lies_on

/-- For two distinct points $A$ and $B$, the second point $B$ lies on the directed line from $A$ to $B$. -/
theorem snd_pt_lies_on_mk_pt_pt {A B : P} [_h : PtNe B A] : B LiesOn DLIN A B := Line.snd_pt_lies_on_mk_pt_pt

/-- Given two distinct points $A$ and $B$, both $A$ and $B$ lie on the directed line from $A$ to $B$. -/
theorem pt_lies_on_of_pt_pt_of_ne {A B : P} [_h : PtNe B A] : A LiesOn DLIN A B ∧ B LiesOn DLIN A B :=
  ⟨fst_pt_lies_on_mk_pt_pt, snd_pt_lies_on_mk_pt_pt⟩

/-- Given a point $A$ and a direction, the point $A$ lies on the line through $A$ in the given direction. -/
theorem pt_lies_on_of_mk_pt_dir (A : P) (dir : Dir) : A LiesOn mk_pt_dir A dir :=
  Line.pt_lies_on_of_mk_pt_dir A dir

/-- Given a point and a nondegenerate vector, $A$ lies on the directed line from $A$ in the direction of the given vector. -/
theorem pt_lies_on_of_mk_pt_vec_nd (A : P) (vec_nd : VecND) : A LiesOn mk_pt_vec_nd A vec_nd :=
  Line.pt_lies_on_of_mk_pt_vec_nd A vec_nd

/-- The direction of the directed line from a point $A$ in the direction of $dir$ is $dir$ itself. -/
theorem dir_eq_of_mk_pt_dir (A : P) (dir : Dir) : (mk_pt_dir A dir).toDir = dir := rfl

/-- Given a point $A$ lying on a directed line $l$, this theorem states that the directed line from $A$ in the direction of $l$ is the same as $l$ itself. -/
theorem mk_pt_dir_eq {A : P} {l : DirLine P} (h : A LiesOn l) : mk_pt_dir A l.toDir = l := by
  induction l using DirLine.ind
  exact Eq.symm ((Quotient.eq (r := same_dir_line.setoid)).mpr ⟨rfl, h⟩)

/-- Given a point $A$ and a directed line $l$, if $A$ lies on $l$, then the directed line from $A$ in the direction of $l$ is the same as $l$. -/
theorem mk_pt_dir_eq_of_eq_toDir {A : P} {l : DirLine P} (h : A LiesOn l) {x : Dir} (hx : x = l.toDir) : mk_pt_dir A x = l := by
  rw [hx]
  exact mk_pt_dir_eq h

/-- If two directed lines have a intersection point and the same direction,
then these two directed lines are identical. -/
theorem eq_of_same_toDir_and_pt_lies_on {A : P} {l₁ l₂ : DirLine P} (h₁ : A LiesOn l₁) (h₂ : A LiesOn l₂) (h : l₁.toDir = l₂.toDir) : l₁ = l₂ := by
  rw [← mk_pt_dir_eq h₁, mk_pt_dir_eq_of_eq_toDir h₂ h]

/-- Given two distinct points $A$ and $B$, if $A$ lies on $l$ and the direction of the nondegenerate segment $AB$ is the same as the direction of a directed line $l$, then the directed line from $A$ to $B$ is the same as $l$. -/
theorem eq_dirline_of_toDir_eq_of_pt_of_ne {A B : P} {l : DirLine P} [_h : PtNe B A] (ha : A LiesOn l) (hd : (SEG_nd A B).toDir = l.toDir) : DLIN A B = l :=
  eq_of_same_toDir_and_pt_lies_on fst_pt_lies_on_mk_pt_pt ha hd

/-- Given two distinct points $A$ and $B$ on a directed line $l$, if the direction of the nondegenerate segment $AB$ is not the same as the direction of $l$, then the directed line from $B$ to $A$ is $l$. -/
theorem eq_dirline_rev_of_toDir_ne_of_pt_pt_of_ne {A B : P} {l : DirLine P} [_h : PtNe B A] (ha : A LiesOn l) (hb : B LiesOn l) (hd : (SEG_nd A B).toDir ≠ l.toDir) : DLIN B A = l := by
  refine' (Eq.trans _ pt_pt_rev_eq_rev.symm).symm
  exact (eq_rev_of_toDir_ne_of_toLine_eq (Line.eq_line_of_pt_pt_of_ne ha hb).symm hd.symm)

/-- If $A$ and $B$ are two distinct points that both lie on the same directed line $l$, then $l$ is either the directed line from $A$ to $B$ or the directed line from $B$ to $A$. -/
theorem eq_dirline_or_rev_of_pt_pt_of_ne {A B : P} {l : DirLine P} [_h : PtNe B A] (ha : A LiesOn l) (hb : B LiesOn l) : DLIN A B = l ∨ DLIN B A = l :=
  if hd : (SEG_nd A B).toDir = l.toDir then (.inl (eq_dirline_of_toDir_eq_of_pt_of_ne ha hd))
  else (.inr (eq_dirline_rev_of_toDir_ne_of_pt_pt_of_ne ha hb hd))

/-- Given two distinct points $A$ and $B$ and two directed line $l_1$ and $l_2$, assume that both $A$ and $B$ lie on $l_1$ and both $A$ and $B$ lie on $l_2$, then either $l_1$ is equal to $l_2$ or $l_1$ is equal to the reverse of $l_2$. -/
theorem eq_dirline_or_rev_of_pt_pt_lies_on_of_ne {A B : P} [_h : PtNe B A] {l₁ l₂ : DirLine P} (hA₁ : A LiesOn l₁) (hB₁ : B LiesOn l₁) (hA₂ : A LiesOn l₂) (hB₂ : B LiesOn l₂) : l₁ = l₂ ∨ l₁ = l₂.reverse :=
  eq_or_eq_rev_of_toLine_eq (Line.eq_of_pt_pt_lies_on_of_ne hA₁ hB₁ hA₂ hB₂)

/-- If $A$ and $B$ are two distinct points that both lie on a directed line $l$, then the projective direction of the nondegenerate segment $AB$ is the same as the projective direction of $l$. -/
theorem toProj_eq_seg_nd_toProj_of_lies_on {A B : P} {l : DirLine P} (ha : A LiesOn l) (hb : B LiesOn l) [_h : PtNe B A] : (SEG_nd A B).toProj = l.toProj :=
  (Line.toProj_eq_seg_nd_toProj_of_lies_on ha hb).trans l.toLine_toProj_eq_toProj

/-- Given a point $A$, there exists a directed line $l$ such that $A$ lies on $l$. -/
theorem exist_dirline_pt_lies_on (A : P) : ∃ l : DirLine P, A LiesOn l := by
  rcases Line.exist_line_pt_lies_on A with ⟨⟨r⟩, h⟩
  exact ⟨r.toDirLine, h⟩

end DirLine

end pt_dir



open Line DirLine

section coercion


/-- The line associated with a ray is the same as the line associated with its reverse. -/
theorem Ray.toLine_eq_rev_toLine {r : Ray P} : r.toLine = r.reverse.toLine :=
  (Quotient.eq (r := same_extn_line.setoid)).mpr same_extn_line.ray_rev_of_same_extn_line

/-- The line associated to a nondegenerate segment is the same as the line associated to its extension ray. -/
theorem SegND.toLine_eq_toRay_toLine {s : SegND P} : s.toRay.toLine = s.toLine := rfl

/-- The line associated to a nondegenerate segment is the same as the line associated to its reverse. -/
theorem SegND.toLine_eq_rev_toLine {s : SegND P} : s.toLine = s.reverse.toLine :=
  line_of_pt_pt_eq_rev (_h := ⟨s.2⟩)

/-- For a nondegenerate segment $s$, the line associated to $s$ is the same as the line associated to the ray of $s$. -/
theorem SegND.toLine_eq_extn_toLine {s : SegND P} : s.toLine = s.extension.toLine :=
  (Quotient.eq (r := same_extn_line.setoid)).mpr ⟨ SegND.extn_toProj.symm,
  .inl (SegND.lies_on_toRay_of_lies_on Seg.target_lies_on)⟩

/-- For two distinct points $A$ and $B$, the line associated to the ray from $A$ to $B$ is the same as the line through $A$ and $B$. -/
theorem ray_of_pt_pt_toLine_eq_line_of_pt_pt {A B : P} [_h : PtNe B A] : (RAY A B).toLine = LIN A B :=
  rfl

/-- The line associated to the nondegenerate segment $AB$ is the same as the line through $A$ and $B$. -/
theorem seg_nd_of_pt_pt_toLine_eq_line_of_pt_pt {A B : P} [_h : PtNe B A] : (SEG_nd A B).toLine = LIN A B :=
  rfl

/-- The reverse of the directed line associated to a ray is the directed line associated to the reverse of the ray. -/
theorem Ray.toDirLine_rev_eq_rev_toLine {r : Ray P} : r.toDirLine.reverse = r.reverse.toDirLine :=
  (Quotient.eq (r := same_dir_line.setoid)).mpr ⟨rfl, .inl r.source_lies_on_rev⟩

/-- The directed line associated with a nondegenerate segment is the same as the directed line associated with the ray of the segment. -/
theorem SegND.toDirLine_eq_toRay_toDirLine {s : SegND P} : s.toRay.toDirLine = s.toDirLine := rfl

/-- The reverse of the directed line associated to a nondegenerate segment is the directed line associated to the reverse of the segment. -/
theorem SegND.toDirLine_rev_eq_rev_toDirLine {s : SegND P} : s.toDirLine.reverse = s.reverse.toDirLine :=
  (eq_dirline_of_toDir_eq_of_pt_of_ne (_h := ⟨s.2.symm⟩)
    (DirLine.lies_on_rev_iff_lies_on.mpr target_lies_on_toDirLine)
      ((s.toDir_of_rev_eq_neg_toDir).trans s.toDirLine.rev_toDir_eq_neg_toDir)).symm

/-- The directed line associated with a nondegenerate segment is the same as the directed line associated with its extension. -/
theorem SegND.toDirLine_eq_extn_toDirLine {s : SegND P} : s.toDirLine = s.extension.toDirLine :=
  (Quotient.eq (r := same_dir_line.setoid)).mpr
    ⟨s.extn_toDir, .inl (s.lies_on_toRay_of_lies_on s.1.target_lies_on)⟩

/-- Let $A$ and $B$ be two distinct points, then the directed line from $A$ to $B$ is the same as the directed line associated to the ray $\overrightarrow{AB}$. -/
theorem ray_of_pt_pt_toDirLine_eq_dirline_of_pt_pt {A B : P} [_h : PtNe B A] : (RAY A B).toDirLine = DLIN A B :=
  rfl

/-- Given two distinct points $A$ and $B$, the directed line from $A$ to $B$ is the same as the directed line associated to the nondegenerate segment $AB$. -/
theorem seg_nd_of_pt_pt_toDirLine_eq_dirline_of_pt_pt {A B : P} [_h : PtNe B A] : (SEG_nd A B).toDirLine = DLIN A B :=
  rfl

end coercion

section lieson

/-- The underlying set of a ray is a subset of the underlying set of the line associated to the ray. -/
theorem Ray.subset_toLine {r : Ray P} : r.carrier ⊆ r.toLine.carrier := by
  rw [toLine_carrier_eq_ray_carrier_union_rev_carrier]
  exact Set.subset_union_left r.carrier r.reverse.carrier

/-- The underlying set of a ray is a subset of the underlying set of the line associated to the ray. -/
theorem ray_subset_line {r : Ray P} {l : Line P} (h : r.toLine = l) : r.carrier ⊆ l.carrier := by
  rw [← h]
  exact r.subset_toLine

/-- Given a point $A$ lying on a nondegenerate segment $s$, the point $A$ also lies on the line associated to $s$. -/
theorem seg_lies_on_line {s : SegND P} {A : P} (h : A LiesOn s) : A LiesOn s.toLine :=
  Set.mem_of_subset_of_mem (ray_subset_line rfl) (SegND.lies_on_toRay_of_lies_on h)

/-- The underlying set of a nondegenerate segment $s$ is a subset of the underlying set of the line associated to $s$. -/
theorem SegND.subset_toLine {s : SegND P} : s.carrier ⊆ s.toLine.carrier := fun _ ↦ seg_lies_on_line

/-- The underlying set of a nondegenerate segment is a subset of the underlying set of the line associated to the segment. -/
theorem seg_subset_line {s : SegND P} {l : Line P} (h : s.toLine = l) : s.carrier ⊆ l.carrier := by
  rw [← h]
  exact s.subset_toLine

/-- The theorem states that for any line $l$, there exist two distinct points $A$ and $B$ such that $A$ and $B$ both lie on the line $l$. -/
theorem Line.nontriv (l : Line P) : ∃ (A B : P), A LiesOn l ∧ B LiesOn l ∧ (B ≠ A) := by
  let ⟨r, h⟩ := l.exists_rep
  rcases r.nontriv with ⟨A, B, g⟩
  exact ⟨A, B, ⟨ray_subset_line h g.1, ray_subset_line h g.2.1, g.2.2⟩⟩

/-- The theorem states that, for a point $A$ and a ray $r$, `REMOVE THIS THEOREM!!!!` a point A lies on a ray r and A is not the source of r, or A lies on the reverse of r and A is not the source of r, or A is the source of r if and only if A lies on r or A lies on the reverse of r. -/
theorem Ray.lies_on_ray_or_lies_on_ray_rev_iff {r : Ray P} {A : P} : A LiesOn r ∧ A ≠ r.source ∨ A LiesOn r.reverse ∧ A ≠ r.source ∨ A = r.source ↔ A LiesOn r ∨ A LiesOn r.reverse := ⟨
  fun | .inl h => .inl h.1
      | .inr h => .casesOn h (fun h => .inr h.1) (fun h => .inr (by rw[h]; exact source_lies_on)),
  fun | .inl h => if g : A = r.source then .inr (.inr g) else .inl ⟨h, g⟩
      | .inr h => if g : A = r.source then .inr (.inr g) else .inr (.inl ⟨h, g⟩)⟩

/-- Given a point and a ray $r$, $A$ lies on the line associated to $r$ if and only if $A$ lies either in the interior of $r$ or the interior of the reverse of $r$ or $A$ is the source of $r$. -/
theorem Ray.lies_on_toLine_iff_lies_int_or_lies_int_rev_or_eq_source {A : P} {r : Ray P} : (A LiesOn r.toLine) ↔ (A LiesInt r) ∨ (A LiesInt r.reverse) ∨ (A = r.source) := by
  rw [lies_int_def, lies_int_def, source_of_rev_eq_source, lies_on_ray_or_lies_on_ray_rev_iff, lies_on_toLine_iff_lies_on_or_lies_on_rev]

/-- If a point $A$ does not lie in the interior of a nondegenerate segment, then $A$ lies on the line of the segment if and only if it lies on the extension ray of the segment or it lies on the extension ray of the reverse of the segment. -/
theorem SegND.lies_on_extn_or_rev_extn_iff_lies_on_toLine_of_not_lies_on {A : P} {seg_nd : SegND P} (h : ¬ A LiesInt seg_nd.1) : A LiesOn seg_nd.toLine ↔ (A LiesOn seg_nd.extension) ∨ (A LiesOn seg_nd.reverse.extension) := by
  sorry
  /-
  constructor
  · intro hh
    rcases (seg_nd.toRay.lies_on_toline_iff_lies_on_or_lies_on_rev).mp hh with h₁ | h₂
    · by_cases ax : A = seg_nd.1.source
      · rw [ax]
        exact .inr Ray.source_lies_on
      by_cases ay : A = seg_nd.1.target
      · rw [ay]
        exact .inl Ray.source_lies_on
      exact .casesOn (lies_on_seg_nd_or_extension_of_lies_on_toRay h₁)
        (fun h₁ ↦ (h ⟨h₁, ax, ay⟩).elim) (fun h₁ ↦ .inl h₁)
    rw [rev_extn_eq_toRay_rev]
    exact .inr h₂
  · exact fun hh ↦ .casesOn hh
      (fun h₁ ↦ Eq.mpr (seg_nd.toline_eq_extn_toline ▸ Eq.refl (A LiesOn seg_nd.toLine))
        ((seg_nd.extension.lies_on_toline_iff_lies_on_or_lies_on_rev).mpr (.inl h₁)))
      (fun h₂ ↦ (seg_nd.toRay.lies_on_toline_iff_lies_on_or_lies_on_rev).mpr <| .inr <| by
        rw [← rev_extn_eq_toRay_rev]
        exact h₂)
 -/

/-- Given a point $X$ and a nondegenerate segment $seg_nd$, if $X$ lies on the extension ray of $seg_nd$, then $X$ lies on the line associated with $seg_nd$. -/
theorem SegND.lies_on_toLine_of_lies_on_extn {X : P} {seg_nd : SegND P} (lieson : X LiesOn seg_nd.extension) : X LiesOn seg_nd.toLine := by
  rw [SegND.toLine_eq_rev_toLine]
  rw [extn_eq_rev_toRay_rev] at lieson
  exact Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mpr (.inr lieson)

/-- Two lines are equal iff they have the same underlying sets. -/
theorem lies_on_iff_lies_on_iff_line_eq_line (l₁ l₂ : Line P) : (∀ A : P, A LiesOn l₁ ↔ A LiesOn l₂) ↔ l₁ = l₂ := by
  constructor
  · induction' l₁ using Line.ind with r
    induction l₂ using Line.ind
    intro h
    rcases r.toLine.nontriv with ⟨X, Y, Xrl₁, Yrl₁, neq⟩
    exact eq_of_pt_pt_lies_on_of_ne (_h := ⟨neq⟩) Xrl₁ Yrl₁ ((h X).mp Xrl₁) ((h Y).mp Yrl₁)
  · exact fun h A ↦ Iff.of_eq (congrArg (lies_on A) h)

/-- If $A$ and $B$ are two distinct points and $A$ lies on a line $l$, the point $B$ lies on the line $l$ if and only if the projective direction of the nondegenerate segment $AB$ is the same as the projective direction of $l$. -/
theorem Line.lies_on_iff_eq_toProj_of_lies_on {A B : P} {l : Line P} [_h : PtNe B A] (hA : A LiesOn l) : B LiesOn l ↔ (SEG_nd A B).toProj = l.toProj := by
  refine' ⟨fun hB ↦ toProj_eq_seg_nd_toProj_of_lies_on hA hB, fun eq ↦ _⟩
  rw [← eq_of_same_toProj_and_pt_lies_on (SegND.lies_on_toLine_of_lie_on (@Seg.source_lies_on _ _ (SEG_nd A B).1)) hA eq]
  exact SegND.lies_on_toLine_of_lie_on Seg.target_lies_on

/-- Let $A$ be a point and $B$ a point that lies on the line through $A$ in a given direction $dir$. Then there exists a real number $t$ such that the vector $\xrightarrow{AB}$ is $t$ times the unit vector of the direction $dir$. -/
theorem Line.exist_real_vec_eq_smul_of_lies_on {A B : P} {dir : Dir} (h : B LiesOn (mk_pt_dir A dir)) : ∃ t : ℝ, VEC A B = t • dir.unitVec :=
  lies_on_or_rev_iff_exist_real_vec_eq_smul.mp h

/-- If $A$ is a point and $v$ a nondegenerate vector and if a point $B$ lies on the line through $A$ in the direction of $v$, then there exists a real number $t$ such that the vector $AB$ is $t$ times the vector $v$, i.e. $\overrightarrow{AB} = t \cdot v$. -/
theorem Line.exist_real_vec_eq_smul_vec_of_lies_on {A B : P} {v : VecND} (hb : B LiesOn (mk_pt_vec_nd A v)) : ∃ t : ℝ, VEC A B = t • v.1 :=
  if h : VEC A B = 0 then ⟨0, h.trans (zero_smul ℝ v.1).symm⟩
  else VecND.toProj_eq_toProj_iff.mp <|
    toProj_eq_seg_nd_toProj_of_lies_on (pt_lies_on_of_mk_pt_vec_nd A v) hb (_hab := ⟨vsub_ne_zero.mp h⟩)

/-- Given a point $C$ lying on the line through distinct points $A$ and $B$, there exists a real number $t$ such that the vector $\overrightarrow{AC}$ is $t$ times the vector $\overrightarrow{AB}$. -/
theorem Line.exist_real_of_lies_on_of_pt_pt {A B C : P} [_h : PtNe B A] (hc : C LiesOn (LIN A B)) : ∃ t : ℝ, VEC A C = t • VEC A B :=
  @exist_real_vec_eq_smul_vec_of_lies_on P _ A C (SEG_nd A B).toVecND hc

/-- For two points $A$ and $B$ and a direction vector $dir$,  there exists a real number $t$ such that the vector $\overrightarrow{AB}$ is t times $dir$, then $B$ lies on the directed line from $A$ in the direction of $dir$. -/
theorem Line.lies_on_of_exist_real_vec_eq_smul {A B : P} {dir : Dir} {t : ℝ} (h : VEC A B = t • dir.unitVec) : B LiesOn (mk_pt_dir A dir) :=
  (@pt_lies_on_line_from_ray_iff_vec_parallel P _ B ⟨A, dir⟩).mpr ⟨t, h⟩

/-- For two points $A$ and $B$ and a nondegenerate vector $v$,  there exists a real number $t$ such that the vector $\overrightarrow{AB}$ is t times $v$, then $B$ lies on the directed line from $A$ in the direction of $v$. -/
theorem Line.lies_on_of_exist_real_vec_eq_smul_vec {A B : P} {v : VecND} {t : ℝ} (h : VEC A B = t • v.1) : B LiesOn (mk_pt_vec_nd A v) :=
  have h' : VEC A B = (t * ‖v‖) • v.toDir.unitVec := by
    simp only [h]
    rw [mul_smul, VecND.norm_smul_toDir_unitVec]
  lies_on_of_exist_real_vec_eq_smul h'

/-- Given points $A$, $B$, and $C$ with $A \neq B$, if there exists a real number t such that the vector $\overrightarrow {AC}$ is $t$ times the vector $\overrightarrow {AB}$, then $C$ lies on the line through $A$ and $B$. -/
theorem Line.lies_on_of_exist_real_of_pt_pt {A B C : P} [_h : PtNe B A] {t : ℝ} (ht : VEC A C = t • VEC A B) : C LiesOn (LIN A B) :=
  @lies_on_of_exist_real_vec_eq_smul_vec P _ A C (SEG_nd A B).toVecND t ht

/-- The theorem states that the set of points on a ray is a subset of the set of points on the directed line associated with the ray. -/
theorem Ray.subset_toDirLine {r : Ray P} : r.carrier ⊆ r.toDirLine.carrier := r.subset_toLine

/-- If a line $l$ is the directed line associated to a ray $r$, then the underlying set of $r$ is the subset of the underlying set of $l$. -/
theorem ray_subset_dirline {r : Ray P} {l : DirLine P} (h : r.toDirLine = l) : r.carrier ⊆ l.carrier :=
  ray_subset_line (congrArg DirLine.toLine h)

/-- A point $A$ lying on a nondegenerate segment $s$ also lies on the directed line associated to $s$. -/
theorem seg_lies_on_dirline {s : SegND P} {A : P} (h : A LiesOn s.1) : A LiesOn s.toDirLine :=
  seg_lies_on_line h

/-- The underlying set of a nondegenerate segment $s$ is a subset of the underlying set of the line associated to $s$. -/
theorem SegND.subset_toDirLine {s : SegND P} : s.carrier ⊆ s.toDirLine.carrier := s.subset_toLine

/-- If a directed line $l$ is the directed line associated to a nondegenerate segment $s$, then the underlying set of $s$ is a subset of the underlying set of $l$. -/
theorem seg_subset_dirline {s : SegND P} {l : DirLine P} (h : s.toDirLine = l) : s.carrier ⊆ l.carrier :=
  seg_subset_line (congrArg DirLine.toLine h)

/-- On any directed line $l$, there exist two distinct points $A$ and $B$ on $l$. -/
theorem DirLine.nontriv (l : DirLine P) : ∃ (A B : P), A LiesOn l ∧ B LiesOn l ∧ (B ≠ A) :=
  l.toLine.nontriv

/-- A point lies on a directed line associated to a ray $r$ if and only if it lies in the interior of $r$ or the interior of the reverse ray or $r$, or it is the source of $r$. -/
theorem Ray.lies_on_toDirLine_iff_lies_int_or_lies_int_rev_or_eq_source {A : P} {r : Ray P} : (A LiesOn r.toDirLine) ↔ (A LiesInt r) ∨ (A LiesInt r.reverse) ∨ (A = r.source) :=
  r.lies_on_toLine_iff_lies_int_or_lies_int_rev_or_eq_source

/-- If a point $A$ does not lie in hte interior of a nondegenerate segement $seg_nd$, then it lies on the line associaeted to $seg_nd$ if and only if it lies on the extension ray of $seg_nd$ or it lies on the extension ray of the reverse of $seg_nd$. -/
theorem SegND.lies_on_extn_or_rev_extn_iff_lies_on_toDirLine_of_not_lies_on {A : P} {seg_nd : SegND P} (h : ¬ A LiesInt seg_nd.1) : A LiesOn seg_nd.toDirLine ↔ (A LiesOn seg_nd.extension) ∨ (A LiesOn seg_nd.reverse.extension) :=
  SegND.lies_on_extn_or_rev_extn_iff_lies_on_toLine_of_not_lies_on h

/-- This theorem states that if a point $X$ lies on the extension ray of a nondegenerate segment seg_nd, then X also lies on the directed line associated to seg_nd. -/
theorem SegND.lies_on_toDirLine_of_lies_on_extn {X : P} {seg_nd : SegND P} (h : X LiesOn seg_nd.extension) : X LiesOn seg_nd.toDirLine :=
  SegND.lies_on_toLine_of_lies_on_extn h

/-- For two directed lines $l_1$ and $l_2$, they have the same associated line if and only if for any point $A$, it lies on $l_1$ if and only if it lies on $l_2$. -/
theorem DirLine.lies_on_iff_lies_on_iff_toLine_eq_toLine (l₁ l₂ : DirLine P) : (∀ A : P, A LiesOn l₁ ↔ A LiesOn l₂) ↔ l₁.toLine = l₂.toLine :=
  lies_on_iff_lies_on_iff_line_eq_line l₁.toLine l₂.toLine

/-- Given two distinct points $A$ and $B$ and a directed line $l$, assume that $A$ lies on $l$, then $B$ lies on $l$ if and only if the projective direction of $l$ is the same as the projective direction of the segment $AB$. -/
theorem DirLine.lies_on_iff_eq_toProj_of_lies_on {A B : P} {l : DirLine P} [_h : PtNe B A] (hA : A LiesOn l) : B LiesOn l ↔ (SEG_nd A B).toProj = l.toProj :=
  (Line.lies_on_iff_eq_toProj_of_lies_on hA).trans (Eq.congr rfl l.toLine_toProj_eq_toProj)

/-- Given a point $A$ and a direcction $dir$, if $B$ is a point that lies on the directed line through $A$ in the direction of $dir$, there exists a real number $t$ such that the vector $\overrightarrow{AB}$ is $t$ times the unit vector of the direction $dir$. -/
theorem DirLine.exist_real_vec_eq_smul_of_lies_on {A B : P} {dir : Dir} (h : B LiesOn (mk_pt_dir A dir)) : ∃ t : ℝ, VEC A B = t • dir.unitVec :=
  lies_on_or_rev_iff_exist_real_vec_eq_smul.mp h

/-- If a point $B$ lies on the directed line through $A$ in the direction of a nondegenerate vector $v$, then the vector $\overrightarrow{AB}$ is some real multiple of $v$. -/
theorem DirLine.exist_real_vec_eq_smul_vec_of_lies_on {A B : P} {v : VecND} (h : B LiesOn (mk_pt_vec_nd A v)) : ∃ t : ℝ, VEC A B = t • v.1 :=
  Line.exist_real_vec_eq_smul_vec_of_lies_on h

/-- Let $A$ and $B$ be two distinct points and $C$ a point that lies on the directed line from $A$ to $B$. Then there exists some real number $t$ such that $\xrightarrow{AC}$ is $t$ times $\xrightarrow{AB}$. -/
theorem DirLine.exist_real_of_lies_on_of_pt_pt {A B C : P} [_h : PtNe B A] (hc : C LiesOn (DLIN A B)) : ∃ t : ℝ, VEC A C = t • VEC A B :=
  Line.exist_real_of_lies_on_of_pt_pt hc

/-- Given two points $A$ and $B$ on a directed line $l$, there exists a real number $t$ such that the vector $\xrightarrow{AB}$ is $t$ times the unit direction vector of $l$. -/
theorem DirLine.exist_real_vec_eq_smul_toDir_of_lies_on {A B : P} {l : DirLine P} (ha : A LiesOn l) (hb : B LiesOn l) : ∃ t : ℝ, VEC A B = t • l.toDir.unitVec := by
  rw [← mk_pt_dir_eq ha]
  rw [← mk_pt_dir_eq ha] at hb
  exact exist_real_vec_eq_smul_of_lies_on hb

/-- Given two points $A$ and $B$ and a direction $dir$, if there exists a real number $t$ such that the vector $\overrightarrow{AB}$ is $t$ times the unit vector of the direction dir, then $B$ lies on the directed line from $A$ in the direction of $dir$. -/
theorem DirLine.lies_on_of_exist_real_vec_eq_smul {A B : P} {dir : Dir} {t : ℝ} (h : VEC A B = t • dir.unitVec) : B LiesOn (mk_pt_dir A dir) :=
  Line.lies_on_of_exist_real_vec_eq_smul h

/-- If the vector from a point $A$ to a point $B$ is a scalar multiple of a nondegenerate vector $v$, then $B$ lies on the directed line through $A$ in the direction of $v$. -/
theorem DirLine.lies_on_of_exist_real_vec_eq_smul_vec {A B : P} {v : VecND} {t : ℝ} (h : VEC A B = t • v.1) : B LiesOn (mk_pt_vec_nd A v):=
  Line.lies_on_of_exist_real_vec_eq_smul_vec h

/-- Given points $A$, $B$, and $C$, if $B$ and $A$ are distinct, and the vector $\overrightarrow {AC}$ is a real multiple of the vector $\overrightarrow{AB}$, then $C$ lies on the directed line from $A$ to $B$. -/
theorem DirLine.lies_on_of_exist_real_of_pt_pt {A B C : P} [_h : PtNe B A] {t : ℝ} (ht : VEC A C = t • VEC A B) : C LiesOn (DLIN A B) :=
  Line.lies_on_of_exist_real_of_pt_pt ht

/-- Given a point $A$ on a directed line $l$, if for some point $B$ the vector $\overrightarrow{AB}$ is a real multiple of the unit direct vector of $l$, then $B$ lies on $l$. -/
theorem DirLine.lies_on_of_exist_real_vec_eq_smul_toDir {A B : P} {l : DirLine P} (ha : A LiesOn l) {t : ℝ} (ht : VEC A B = t • l.toDir.unitVec) : B LiesOn l := by
  rw [← mk_pt_dir_eq ha]
  exact lies_on_of_exist_real_vec_eq_smul ht

theorem Ray.eq_toDirLine_of_lies_int {A : P} {r : Ray P} (h : A LiesInt r) : DLIN r.source A h.ne_source = r.toDirLine := sorry -- use `RAY r.source A = r` to prove it

theorem Ray.eq_toLine_of_lies_int {A : P} {r : Ray P} (h : A LiesInt r) : LIN r.source A h.ne_source = r.toLine := sorry

theorem SegND.dirLine_source_pt_eq_toDirLine_of_lies_int {A : P} {s : SegND P} (h : A LiesInt s) : DLIN s.source A h.ne_source = s.toDirLine := sorry

theorem SegND.line_source_pt_eq_toLine_of_lies_int {A : P} {s : SegND P} (h : A LiesInt s) : LIN s.source A h.ne_source = s.toLine := sorry

theorem SegND.dirLine_pt_target_eq_toDirLine_of_lies_int {A : P} {s : SegND P} (h : A LiesInt s) : DLIN A s.target h.ne_target.symm = s.toDirLine := sorry

theorem SegND.line_pt_target_eq_toLine_of_lies_int {A : P} {s : SegND P} (h : A LiesInt s) : LIN A s.target h.ne_target.symm = s.toLine := sorry

theorem SegND.dirLine_source_midpt_eq_toDirLine {s : SegND P} : DLIN s.source s.midpoint s.midpt_ne_source = s.toDirLine := sorry

theorem SegND.line_source_midpt_eq_toLine {s : SegND P} : LIN s.source s.midpoint s.midpt_ne_source = s.toLine := sorry

theorem SegND.dirLine_midpt_target_eq_toDirLine {s : SegND P} : DLIN s.midpoint s.target (s.midpt_ne_target).symm = s.toDirLine := sorry

theorem SegND.line_midpt_target_eq_toLine {s : SegND P} : LIN s.midpoint s.target (s.midpt_ne_target).symm = s.toLine := sorry

theorem eq_or_vec_eq_of_dist_eq_of_lies_on_line_pt_pt {A B C : P} [hne : PtNe B A] (h : C LiesOn (LIN A B)) (heq : dist A C = dist A B) : (C = B) ∨ (VEC A C = VEC B A) := by
  rcases Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mp h with h | h
  · left
    apply (eq_iff_vec_eq_zero _ _).mpr
    have : VEC A C = (dist A C) • (RAY A B).2.unitVec := Ray.vec_eq_dist_smul_toDir_of_lies_on h
    calc
      _ = VEC A C - VEC A B := by rw [vec_sub_vec]
      _ = (dist A B) • (RAY A B).2.unitVec - VEC A B := by rw [this, heq]
      _ = (dist A B) • (RAY A B).2.unitVec - ‖VEC_nd A B‖ • (VEC_nd A B).toDir.unitVec := by
        simp only [Ray.mkPtPt_toDir, VecND.norm_smul_toDir_unitVec, ne_eq, VecND.coe_mkPtPt]
      _ = (dist A B) • (RAY A B).2.unitVec - ‖VEC_nd A B‖ • (RAY A B).2.unitVec := rfl
      _ = 0 := by
        rw [← sub_smul, dist_comm, NormedAddTorsor.dist_eq_norm']
        simp only [Ray.mkPtPt_toDir, smul_eq_zero, VecND.ne_zero, or_false]
        exact sub_eq_zero.mpr rfl
  right
  calc
    _ = (dist A C) • (RAY A B).reverse.2.unitVec := Ray.vec_eq_dist_smul_toDir_of_lies_on h
    _ = (dist A C) • (- (VEC_nd A B).toDir.unitVec) := by
      simp only [Ray.reverse_toDir, Ray.mkPtPt_toDir, Dir.neg_unitVec, smul_neg]
    _ = (dist A B) • (- (VEC_nd A B).toDir.unitVec) := by rw [heq]
    _ = - (‖VEC_nd A B‖ • (VEC_nd A B).toDir.unitVec) := by
      rw [smul_neg, dist_comm, NormedAddTorsor.dist_eq_norm']
      rfl
    _ = - (VEC_nd A B).1 := by
      simp only [VecND.norm_smul_toDir_unitVec, ne_eq, VecND.coe_mkPtPt, neg_vec]
    _ = - VEC A B := rfl
    _ = VEC B A := by rw [neg_vec]

theorem vec_eq_dist_eq_of_lies_on_line_pt_pt_of_ptNe {A B C : P} [_hne₁ : PtNe B A] [_hne₂ : PtNe C B] (h : C LiesOn (LIN A B)) (heq : dist A C = dist A B) : VEC B A = VEC A C :=
  (eq_or_vec_eq_of_dist_eq_of_lies_on_line_pt_pt h heq).casesOn
    (fun eq ↦ (_hne₂.out eq).elim) (fun hh ↦ hh.symm)

theorem SegND.dist_midpt_le_iff_lies_on_of_lies_on_toLine {A : P} {s : SegND P} (h : A LiesOn s.toLine) : dist A s.midpoint < dist s.source s.midpoint ↔ A LiesInt s := sorry

theorem SegND.dist_midpt_lt_iff_lies_int_of_lies_on_toLine {A : P} {s : SegND P} (h : A LiesOn s.toLine) : dist A s.midpoint < dist s.source s.midpoint ↔ A LiesInt s := sorry

theorem SegND.dist_midpt_eq_iff_eq_source_or_eq_target_of_lies_on_toLine {A : P} {s : SegND P} (h : A LiesOn s.toLine) : dist A s.midpoint = dist s.source s.midpoint ↔ A = s.source ∨ A = s.target := by
  haveI : PtNe s.midpoint s.source := ⟨s.midpt_ne_source⟩
  constructor
  · intro hh
    rw [dist_comm, ← Seg.length_eq_dist, dist_comm, Seg.length_eq_dist] at hh
    have : A LiesOn (LIN s.midpoint s.source) := by sorry
    rcases eq_or_vec_eq_of_dist_eq_of_lies_on_line_pt_pt this hh with h₁ | h₂
    · exact .inl h₁
    right
    apply (eq_iff_vec_eq_zero _ _).mpr
    calc
      _ = VEC s.midpoint A - VEC s.midpoint s.target := by rw [vec_sub_vec]
      _ = VEC s.source s.midpoint - VEC s.midpoint s.target := by rw [h₂]
      _ = 0 := by rw [s.vec_midpt_eq, sub_self]
  intro hh
  rcases hh with hh | hh
  · rw [hh]
  rw [hh, dist_comm, ← Seg.length_eq_dist, ← Seg.length_eq_dist]
  exact (s.1.dist_target_eq_dist_source_of_midpt).symm

theorem SegND.dist_midpt_gt_iff_not_lies_on_of_lies_on_toLine {A : P} {s : SegND P} (h : A LiesOn s.toLine) : dist s.source s.midpoint < dist A s.midpoint ↔ ¬ (A LiesOn s) := by
  apply Iff.not_right
  push_neg
  apply Iff.trans le_iff_lt_or_eq
  constructor
  · intro heq
    rcases heq with heq | heq
    · exact ((s.dist_midpt_lt_iff_lies_int_of_lies_on_toLine h).mp heq).1
    rcases (SegND.dist_midpt_eq_iff_eq_source_or_eq_target_of_lies_on_toLine h).mp heq with heq | heq
    · rw [heq]
      exact s.source_lies_on
    rw [heq]
    exact s.target_lies_on
  intro hh
  by_cases hh' : A LiesInt s
  · exact .inl ((SegND.dist_midpt_lt_iff_lies_int_of_lies_on_toLine h).mpr hh')
  right
  apply (SegND.dist_midpt_eq_iff_eq_source_or_eq_target_of_lies_on_toLine h).mpr
  contrapose! hh'
  exact ⟨hh, hh'.1, hh'.2⟩

theorem lies_int_seg_nd_iff_lies_on_ray_reverse {A B C : P} [hne₁ : PtNe B C] [hne₂ : PtNe A B] (h : A LiesOn (LIN B C)) : A LiesInt (SEG B C) ↔ C LiesOn (RAY A B).reverse := sorry

theorem not_lies_on_seg_nd_iff_lies_on_ray {A B C : P} [hne₁ : PtNe B C] [hne₂ : PtNe A B] (h : A LiesOn (LIN B C)) : ¬ (A LiesOn (SEG B C)) ↔ C LiesOn (RAY A B) := sorry

end lieson



section collinear

namespace Line

/-- Given three points $A$, $B$ and $C$, if $A$ and $B$ are distinct and $C$ lies on the line $AB$, then $A$, $B$, and $C$ are collinear. -/
theorem pt_pt_linear {A B C : P} [_h : PtNe B A] (hc : C LiesOn (LIN A B)) : collinear A B C :=
  if hcb : C = B then collinear_of_trd_eq_snd A hcb
  else if hac : A = C then collinear_of_fst_eq_snd B hac
  else haveI : PtNe C B := ⟨hcb⟩
  perm_collinear_trd_fst_snd <| (dite_prop_iff_or _).mpr <| .inr ⟨by push_neg; exact ⟨hac, Fact.out, hcb⟩,
    ((lies_on_iff_eq_toProj_of_lies_on snd_pt_lies_on_mk_pt_pt).mp hc).trans <|
      congrArg toProj line_of_pt_pt_eq_rev⟩

/-- The theorem states that if three points $A$, $B$, and $C$ lie on the same line $l$, then they are collinear. -/
theorem linear {l : Line P} {A B C : P} (h₁ : A LiesOn l) (h₂ : B LiesOn l) (h₃ : C LiesOn l) : collinear A B C := by
  if h : B = A then exact collinear_of_snd_eq_fst C h
  else
  haveI : PtNe B A := ⟨h⟩
  refine' pt_pt_linear _
  rw [eq_line_of_pt_pt_of_ne h₁ h₂]
  exact h₃

/-- If $A$ and $B$ are two distinct points and $C$ is a point such that $A$, $B$ and $C$ are collinear, then $C$ lies on the line $AB$. -/
theorem pt_pt_maximal {A B C : P} [_h : PtNe B A] (Co : collinear A B C) : C LiesOn (LIN A B) :=
  if hcb : C = B then by
    rw [hcb]
    exact snd_pt_lies_on_mk_pt_pt
  else haveI : PtNe C B := ⟨hcb⟩
  (lies_on_iff_eq_toProj_of_lies_on snd_pt_lies_on_mk_pt_pt).mpr <|
    (collinear_iff_toProj_eq_of_ptNe.mp (perm_collinear_snd_trd_fst Co)).trans <|
      congrArg Line.toProj (line_of_pt_pt_eq_rev (_h := _h)).symm

/-- Given two distinct points $A$ and $B$ on a line $l$, if a point $C$ is so that $A$, $B$, and $C$ are collinear, then $C$ lines on $l$. -/
theorem maximal {l : Line P} {A B C : P} (h₁ : A LiesOn l) (h₂ : B LiesOn l) [_h : PtNe B A] (Co : collinear A B C) : C LiesOn l := by
  rw [← eq_line_of_pt_pt_of_ne h₁ h₂]
  exact pt_pt_maximal Co

/-- Given two distinct points $A$ and $B$, a point $X$ lies on the line through $A$ and $B$ if and only if $A$, $B$, and $X$ are collinear. -/
theorem lies_on_line_of_pt_pt_iff_collinear {A B : P} [_h : PtNe B A] (X : P) : (X LiesOn (LIN A B)) ↔ collinear A B X := ⟨
  fun hx ↦ (LIN A B).linear fst_pt_lies_on_mk_pt_pt snd_pt_lies_on_mk_pt_pt hx,
  fun c ↦ (LIN A B).maximal fst_pt_lies_on_mk_pt_pt snd_pt_lies_on_mk_pt_pt c⟩

-- This is also a typical proof that shows how to use linear, maximal, nontriv of a line. Please write it shorter in future.

/-- This theorem states that if $A$ and $B$ are two distinct points on a line $l$, then a point $C$ lies on $l$ if and only if $A$, $B$, and $C$ are collinear. -/
theorem lies_on_iff_collinear_of_ne_lies_on_lies_on {A B : P} {l : Line P} [_h : PtNe B A] (ha : A LiesOn l) (hb : B LiesOn l) (C : P) : (C LiesOn l) ↔ collinear A B C :=
  ⟨fun hc ↦ l.linear ha hb hc, fun c ↦ l.maximal ha hb c⟩

/-- The given theorem is an equivalence statement between the collinearity of three points and the existence of a line on which all three points lie. -/
theorem collinear_iff_exist_line_lies_on (A B C : P) : collinear A B C ↔ ∃ l : Line P, (A LiesOn l) ∧ (B LiesOn l) ∧ (C LiesOn l) := by
  constructor
  · intro c
    by_cases h : PtNe B A
    · exact ⟨LIN A B, fst_pt_lies_on_mk_pt_pt, snd_pt_lies_on_mk_pt_pt,
        (lies_on_line_of_pt_pt_iff_collinear C).mpr c⟩
    rw [PtNe, fact_iff, ne_eq, not_not] at h
    by_cases hh : PtNe C B
    · use LIN B C hh.out
      rw [← h, and_self_left]
      exact ⟨fst_pt_lies_on_mk_pt_pt, snd_pt_lies_on_mk_pt_pt⟩
    rw [PtNe, fact_iff, ne_eq, not_not] at hh
    simp only [hh, h, and_self, exist_line_pt_lies_on A]
  · intro ⟨l, ha, hb, hc⟩
    if h : PtNe B A then exact (lies_on_iff_collinear_of_ne_lies_on_lies_on ha hb C).mp hc
    else
      simp [PtNe, fact_iff] at h
      simp only [h, collinear, or_true, dite_true]

end Line

namespace DirLine

/-- If $A$, $B$ and $C$ are three points on the same directed line $l$, then they are collinear. -/
theorem linear {l : DirLine P} {A B C : P} (h₁ : A LiesOn l) (h₂ : B LiesOn l) (h₃ : C LiesOn l) : collinear A B C :=
  Line.linear h₁ h₂ h₃

/-- If $A$, $B$ and $C$ are three collinear points in which $A \neq B$, then $C$ lies on the directed line associated to $AB$. -/
theorem pt_pt_maximal {A B C : P} [_h : PtNe B A] (Co : collinear A B C) : C LiesOn (DLIN A B) :=
  Line.pt_pt_maximal Co

/-- Given two points $A$ and $B$ on a directed line $l$, if a point $C$ is so that $A$, $B$, and $C$ are collinear, then $C$ lies on $l$. -/
theorem maximal {l : DirLine P} {A B C : P} (h₁ : A LiesOn l) (h₂ : B LiesOn l) [_h : PtNe B A] (Co : collinear A B C) : C LiesOn l :=
  Line.maximal h₁ h₂ Co

/-- Given two distinct points $A$ and $B$, a point $X$ lies on the directed line from $A$ to $B$ if and only if $A$, $B$, and $X$ are collinear. -/
theorem lies_on_dirline_of_pt_pt_iff_collinear {A B : P} [_h : PtNe B A] (X : P) : (X LiesOn (DLIN A B)) ↔ collinear A B X :=
  Line.lies_on_line_of_pt_pt_iff_collinear X

/-- Let $A$ and $B$ be two distinct points on a directed line $l$, then a point $C$ lies on $l$ if and only if $A$, $B$ and $C$ are collinear. -/
theorem lies_on_iff_collinear_of_ne_lies_on_lies_on {A B : P} {l : DirLine P} [_h : PtNe B A] (ha : A LiesOn l) (hb : B LiesOn l) (C : P) : (C LiesOn l) ↔ collinear A B C :=
  Line.lies_on_iff_collinear_of_ne_lies_on_lies_on ha hb C

/-- The theorem states that three points $A$, $B$, and $C$ are collinear if and only if there exists a line $l$ such that $A$, $B$, and $C$ all lie on $l$. -/
theorem collinear_iff_exist_line_lies_on (A B C : P) : collinear A B C ↔ ∃ l : Line P, (A LiesOn l) ∧ (B LiesOn l) ∧ (C LiesOn l) :=
  Line.collinear_iff_exist_line_lies_on A B C

end DirLine

end collinear



section Archimedean_property

namespace Line

/-- There are two distinct points on a line, i.e. given a point $A$ on a line $l$, there exists a point $B$ on $l$ such that $B \neq A$. -/
theorem exists_ne_pt_pt_lies_on (A : P) {l : Line P} : ∃ B : P, B LiesOn l ∧ B ≠ A := by
  rcases l.nontriv with ⟨X, Y, hx, hy, ne⟩
  exact if h : A = X then ⟨Y, hy, ne.trans_eq h.symm⟩ else ⟨X, hx, ne_comm.mp h⟩

/-- Given two distinct points $A$ and $B$, if $A$ lies on a line $l$ and the projective direction of segment $AB$ is the same as that of $l$, then $B$ lies on the $l$. -/
theorem lies_on_of_SegND_toProj_eq_toProj {A B : P} {l : Line P} (ha : A LiesOn l) [_hab : PtNe B A] (hp : (SEG_nd A B).toProj = l.toProj) : B LiesOn l :=
  (lies_on_iff_eq_toProj_of_lies_on ha).mpr hp

/-- Let $A$ and $B$ be two distinct points on a line $l$, then moving $B$ by the vector $\xrightarrow{AB}$ still lies on $l$. -/
theorem vec_vadd_pt_lies_on_line {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) [_h : PtNe B A] : (VEC A B) +ᵥ B LiesOn l := by
  rw [← eq_line_of_pt_pt_of_ne hA hB]
  refine' Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev.mpr
    (.inl ⟨2 * ‖VEC A B‖, mul_nonneg zero_le_two (norm_nonneg (VEC A B)), _⟩)
  have eq : VEC A (VEC A B +ᵥ B) = (2 : ℝ) • (VEC A B) := (vadd_vsub_assoc _ B A).trans (two_smul _ _).symm
  simp [Ray.mk_pt_pt, eq, mul_smul]

/-- Given two distinct points $A$ and $B$ on a line $l$, there exists a point $C$ on the line $l$ such that $B$ lies on the segment $AC$. -/
theorem exist_pt_beyond_pt_right {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) [_h : PtNe B A] : ∃ C : P, C LiesOn l ∧ B LiesInt (SEG A C) :=
  ⟨VEC A B +ᵥ B, vec_vadd_pt_lies_on_line hA hB, (SEG_nd A B).target_lies_int_seg_source_vec_vadd_target⟩

/-- Given two distinct points $A$ and $B$ on a line $l$, there exists some point $C$ on $l$ such that $A$ lies in the interior of the segment $CB$. -/
theorem exist_pt_beyond_pt_left {A B : P} {l : Line P} (hA : A LiesOn l) (hB : B LiesOn l) [_h : PtNe B A] : ∃ C : P, C LiesOn l ∧ A LiesInt (SEG C B) := by
  rcases exist_pt_beyond_pt_right hB hA with ⟨C, cl, acb⟩
  exact ⟨C, cl, Seg.lies_int_rev_iff_lies_int.mp acb⟩

end Line

namespace DirLine

/-- Given a point $A$ and a directed line $l$, there exists some point $B$ different from $A$ that lies on $l$. -/
theorem exists_ne_pt_pt_lies_on (A : P) {l : DirLine P} : ∃ B : P, B LiesOn l ∧ B ≠ A :=
  l.toLine.exists_ne_pt_pt_lies_on A

/-- Given two distinct points $A$ and $B$ and a directed line l, if $A$ lies on $l$ and the segment $AB$ is in the same direction as $l$, then $B$ lies on $l$. -/
theorem lies_on_of_SegND_toProj_eq_toProj {A B : P} {l : DirLine P} (ha : A LiesOn l) [_hab : PtNe B A] (hp : (SEG_nd A B).toDir = l.toDir) : B LiesOn l :=
  Line.lies_on_of_SegND_toProj_eq_toProj ha ((congrArg Dir.toProj hp).trans l.toLine_toProj_eq_toProj.symm)

/-- Given two distinct points $A$ and $B$ on a directed line $l$, there exists a point $C$ on $l$ such that $B$ lies in the interior of the segment AC.
-/
theorem exist_pt_beyond_pt_right {A B : P} {l : DirLine P} (hA : A LiesOn l) (hB : B LiesOn l) [_h : PtNe B A] : ∃ C : P, C LiesOn l ∧ B LiesInt (SEG A C) :=
  Line.exist_pt_beyond_pt_right hA hB

/-- Let $A$ and $B$ be two distinct points that lie on a directed line $l$, then there exists a point $C$ on $l$ such that $A$ lies in the interior of segment $CB$. -/
theorem exist_pt_beyond_pt_left {A B : P} {l : DirLine P} (hA : A LiesOn l) (hB : B LiesOn l) [_h : PtNe B A] : ∃ C : P, C LiesOn l ∧ A LiesInt (SEG C B) :=
  Line.exist_pt_beyond_pt_left hA hB

end DirLine

end Archimedean_property



section addtorsor

namespace DirLine

/-- A directed line can be viewed as a torsor over the addition group structure of $\mathbb{R}$, that is, points on a directed line can be translated by real multiples of the unit direction vector. -/
instance instRealNormedAddTorsor (l : DirLine P) : NormedAddTorsor ℝ l.carrier.Elem where
  vadd :=
    fun x ⟨A, ha⟩ ↦ ⟨x • l.toDir.unitVec +ᵥ A, lies_on_of_exist_real_vec_eq_smul_toDir ha (vadd_vsub _ A)⟩
  zero_vadd := by
    intro ⟨A, _⟩
    apply Subtype.val_inj.mp
    show (0 : ℝ) • l.toDir.unitVec +ᵥ A = A
    rw [zero_smul, zero_vadd]
  add_vadd := by
    intro x y ⟨A, _⟩
    apply Subtype.val_inj.mp
    show (x + y) • l.toDir.unitVec +ᵥ A = x • l.toDir.unitVec +ᵥ (y • l.toDir.unitVec +ᵥ A)
    rw [add_smul, add_vadd]
  vsub := fun ⟨A, _⟩ ⟨B, _⟩ ↦ inner (A -ᵥ B) l.toDir.unitVec
  nonempty := by
    rcases l.nontriv with ⟨A, _, ha, _⟩
    exact ⟨A, ha⟩
  vsub_vadd' := by
    intro ⟨A, ha⟩ ⟨B, hb⟩
    apply Subtype.val_inj.mp
    show inner (VEC B A) l.toDir.unitVec • l.toDir.unitVec +ᵥ B = A
    have h : @inner ℝ _ _ (VEC B A) l.toDir.unitVec • l.toDir.unitVec = VEC B A := by
      rcases exist_real_vec_eq_smul_toDir_of_lies_on hb ha with ⟨t, h⟩
      rw [h, real_inner_smul_self_left l.toDir.unitVec t]
      simp only [VecND.norm_coe, Dir.norm_unitVecND, mul_one]
    rw [h]
    exact vsub_vadd A B
  vadd_vsub' := by
    intro x ⟨A, _⟩
    show inner (x • l.toDir.unitVec +ᵥ A -ᵥ A) l.toDir.unitVec = x
    rw [vadd_vsub, real_inner_smul_self_left l.toDir.unitVec x, l.toDir.norm_unitVec, mul_one, mul_one]
  dist_eq_norm' := by
    intro ⟨A, ha⟩ ⟨B, hb⟩
    refine' (dist_eq_norm_vsub Vec A B).trans _
    rcases exist_real_vec_eq_smul_toDir_of_lies_on hb ha with ⟨t, h⟩
    show ‖VEC B A‖ = ‖@inner ℝ _ _ (VEC B A) l.toDir.unitVec‖
    simp only [h, norm_smul, Real.norm_eq_abs, VecND.norm_coe, Dir.norm_unitVecND, mul_one,
      real_inner_smul_left, Dir.inner_unitVec, vsub_self, AngValue.cos_zero]

section ddist

/-- Given two points $A$ and $B$ on a directed line $l$, this function returns the distance from $A$ to $B$ on the directed line $l$, as a real number; or in short $\dist(A, B)$. -/
def ddist {l : DirLine P} {A B : P} (ha : A LiesOn l) (hb : B LiesOn l) : ℝ :=
  (⟨B, hb⟩ : l.carrier.Elem) -ᵥ ⟨A, ha⟩

/-- For a point $A$ on a directed line $l$, the distance from $A$ to itself is $0$, i.e. $\dist(A, A) = 0$. -/
@[simp]
theorem ddist_self {l: DirLine P} {A : P} (ha : A LiesOn l) : ddist ha ha = 0 :=
  vsub_self _

/-- The negation of the distance from point $A$ to point $B$ on a directed line $l$ is equal to the distance from point $B$ to point $A$ on the same directed line $l$. -/
@[simp]
theorem neg_ddist_eq_ddist_rev {l: DirLine P} {A B : P} (ha : A LiesOn l) (hb : B LiesOn l) : - ddist ha hb = ddist hb ha :=
  neg_vsub_eq_vsub_rev _ _

/-- The distance from point $A$ to point $B$ on a directed line $l$ is zero if and only if $B$ is equal to $A$. -/
@[simp]
theorem ddist_eq_zero_iff_eq {l: DirLine P} {A B : P} (ha : A LiesOn l) (hb : B LiesOn l) : ddist ha hb = 0 ↔ B = A :=
  vsub_eq_zero_iff_eq.trans Subtype.mk_eq_mk

/-- The distance from point $A$ to point $B$ on directed line $l$ is non-zero if and only if $B$ is not equal to $A$. -/
@[simp]
theorem ddist_ne_zero_iff_ne {l: DirLine P} {A B : P} (ha : A LiesOn l) (hb : B LiesOn l) : ddist ha hb ≠ 0 ↔ B ≠ A := (ddist_eq_zero_iff_eq ha hb).not

/-- Let $A$, $B$ and $C$ be three points on a directed line $l$. Then the sum of the distance from $A$ to $B$ and the distance from $B$ to $C$ is equal to the distance from $A$ to $C$, i.e. $\dist(A, B) + \dist(B, C) = \dist(A, C)$. -/
@[simp]
theorem ddist_add {l: DirLine P} {A B C : P} (ha : A LiesOn l) (hb : B LiesOn l) (hc : C LiesOn l) : ddist ha hb + ddist hb hc = ddist ha hc := by
  rw [add_comm]
  exact vsub_add_vsub_cancel _ _ _

/-- On a directed line $l$, the distance from a point $A$ to point $B$ minus the distance from point $A$ to point $C$ is equal to the distance from point $C$ to point $B$. -/
@[simp]
theorem ddist_sub_right {l: DirLine P} {A B C : P} (ha : A LiesOn l) (hb : B LiesOn l) (hc : C LiesOn l) : ddist ha hb - ddist ha hc = ddist hc hb :=
  vsub_sub_vsub_cancel_right _ _ _

/-- Given three points $A$, $B$, and $C$ on a directed line $l$, the difference between the distance from $A$ to $C$ and the distance from $B$ to $C$ is equal to the distance from $A$ to $B$. -/
@[simp]
theorem ddist_sub_left {l: DirLine P} {A B C : P} (ha : A LiesOn l) (hb : B LiesOn l) (hc : C LiesOn l) : ddist ha hc - ddist hb hc = ddist ha hb :=
  vsub_sub_vsub_cancel_left _ _ _

/-- Given three points $A$, $B$, and $C$ on a directed line, the distance from point $A$ to point $B$ is equal to the distance from point $A$ to point $C$ if and only if point $B$ is the same as point $C$. -/
@[simp]
theorem ddist_left_cancel_iff {l: DirLine P} {A B C : P} (ha : A LiesOn l) (hb : B LiesOn l) (hc : C LiesOn l) : ddist ha hb = ddist ha hc ↔ B = C :=
  vsub_left_cancel_iff.trans Subtype.mk_eq_mk

/-- On a directed line, the distance from point $A$ to point $C$ is equal to the distance from point $B$ to point $C$ if and only if $A$ is equal to $B$. -/
@[simp]
theorem ddist_right_cancel_iff {l: DirLine P} {A B C : P} (ha : A LiesOn l) (hb : B LiesOn l) (hc : C LiesOn l) : ddist ha hc = ddist hb hc ↔ A = B :=
  vsub_right_cancel_iff.trans Subtype.mk_eq_mk

/-- Let $A$, $B$, $C$ and $D$ be four points on a directed line $l$. Then the distance from $A$ to $B$ minus the distance from $C$ to $D$ is equal to the distance from $D$ to $B$ minus the distance from $C$ to $A$, i.e $\dist(A, B) - \dist(C, D) = \dist(D, B) - \dist(C, A)$ -/
theorem ddist_sub_ddist_comm {l: DirLine P} {A B C D : P} (ha : A LiesOn l) (hb : B LiesOn l) (hc : C LiesOn l) (hd : D LiesOn l) : ddist ha hb - ddist hc hd = ddist hd hb - ddist hc ha :=
  vsub_sub_vsub_comm _ _ _ _

/-- On a directed line, the sum of the distance from $A$ to $B$ and the distance from $C$ to $D$ is equal to the sum of the distance from $A$ to $D$ and the distance from $C$ to $B$. -/
theorem ddist_add_ddist_comm {l: DirLine P} {A B C D : P} (ha : A LiesOn l) (hb : B LiesOn l) (hc : C LiesOn l) (hd : D LiesOn l) : ddist ha hb + ddist hc hd = ddist ha hd + ddist hc hb := by
  rw [← neg_ddist_eq_ddist_rev hd hc]
  apply (ddist_sub_ddist_comm ha hb hd hc).trans
  rw [add_comm, ← neg_ddist_eq_ddist_rev hd ha]
  rfl

end ddist

section order

instance instLinearOrderedAddTorsor (l : DirLine P) : LinearOrderedAddTorsor ℝ l.carrier.Elem :=
  AddTorsor.LinearOrderedAddTorsor_of_LinearOrderedAddCommGroup ℝ l.carrier.Elem

/-- The theorem states that for two points $A$ and $B$ on a directed line $l$, we write $A \leq B$ if the distance from $A$ to $B$ is nonnegative. -/
theorem le_iff_zero_le_ddist {l: DirLine P} {A B : P} (ha : A LiesOn l) (hb : B LiesOn l) : (⟨A, ha⟩ : l.carrier.Elem) ≤ ⟨B, hb⟩ ↔ 0 ≤ ddist ha hb :=
  vsub_le_zero_iff_zero_le_vsub_rev (⟨A, ha⟩ : l.carrier.Elem) ⟨B, hb⟩

/-- For two points $A$ and $B$ on a directed line $l$, $A$ is less than $B$ if and only if the distance from $A$ to $B$ is positive. -/
theorem lt_iff_zero_lt_ddist {l: DirLine P} {A B : P} (ha : A LiesOn l) (hb : B LiesOn l) : (⟨A, ha⟩ : l.carrier.Elem) < ⟨B, hb⟩ ↔ 0 < ddist ha hb :=
  vsub_lt_zero_iff_zero_lt_vsub_rev (⟨A, ha⟩ : l.carrier.Elem) ⟨B, hb⟩

end order

end DirLine

end addtorsor

end EuclidGeom
