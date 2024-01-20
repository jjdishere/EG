import EuclideanGeometry.Foundation.Axiom.Basic.Class

/-!
# Segments and rays

In this file, we define the class of segments, rays, and their coercions, as well as basic properties.  A more precise plan in terms of sections is as follows:
* (1) (definition) We define the corresponding classes: rays, segments, and nondegenerate segments.
* (2) (make) We define the make functions of rays, segments, and nondegenerate segments.
* (3) (coercion) We define the coercions among rays, segments, and nondegenerate segments, as well as coercions to directions, or projective directions.
* (4) (coercion-compatibility) We discuss compatibility of coercion functions.
* (5) (lieson-compatibility) We discuss compatibility regarding points lying on or in the interior of segments or rays.
* (6) (reverse) We introduce the concept of reversing a segment and reversing a ray.
* (7) (extension) We define the extension ray of a nondegenerate segment.
* (8) (length) We define the length function of a segment.
* (9) (midpoint) We define the function that gives the midpoint of a segment.
* (10) (archimedean) We discuss the Archimedean property of a segment.

## Important definitions

* Class `Ray` : A \emph{ray} consists of the pair of its source point $P$ and its direction.
* Class `Seg` : A \emph{segment} consists of a pair of points: the source and the target. (We allow the source and the target to be the same.)
* Subclass `SegND` : A \emph{nondegenerate segment} is a segment whose source and target are not equal.
* Definition `Seg.length` : The function that gives the length of a given segment.
* Definition `Ray.reverse` : Given a ray, this function returns the ray with the same source but with reversed direction.
* Definition `Seg.reverse` : Given a segment, this function swapped its source and target point.
* Definition `SegND.reverse` : Given a nondegenerate segment, this function swapped its source and target point.
* Definition `SegND.extension` : Given a nondegenerate segment, this function returns the extension ray of the segment.
* Definition `Seg.midpoint` : This function returns the hmidpoint of a segment.


## List of notations

* `SEG A B` : notation for the segment with source $A$ and target $B$.
* `SEG_nd A B` : notation for the segment with source $A$ and target $B$, where $h$ is a proof of that $A \neq B$.
* `RAY A B h` : notation for the ray with source $A$ in the direction of $B$, where $h$ is a proof of that $A \neq B$.

## List of main theorems

## Implementation notes

## Further works

-/


noncomputable section
namespace EuclidGeom


section definition
/-!
## (1) Definition
-/

/-- A \emph{ray} consists of a pair of a point $P$ and a direction; it is the ray that starts at the point and extends in the given direction. -/
@[ext]
structure Ray (P : Type*) [EuclideanPlane P] where
  /-- returns the source of the ray. -/
  source : P
  /-- returns the direction of the ray. -/
  toDir : Dir

attribute [pp_dot] Ray.source Ray.toDir

alias Ray.mk_pt_dir := Ray.mk

/-- A \emph{Segment} consists of a pair of points: the source and the target; it is the segment from the source to the target. (We allow the source and the target to be the same.) -/
@[ext]
structure Seg (P : Type*) [EuclideanPlane P] where
  /-- returns the source of the segment. -/
  source : P
  /-- returns the target of the segment. -/
  target : P

attribute [pp_dot] Seg.source Seg.target

namespace Seg

/-- Given a segment $AB$, this function returns whether the segment $AB$ is nondegenerate, i.e. whether $A \neq B$. -/
def IsND {P : Type*} [EuclideanPlane P] (seg : Seg P) : Prop := seg.target ≠ seg.source

end Seg

/-- A \emph{nondegenerate segment} is a segment $AB$ that is nondegenerate, i.e. $A \neq B$. -/
def SegND (P : Type*) [EuclideanPlane P] := {seg : Seg P // seg.IsND}


end definition

variable {P : Type*} [EuclideanPlane P]


section make
/-!
## (2) Make
-/

/-- Given two points $A$ and $B$, this returns the segment with source $A$ and target $B$. It is an abbreviation of $\verb|Seg.mk|$. -/
scoped notation "SEG" => Seg.mk

/-- Given two distinct points $A$ and $B$, this function returns a nondegenerate segment with source $A$ and target $B$. We use $\verb|SEG_nd|$ to abbreviate $\verb|SegND.mk|$. -/
def SegND.mk (A B : P) (h : B ≠ A) : SegND P where
  val := SEG A B
  property := h

@[inherit_doc SegND.mk]
scoped syntax "SEG_nd" ws term:max ws term:max (ws term:max)? : term

macro_rules
  | `(SEG_nd $A $B) => `(SegND.mk $A $B (@Fact.out _ inferInstance))
  | `(SEG_nd $A $B $h) => `(SegND.mk $A $B $h)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `SegND.mk` -/
@[delab app.EuclidGeom.SegND.mk]
def delabSegNDMk : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``SegND.mk 5
  let A ← withNaryArg 2 delab
  let B ← withNaryArg 3 delab
  withNaryArg 4 do
    if (← getExpr).isAppOfArity' ``Fact.out 2 then
      `(SEG_nd $A $B)
    else
      `(SEG_nd $A $B $(← delab))

/-- Given two distinct points $A$ and $B$, this function returns the ray starting from $A$ in the direction of $B$. By definition, the direction of the ray is given by the normalization of the vector from $A$ to $B$, using $\verb|toDir|$ function. We use $\verb|RAY|$ to abbreviate $\verb|Ray.mk_pt_pt|$. -/
def Ray.mk_pt_pt (A B : P) (h : B ≠ A) : Ray P where
  source := A
  toDir := VecND.toDir ⟨VEC A B, (vsub_ne_zero.mpr h)⟩

@[inherit_doc Ray.mk_pt_pt]
scoped syntax "RAY" ws term:max ws term:max (ws term:max)? : term

macro_rules
  | `(RAY $A $B) => `(Ray.mk_pt_pt $A $B (@Fact.out _ inferInstance))
  | `(RAY $A $B $h) => `(Ray.mk_pt_pt $A $B $h)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `Ray.mk_pt_pt` -/
@[delab app.EuclidGeom.Ray.mk_pt_pt]
def delabRayMkPtPt : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``Ray.mk_pt_pt 5
  let A ← withNaryArg 2 delab
  let B ← withNaryArg 3 delab
  withNaryArg 4 do
    if (← getExpr).isAppOfArity' ``Fact.out 2 then
      `(RAY $A $B)
    else
      `(RAY $A $B $(← delab))

end make


section coersion
/-!
## (3) Coersion
-/


namespace Ray

/-- Given a ray, this function returns its projective direction; it is the projective direction of the direction of the ray. -/
@[pp_dot]
def toProj (ray : Ray P) : Proj := (ray.toDir : Proj)

/-- Given a point $X$ and a ray $ray$, this function returns whether $X$ lies on $ray$; here saying that $X$ lies on $ray$ means that the vector from the start point of the ray to $X$ is some nonnegative multiple of the direction vector of the ray. -/
protected def IsOn (X : P) (ray : Ray P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ VEC ray.source X = t • ray.toDir.unitVec

/-- Given a point $X$ and a ray, this function returns whether the point lies in the interior of the ray; here saying that a point lies in the interior of a ray means that it lies on the ray and is not equal to the source of the ray. -/
protected structure IsInt (X : P) (ray : Ray P) : Prop where
  isOn : Ray.IsOn X ray
  ne_source : X ≠ ray.source

alias ne_source_of_lies_int := IsInt.ne_source

/-- Given a ray, its carrier is the set of points that lie on the ray. -/
protected def carrier (ray : Ray P) : Set P := { X : P | Ray.IsOn X ray }

/-- Given a ray, its interior is the set of points that lie in the interior of the ray. -/
protected def interior (ray : Ray P) : Set P := { X : P | Ray.IsInt X ray }

/-- This is to register that a ray is an instance of a class of objects that we may speak of both carrier and interior (and that the interior is a subset of the carrier). -/
instance : IntFig (Ray P) P where
  carrier := Ray.carrier
  interior := Ray.interior
  interior_subset_carrier _ _ := IsInt.isOn

end Ray

namespace Seg

/-- Given a segment, this function returns the vector associated to the segment, that is, the vector from the source of the segment to the target of the segment. -/
@[pp_dot]
def toVec (seg : Seg P) : Vec := VEC seg.source seg.target

@[simp]
lemma mk_source_target (s : Seg P) : VEC s.source s.target = s.toVec := rfl

/-- Given a point $X$ and a segment $seg$, this function returns whether $X$ lies on $seg$; here saying that $X$ lies on $seg$ means that the vector from the source of $seg$ to $X$ is a real multiple $t$ of the vector of $seg$ with $0 \leq t \leq 1$. -/
protected def IsOn (X : P) (seg : Seg P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧ VEC seg.source X  = t • (VEC seg.source seg.target)

/-- Given a point $X$ and a segment $seg$, this function returns whether $X$ lies in the interior of $seg$; here saying that $X$ lies in the interior of $seg$ means $X$ lies on $seg$ and is different from the source and the target of $seg$. -/
protected structure IsInt (X : P) (seg : Seg P) : Prop where
  isOn : Seg.IsOn X seg
  ne_source : X ≠ seg.source
  ne_target : X ≠ seg.target

alias ne_source_of_lies_int := IsInt.ne_source

alias ne_target_of_lies_int := IsInt.ne_target

/-- Given a segment, this function returns the set of points that lie on the segment. -/
protected def carrier (seg : Seg P) : Set P := { X : P | Seg.IsOn X seg }

/-- Given a segment, this function returns the set of points that lie in the interior of the segment. -/
protected def interior (seg : Seg P) : Set P := { X : P | Seg.IsInt X seg }

/-- Instance $\verb|IntFig Seg|$ : This is to register that a segment is an instance of a class of objects that we may speak of both carrier and interior (and that the interior is a subset of the carrier). -/
instance : IntFig (Seg P) P where
  carrier := Seg.carrier
  interior := Seg.interior
  interior_subset_carrier _ _ h := h.1

end Seg

namespace SegND

/-- One may naturally coerce a nondegenerate segment into a segment. -/
instance : Coe (SegND P) (Seg P) where
  coe := fun x => x.1

/-- Given a nondegenerate segment, this function returns the source of the segment. -/
@[pp_dot]
abbrev source (seg_nd : SegND P) : P := seg_nd.1.source

/-- Given a nondegenerate segment, this function returns the target of the segment. -/
@[pp_dot]
abbrev target (seg_nd : SegND P) : P := seg_nd.1.target

/-- Given a nondegenerate segment $AB$, this function returns the nondegenerate vector $\overrightarrow{AB}$. -/
@[pp_dot]
def toVecND (seg_nd : SegND P) : VecND := ⟨VEC seg_nd.source seg_nd.target, ne_iff_vec_ne_zero.mp seg_nd.2⟩

/-- Given a nondegenerate segment $AB$, this function returns the direction associated to the segment, defined by normalizing the nondegenerate vector $\overrightarrow{AB}$. -/
@[pp_dot]
abbrev toDir (seg_nd : SegND P) : Dir := seg_nd.toVecND.toDir

/-- Given a nondegenerate segment $AB$, this function returns the ray $AB$, whose source is $A$ in the direction of $B$. -/
@[pp_dot]
def toRay (seg_nd : SegND P) : Ray P where
  source := seg_nd.1.source
  toDir := seg_nd.toDir

@[simp]
lemma toRay_source (s : SegND P) : s.toRay.source = s.source := rfl

/-- Given a nondegenerate segment $AB$, this function returns the projective direction  of $AB$, defined as the projective direction of the nondegenerate vector $\overrightarrow{AB}$. -/
@[pp_dot]
abbrev toProj (seg_nd : SegND P) : Proj := seg_nd.toVecND.toProj

/-- Given a point $A$ and a nondegenerate segment $seg_nd$, this function returns whether $A$ lies on $seg_nd$, namely, whether it lies on the corresponding segment.-/
protected abbrev IsOn (X : P) (seg_nd : SegND P) : Prop := Seg.IsOn X seg_nd.1

/-- Given a point $A$ and a nondegenerate segment $seg_nd$, this function returns whether $A$ lies in the interior of $seg_nd$, namely, whether it lies in the interior of the corresponding segment. -/
protected abbrev IsInt (X : P) (seg_nd : SegND P) : Prop := Seg.IsInt X seg_nd.1

/-- Given a nondegenerate segment, this function returns the set of points that lie on the segment. -/
protected abbrev carrier (seg_nd : SegND P) : Set P := { X : P | SegND.IsOn X seg_nd }

/-- Given a nondegenerate segment, this function returns the set of points that lie in the interior of the segment. -/
protected abbrev interior (seg_nd : SegND P) : Set P := { X : P | Seg.IsInt X seg_nd }

/-- This is to register that a nondegenerate segment is an instance of a class of objects that we may speak of both carrier and interior (and that the interior is a subset of the carrier). -/
instance : IntFig (SegND P) P where
  carrier := SegND.carrier
  interior := SegND.interior
  interior_subset_carrier _ _ h := h.1

end SegND

@[simp]
lemma Ray.mkPtPt_toDir (A B : P) [_h : PtNe B A] : (RAY A B).toDir = (VEC_nd A B).toDir := rfl

@[simp]
lemma SegND.mkPtPt_toDir (A B : P) [_h : PtNe B A] : (SEG_nd A B).toDir = (VEC_nd A B).toDir := rfl

end coersion



section coersion_compatibility
/-!
## (4) Coersion compatiblity
-/

/-- Given a nondegenerate segment, the direction of to the ray associated to the segment is the same as the direction of the segment. -/
@[simp]
theorem SegND.toRay_toDir_eq_toDir {seg_nd : SegND P} : seg_nd.toRay.toDir = seg_nd.toDir := rfl

/-- Given a nondegenerate segment, the projective direction of the ray associated to the segment is the same as the projective direction of the segment. -/
@[simp]
theorem SegND.toRay_toProj_eq_toProj {seg_nd : SegND P} : seg_nd.toRay.toProj = seg_nd.toProj := rfl


/-- Given two points $A$ and $B$, the vector associated to the segment $AB$ is same as vector $\overrightarrow{AB}$. -/
@[simp]
theorem seg_toVec_eq_vec {A B : P} : (SEG A B).toVec = VEC A B := rfl

/-- Given a segment $AB$, $A$ is same as $B$ if and only if vector $\overrightarrow{AB}$ is zero. -/
theorem toVec_eq_zero_of_deg {l : Seg P} : (l.target = l.source) ↔ l.toVec = 0 := by
  rw [Seg.toVec, Vec.mkPtPt, vsub_eq_zero_iff_eq]

/-- Given two distinct points $A$ and $B$, the direction of ray $AB$ is same as the negative direction of ray $BA$ -/
theorem Ray.toDir_eq_neg_toDir_of_mk_pt_pt {A B : P} [h : PtNe B A] : (RAY A B).toDir = -(RAY B A).toDir := by
  simp only [Ray.mk_pt_pt, ne_eq]
  rw [← VecND.neg_toDir, ← VecND.mk_neg]
  congr
  rw [neg_vec]

/-- Given two distinct points $A$ and $B$, the projective direction of ray $AB$ is same as that of ray $BA$. -/
theorem Ray.toProj_eq_toProj_of_mk_pt_pt {A B : P} [_h : PtNe B A] : (RAY A B).toProj = (RAY B A).toProj :=
  Dir.toProj_eq_toProj_iff.mpr (.inr toDir_eq_neg_toDir_of_mk_pt_pt)

/-- Given two distinct points $A$ and $B$, the ray associated to the segment $AB$ is same as ray $AB$. -/
theorem pt_pt_seg_toRay_eq_pt_pt_ray {A B : P} [_h : PtNe B A] : (SEG_nd A B).toRay = RAY A B := rfl

/-- Given a segment $AB$, $AB$ is nondegenerate if and only if vector  $\overrightarrow{AB}$ is nonzero. -/
theorem Seg.IsND_iff_toVec_ne_zero {l : Seg P} : l.IsND ↔ l.toVec ≠ 0 := toVec_eq_zero_of_deg.not

/-- If $ray_1$ and $ray_2$ are two rays with the same projective direction, then the direction vector of $ray_2$ is a real multiple of the direction vector of $ray_1$. -/
theorem dir_parallel_of_same_proj {ray₁ ray₂ : Ray P} (h : ray₁.toProj = ray₂.toProj) : ∃ t : ℝ, ray₂.toDir.unitVec = t • ray₁.toDir.unitVec := by
  rcases Dir.toProj_eq_toProj_iff.mp h with xy | xy
  · use 1
    rw [one_smul, xy]
  · use -1
    rw [xy, Dir.neg_unitVec, neg_one_smul, neg_neg]

end coersion_compatibility



section lieson_compatibility
/-!
## (5) Lieson compatibility
-/

/-- Given a nondegenerate segment, a point lies on the nondegenerate segment if and only if it lies on the corresponding segment (without knowing the nondegenate condition). -/
@[simp]
theorem SegND.lies_on_of_lies_on {X : P} {seg_nd : SegND P} : X LiesOn seg_nd ↔ X LiesOn seg_nd.1 := ⟨ fun a => a, fun a => a ⟩

/-- Given a nondegenerate segment, a point lies in the interior of the nondegenerate segment if and only if it lies in the interior of the corresponding segment (without knowing the nondegenate condition). -/
@[simp]
theorem SegND.lies_int_of_lies_int {X : P} {seg_nd : SegND P} : X LiesInt seg_nd ↔ X LiesInt seg_nd.1 := ⟨ fun a => a, fun a => a ⟩

/-- Given a ray, a point $X$ lies on the ray if and only if the vector from the source of the ray to $X$ is a nonnegative multiple of the direction of ray. -/
theorem Ray.lies_on_iff {X : P} {ray : Ray P} : X LiesOn ray ↔ ∃ (t : ℝ) , 0 ≤ t ∧ VEC ray.source X = t • ray.toDir.unitVec := Iff.rfl

/-- Given a ray, a point $X$ lies in the interior of the ray if and only if the vector from the source of the ray to $X$ is a positive multiple of the direction of ray. -/
theorem Ray.lies_int_iff {X : P} {ray : Ray P} : X LiesInt ray ↔ ∃ (t : ℝ) , 0 < t ∧ VEC ray.source X = t • ray.toDir.unitVec := by
  constructor
  intro ⟨⟨t, tnonneg, ht⟩, ns⟩
  · use t
    constructor
    · contrapose! ns
      have : t = 0 := by linarith
      rw [eq_iff_vec_eq_zero, ht, this, zero_smul]
    · exact ht
  · intro ⟨t, tpos, ht⟩
    constructor
    · exact ⟨t, by linarith, ht⟩
    · rw [ne_iff_vec_ne_zero, ht, smul_ne_zero_iff]
      exact ⟨by linarith, VecND.ne_zero _⟩

/-- For a nondegenerate segment $AB$, a point $X$ lies on $AB$ if and only if there exist a real number $t$ satisfying that $0 \leq t \leq 1$ and that the vector $\overrightarrow{AX}$ is same as $t \cdot \overrightarrow{AB}$. -/
theorem SegND.lies_on_iff {X : P} {seg_nd : SegND P}: X LiesOn seg_nd ↔ ∃ (t : ℝ) , 0 ≤ t ∧ t ≤ 1 ∧ VEC seg_nd.source X = t • seg_nd.toVecND.1 := Iff.rfl

/-- For a nondegenerate segment $AB$, a point $X$ lies in the interior of $AB$ if and only if there exist a real number $t$ satisfying that $0 < t < 1$ and that the vector $\overrightarrow{AX}$ is same as $t \cdot \overrightarrow{AB}$. -/
theorem SegND.lies_int_iff {X : P} {seg_nd : SegND P}: X LiesInt seg_nd ↔ ∃ (t : ℝ) , 0 < t ∧ t < 1 ∧ VEC seg_nd.source X = t • seg_nd.toVecND.1 := by
  constructor
  · intro ⟨⟨t, tnonneg, tle1, ht⟩, ns, nt⟩
    rw [ne_iff_vec_ne_zero] at ns nt
    use t
    constructor
    · contrapose! ns
      have : t = 0 := by linarith
      rw [ht, this, zero_smul]
    · constructor
      · contrapose! nt
        have : t = 1 := by linarith
        simp only [this, Seg.mk_source_target, one_smul] at ht
        rw [← vec_sub_vec seg_nd.source]
        exact sub_eq_zero_of_eq ht
      · exact ht
  · intro ⟨t, tpos, tlt1, ht⟩
    constructor
    · exact ⟨t, by linarith, by linarith, ht⟩
    · rw [ne_iff_vec_ne_zero]
      rw [SegND.source] at ht
      rw [ht, smul_ne_zero_iff]
      exact ⟨ by linarith, seg_nd.toVecND.2⟩
    · simp only [ne_eq, toVecND, Seg.mk_source_target] at ht
      rw [ne_iff_vec_ne_zero]
      have h1 : VEC seg_nd.target X = (t - 1) • seg_nd.toVecND.1 := by
        rw [sub_smul]
        simp only [ne_eq, toVecND, Seg.mk_source_target, one_smul]
        rw [← ht]
        exact (vec_sub_vec _ _ _).symm
      rw [SegND.target] at h1
      rw [h1, smul_ne_zero_iff]
      exact ⟨by linarith, seg_nd.toVecND.2⟩

/-- For a nondegenerate segment $AB$, if a point $X$ lies on the interior of $AB$ then $X$ not equal to $A$. -/
theorem SegND.ne_source_of_lies_int {X : P} {s : SegND P} (h : X LiesInt s) : X ≠ s.source :=
  h.ne_source

/-- For a nondegenerate segment $AB$, if a point $X$ lies on the interior of $AB$ then $X$ not equal to $B$. -/
theorem SegND.ne_target_of_lies_int {X : P} {s : SegND P} (h : X LiesInt s) : X ≠ s.target :=
  h.ne_target

/-- For a segment $AB$, if there exists an interior point $X$, then it is nondegenerate. -/
theorem Seg.isND_of_pt_liesint {seg : Seg P} {X : P} (h : X LiesInt seg) : seg.IsND := by
  rcases h.1 with ⟨t, ⟨_, ⟨_, H⟩⟩⟩
  rw [IsND]
  by_contra H1
  rw [eq_iff_vec_eq_zero] at H1
  rw [H1, smul_zero] at H
  apply h.2
  rw [eq_iff_vec_eq_zero]
  apply H

/-- For a segment $AB$, a point $X$ lies in the interior of $AB$ if and only if $AB$ is nondegenerate, and there exist a real number $t$ satisfying that $0 < t < 1$ and that the vector $\overrightarrow{AX}$ is same as $t \cdot \overrightarrow{AB}$. -/
theorem Seg.lies_int_iff {X : P} {seg : Seg P}: X LiesInt seg ↔ seg.IsND ∧ (∃ (t : ℝ) , 0 < t ∧ t < 1 ∧ VEC seg.source X = t • seg.toVec) := by
  constructor
  · intro h1
    let segnd : SegND P := ⟨ seg, seg.isND_of_pt_liesint h1 ⟩
    exact ⟨ segnd.2, (segnd.lies_int_iff).mp h1 ⟩
  · intro h2
    let segnd : SegND P := ⟨ seg, h2.1 ⟩
    exact (segnd.lies_int_iff).mpr h2.2

/-- Given a segment $AB$, the source $A$ of the segment lies on the segment. -/
@[simp]
theorem Seg.source_lies_on {seg : Seg P} : seg.source LiesOn seg :=
  ⟨0, by rfl, zero_le_one, by rw [vec_same_eq_zero, zero_smul]⟩

/--  Given a segment $AB$, the target $B$ lies on the segment $AB$. -/
@[simp]
theorem Seg.target_lies_on {seg : Seg P} : seg.target LiesOn seg := ⟨1, zero_le_one, Eq.le rfl, by rw [one_smul]⟩

/-- Given a segment $AB$, the source $A$ does not belong to the interior of $AB$. -/
@[simp]
theorem Seg.source_not_lies_int {seg : Seg P} : ¬ seg.source LiesInt seg := fun h ↦ h.2 rfl

/-- Given a segment $AB$, the target $B$ does not belong to the interior of $AB$. -/
@[simp]
theorem Seg.target_not_lies_int {seg : Seg P} : ¬ seg.target LiesInt seg := fun h ↦ h.3 rfl

/-- For a segment $AB$, every point of the interior of $AB$ lies on the segment $AB$. -/
@[simp]
theorem Seg.lies_on_of_lies_int {X : P} {seg : Seg P} (h : X LiesInt seg) : X LiesOn seg := h.1

/-- Given a nondegenerate segment $AB$, the source $A$ of the segment lies on the segment. -/
@[simp]
theorem SegND.source_lies_on {seg_nd : SegND P} : seg_nd.source LiesOn seg_nd := seg_nd.1.source_lies_on

/-- Given a nondegenerate segment $AB$, the target $B$ lies on the segment $AB$. -/
@[simp]
theorem SegND.target_lies_on {seg_nd : SegND P} : seg_nd.target LiesOn seg_nd := seg_nd.1.target_lies_on

/-- Given a nondegenerate segment $AB$, the source $A$ does not belong to the interior of $AB$. -/
@[simp]
theorem SegND.source_not_lies_int {seg_nd : SegND P} : ¬ seg_nd.source LiesInt seg_nd := fun h ↦ h.2 rfl

/-- Given a nondegenerate segment $AB$, the target $B$ does not belong to the interior of $AB$. -/
@[simp]
theorem SegND.target_not_lies_int {seg_nd : SegND P} : ¬ seg_nd.target LiesInt seg_nd := fun h ↦ h.3 rfl

/-- For a nondegenerate segment $AB$, every point of the interior of $AB$ lies on the segment $AB$. -/
@[simp]
theorem SegND.lies_on_of_lies_int {X : P} {seg_nd : SegND P} (h : X LiesInt seg_nd) : X LiesOn seg_nd := h.1

/-- Given a ray, the source of the ray lies on the ray. -/
@[simp]
theorem Ray.source_lies_on {ray : Ray P} : ray.source LiesOn ray := ⟨0, by rfl, by rw [vec_same_eq_zero, zero_smul]⟩

/-- Given a ray, the source of the ray does not lie in the interior of the ray. -/
@[simp]
theorem Ray.source_not_lies_int {ray : Ray P} : ¬ ray.source LiesInt ray := fun h ↦ h.2 rfl

/-- For a ray, every point of the interior of the ray lies on the ray. -/
@[simp]
theorem Ray.lies_on_of_lies_int {X : P} {ray : Ray P} (h : X LiesInt ray) : X LiesOn ray := h.1

/-- Given a ray, a point lies in the interior of the ray if and only if it lies on the ray and is different from the source of ray. -/
theorem Ray.lies_int_def {X : P} {ray : Ray P} : X LiesInt ray ↔ X LiesOn ray ∧ X ≠ ray.source :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- For a nondegenerate segment $AB$, every point of the segment $AB$ lies on the ray associated to $AB$. -/
theorem SegND.lies_on_toRay_of_lies_on {X : P} {seg_nd : SegND P} (h : X LiesOn seg_nd) : X LiesOn seg_nd.toRay := by
  rcases h with ⟨t, ht0, _, h⟩
  refine' ⟨t • ‖VEC seg_nd.source seg_nd.target‖, smul_nonneg ht0 (norm_nonneg _), _⟩
  dsimp
  rw [h, mul_smul]
  congr
  exact seg_nd.toVecND.norm_smul_toDir_unitVec.symm

/-- For a nondegenerate segment $seg_nd$, every point of the interior of the $seg_nd$ lies in the interior of the ray associated to the $seg_nd$. -/
theorem SegND.lies_int_toRay_of_lies_int {X : P} {seg_nd : SegND P} (h : X LiesInt seg_nd) : X LiesInt seg_nd.toRay :=
  ⟨SegND.lies_on_toRay_of_lies_on h.1, h.2⟩

/-- Given a nondegenerate segment $seg_nd$, the target of $seg_nd$ lies on the interior of the
ray associated to $seg_nd$ -/
theorem SegND.target_lies_int_toRay {seg_nd : SegND P} : seg_nd.target LiesInt seg_nd.toRay := by
  have H: seg_nd.target LiesOn seg_nd.toRay:= by
    apply SegND.lies_on_toRay_of_lies_on
    exact target_lies_on
  rw [Ray.lies_int_def]; constructor
  apply H
  apply seg_nd.2

/-- Given two distinct points $A$ and $B$, $B$ lies on the ray $AB$. -/
theorem Ray.snd_pt_lies_on_mk_pt_pt {A B : P} [h : PtNe B A] : B LiesOn (RAY A B) := by
  show B LiesOn (SEG_nd A B).toRay
  exact SegND.lies_on_toRay_of_lies_on Seg.target_lies_on

/-- Given two distinct points $A$ and $B$, $B$ lies in the interior of the ray $AB$. -/
theorem Ray.snd_pt_lies_int_mk_pt_pt (A B : P) [h : PtNe B A] : B LiesInt (RAY A B) :=
  ⟨snd_pt_lies_on_mk_pt_pt, h.out⟩

/-- Given a point $A$ on a ray, the direction of the ray is the same as the direction from the source of the ray to $A$. -/
theorem Ray.pt_pt_toDir_eq_ray_toDir {ray : Ray P} {A : P} (h : A LiesInt ray) : (RAY ray.1 A h.2).toDir = ray.toDir := by
  rcases (lies_int_iff).mp h with ⟨t, ht, eq⟩
  trans VecND.toDir ⟨t • ray.toDir.unitVec, (smul_ne_zero ht.ne' (VecND.ne_zero _))⟩
  · simp_rw [← eq]
    rfl
  · simp [ht]

/-- Given a point $A$ on the interior of a ray, the ray starting at the source of the ray in the direction of $A$ is the same as the original ray. -/
theorem Ray.pt_pt_eq_ray {ray : Ray P} {A : P} (h : A LiesInt ray) : RAY ray.1 A h.2 = ray :=
  (Ray.ext _ ray) rfl (pt_pt_toDir_eq_ray_toDir h)

/-- Given a point $A$ on the interior of a ray, the ray associated to the segment from the source of the ray to $A$ is the same as the original ray. -/
theorem Ray.source_int_toRay_eq_ray {ray : Ray P} {A : P} (h : A LiesInt ray) : (SEG_nd ray.source A h.2).toRay = ray :=
  Ray.pt_pt_eq_ray h

/-- Given a point $A$ on the interior of a ray, the vector from the source of the ray to $A$ is equal to the distance of the source and $A$ times the direction vector of the original ray. -/
theorem Ray.vec_eq_dist_smul_toDir_of_lies_on {A : P} {r : Ray P} (h : A LiesOn r) : VEC r.1 A = (dist r.1 A) • r.toDir.unitVec := by
  by_cases heq : A = r.1
  · rw [← heq, vec_same_eq_zero, dist_self, zero_smul]
  push_neg at heq
  have h : A LiesInt r := ⟨h, heq⟩
  have h₁ : RAY r.1 A h.2 = r := Ray.pt_pt_eq_ray h
  calc
    _ = (VEC_nd r.1 A h.2).1 := rfl
    _ = ‖VEC_nd r.1 A h.2‖ • (VEC_nd r.1 A h.2).toDir.unitVec := by simp only [ne_eq,
      VecND.norm_smul_toDir_unitVec]
    _ = (dist r.1 A) • (VEC_nd r.1 A h.2).toDir.unitVec := by
      rw [dist_comm, NormedAddTorsor.dist_eq_norm']
      rfl
    _ = (dist r.1 A) • (RAY r.1 A h.2).2.unitVec := rfl
    _ = (dist r.1 A) • r.2.unitVec := by rw [h₁]

/-- Given two segments $seg_1$ and $seg_2$, if the source and the target of the $seg_1$ both lie on $seg_2$, then every point of $seg_1$ lies on $seg_2$. -/
theorem every_pt_lies_on_seg_of_source_and_target_lies_on_seg {seg₁ seg₂ : Seg P} (h₁ : seg₁.source LiesOn seg₂) (h₂ : seg₁.target LiesOn seg₂) {A : P} (ha : A LiesOn seg₁) : (A LiesOn seg₂) := by
  rcases h₁ with ⟨x, xnonneg, xle1, hx⟩
  rcases h₂ with ⟨y, ynonneg, yle1, hy⟩
  rcases ha with ⟨t, tnonneg, tleone, ht⟩
  rw [←vec_add_vec seg₁.source seg₂.source, ←vec_add_vec seg₁.source seg₂.source seg₁.target, ←neg_vec, hx, hy, neg_add_eq_iff_eq_add, ←neg_smul, smul_add, smul_smul, smul_smul, ←add_smul, ←add_smul, ←add_assoc, mul_neg, ←sub_eq_add_neg, ←one_mul x, ←mul_assoc, ←sub_mul, mul_one] at ht
  use ( (1- t) * x + t * y)
  constructor
  apply add_nonneg
  apply mul_nonneg
  linarith
  linarith
  apply mul_nonneg tnonneg ynonneg
  constructor
  nth_rw 2[←sub_add_cancel 1 t,←mul_one (1-t)]
  nth_rw 4[←mul_one t]
  apply add_le_add
  apply mul_le_mul _ xle1 xnonneg
  linarith
  simp only [le_refl]
  apply mul_le_mul _ yle1 ynonneg tnonneg
  simp only [le_refl]
  rw [ht]

/-- Given two segments $seg_1$ and $seg_2$, if the source and the target of $seg_1$ both lie in the interior of $seg_2$, and if $A$ is a point on $seg_1$, then $A$ lies in the interior of $seg_2$. -/
theorem every_pt_lies_int_seg_of_source_and_target_lies_int_seg {seg₁ seg₂ : Seg P} (h₁ : seg₁.source LiesInt seg₂) (h₂ : seg₁.target LiesInt seg₂) {A : P} (ha : A LiesOn seg₁) : A LiesInt seg₂ := by
  rw [Seg.lies_int_iff]
  constructor
  apply ((Seg.lies_int_iff).mp h₁).1
  rw [Seg.lies_int_iff] at h₁ h₂
  rcases h₁ with ⟨ _ , x, xpos, xlt1, hx⟩
  rcases h₂ with ⟨ _ , y, ypos, ylt1, hy⟩
  rcases ha with ⟨t, tnonneg, tle1, ht⟩
  use ( (1- t) * x + t * y)
  by_cases h : 0 = t
  constructor
  simp only [←h, sub_zero, one_mul, zero_mul, add_zero]
  exact xpos
  constructor
  simp only [←h, sub_zero, one_mul, zero_mul, add_zero]
  exact xlt1
  rw [←h, zero_smul, ←eq_iff_vec_eq_zero] at ht
  simp only [← h, sub_zero, one_mul, zero_mul, add_zero, ht, hx]
  constructor
  apply lt_of_lt_of_le (mul_pos (lt_of_le_of_ne tnonneg h) ypos)
  simp only [le_add_iff_nonneg_left, gt_iff_lt, sub_pos]
  apply mul_nonneg
  linarith
  linarith
  constructor
  have: (1 - t) * x + t * y < (1 - t) * x + t := by
    simp only [add_lt_add_iff_left, gt_iff_lt]
    nth_rw 2[←mul_one t]
    apply mul_lt_mul_of_pos_left ylt1 (lt_of_le_of_ne tnonneg h)
  apply lt_of_lt_of_le this
  have : 1 = 1 - t + t := by norm_num
  nth_rw 2 [this]
  apply add_le_add
  nth_rw 2[←mul_one (1 - t)]
  apply mul_le_mul
  linarith
  linarith
  linarith
  linarith
  linarith
  rw [←vec_add_vec seg₂.1 seg₁.1 A, ht, ←vec_sub_vec seg₂.1 seg₁.1 seg₁.2, hy, hx, ←sub_smul, smul_smul, ←add_smul, ←sub_eq_zero, ←sub_smul, smul_eq_zero]
  left
  ring

/-- Given two segments $seg_1$ and $seg_2$, if the source and the target of $seg_1$ both lie on $seg_2$, and if $A$ is a point in the interior of $seg_1$, then $A$ lies in the interior of $seg_2$. -/
theorem every_int_pt_lies_int_seg_of_source_and_target_lies_on_seg {seg₁ seg₂ : Seg P} (h₁ : seg₁.source LiesOn seg₂) (h₂ : seg₁.target LiesOn seg₂) {A : P} (ha : A LiesInt seg₁) : A LiesInt seg₂ := by
  apply (Seg.lies_int_iff).mpr
  rcases h₁ with ⟨x, xnonneg, xle1, hx⟩
  rcases h₂ with ⟨y, ynonneg, yle1, hy⟩
  rcases (Seg.lies_int_iff).mp ha with ⟨nd, t, tpos, tlt1, ht⟩
  constructor
  rw [Seg.IsND, ne_iff_vec_ne_zero]
  contrapose! nd
  rw [nd, smul_zero, ←eq_iff_vec_eq_zero] at hx hy
  rw [Seg.IsND, not_not, eq_iff_vec_eq_zero, hx, hy, vec_same_eq_zero]
  rw [Seg.toVec, ←vec_sub_vec seg₂.1, ← vec_sub_vec seg₂.1 seg₁.1 seg₁.2, sub_eq_iff_eq_add, hx, hy, ←sub_smul, smul_smul, ←add_smul] at ht
  use ( (1- t) * x + t * y)
  have ynex : y ≠ x := by
    contrapose! nd
    rw [Seg.IsND, not_not, eq_iff_vec_eq_zero, ←vec_sub_vec seg₂.1, hx, hy, ←sub_smul, nd, sub_self,zero_smul]
  constructor
  by_cases h : 0 = x
  rw [←h, mul_zero, zero_add]
  apply mul_pos
  exact tpos
  apply lt_of_le_of_ne
  exact ynonneg
  rw [h]
  symm
  exact ynex
  have : 0 < (1 - t) * x := by
    apply mul_pos
    linarith
    apply lt_of_le_of_ne xnonneg h
  apply lt_of_lt_of_le this
  simp only [le_add_iff_nonneg_right, gt_iff_lt]
  apply mul_nonneg
  linarith
  linarith
  constructor
  by_cases h : 1 = x
  simp only [←h, mul_one, sub_add, sub_lt_iff_lt_add, lt_add_iff_pos_right, sub_pos, gt_iff_lt]
  nth_rw 2[←mul_one t]
  apply mul_lt_mul_of_pos_left
  apply lt_of_le_of_ne
  exact yle1
  rw [h]
  exact ynex
  exact tpos
  have :(1 - t) * x + t * y < (1 - t) + t * y := by
    simp only [add_lt_add_iff_right, gt_iff_lt, sub_pos]
    nth_rw 2 [← mul_one (1 - t)]
    apply mul_lt_mul_of_pos_left
    apply lt_of_le_of_ne xle1
    symm
    exact h
    linarith
  apply lt_of_lt_of_le this
  rw [sub_add, tsub_le_iff_right, le_add_iff_nonneg_right, sub_nonneg, ←mul_one t,mul_assoc, one_mul]
  apply mul_le_mul _ yle1 ynonneg
  linarith
  linarith
  rw [ht, ←sub_eq_zero, Seg.toVec, ←sub_smul, smul_eq_zero]
  left
  ring

/-- Given a segment and a ray, if the source and the target of the segment both lie on the ray, and if $A$ is a point on the segment, then $A$ lies on the ray. -/
theorem every_pt_lies_on_ray_of_source_and_target_lies_on_ray {seg : Seg P} {ray : Ray P} (h₁ : seg.source LiesOn ray) (h₂: seg.target LiesOn ray) {A : P} (ha : A LiesOn seg) : A LiesOn ray :=by
  rcases h₁ with ⟨x, xnonneg, hx⟩
  rcases h₂ with ⟨y, ynonneg, hy⟩
  rcases ha with ⟨t, tnonneg, tleone, ht⟩
  rw [←vec_add_vec seg.source ray.source, ←vec_add_vec seg.source ray.source seg.target, ←neg_vec, hx, hy, neg_add_eq_iff_eq_add, ←neg_smul, smul_add, smul_smul, smul_smul, ←add_smul, ←add_smul, ←add_assoc, mul_neg, ←sub_eq_add_neg, ←one_mul x, ←mul_assoc, ←sub_mul,mul_one] at ht
  use ( (1- t) * x + t * y)
  constructor
  apply add_nonneg
  apply mul_nonneg
  linarith
  linarith
  apply mul_nonneg
  linarith
  linarith
  rw [ht]

/-- Given a segment and a ray, if the source and the target of the segment both lie in the interior of the ray, and if $A$ is a point on the segment, then $A$ lies in the interior of the ray.-/
theorem every_pt_lies_int_ray_of_source_and_target_lies_int_ray {seg : Seg P} {ray : Ray P} (h₁ : seg.source LiesInt ray) (h₂ : seg.target LiesInt ray) {A : P} (ha : A LiesOn seg) : A LiesInt ray := by
  rcases (Ray.lies_int_iff.mp h₁) with ⟨x, xpos, hx⟩
  rcases (Ray.lies_int_iff.mp h₂) with ⟨y, ypos, hy⟩
  apply Ray.lies_int_iff.mpr
  rcases ha with ⟨t, tnonneg, tle1, ht⟩
  rw [←vec_sub_vec ray.source, ←vec_sub_vec ray.source seg.source seg.target, hx, hy, sub_eq_iff_eq_add, ←sub_smul,smul_smul, ←add_smul, mul_sub] at ht
  use (t * y + (1 - t) * x)
  constructor
  by_cases h : 0 = t
  rw [←h]
  linarith
  apply lt_of_lt_of_le (mul_pos (lt_of_le_of_ne tnonneg h) ypos)
  simp only [le_add_iff_nonneg_right, gt_iff_lt, sub_pos]
  apply mul_nonneg
  linarith
  linarith
  rw [ht, ←sub_eq_zero, ←sub_smul, smul_eq_zero]
  left
  ring

/-- Given a segment and a ray, if the source and the target of the segment both lie on the ray, and if $A$ is a point in the interior of the segment, then $A$ lies in the interior of the ray. -/
theorem every_int_pt_lies_int_ray_of_source_and_target_lies_on_ray {seg : Seg P} {ray : Ray P} (h₁ : seg.source LiesOn ray) (h₂ : seg.target LiesOn ray) {A : P} (ha : A LiesInt seg) : A LiesInt ray := by
  rcases h₁ with ⟨x, xnonneg, hx⟩
  rcases h₂ with ⟨y, ynonneg, hy⟩
  rcases Seg.lies_int_iff.mp ha with ⟨nd, t, tpos, tlt1, ht⟩
  simp only [Seg.toVec, ←vec_sub_vec ray.1 seg.1, hx, hy, sub_eq_iff_eq_add, ←sub_smul, smul_smul, ←add_smul] at ht
  apply Ray.lies_int_iff.mpr
  use (1 - t) * x + t * y
  have ynex : y ≠ x := by
    contrapose! nd
    rw [Seg.IsND, not_not, eq_iff_vec_eq_zero, ←vec_sub_vec ray.1, hx, hy, ←sub_smul, nd, sub_self, zero_smul]
  constructor
  by_cases h : 0 = x
  rw [←h, mul_zero, zero_add]
  apply mul_pos
  exact tpos
  apply lt_of_le_of_ne
  exact ynonneg
  rw [h]
  symm
  exact ynex
  have : 0 < (1 - t) * x := by
    apply mul_pos
    linarith
    apply lt_of_le_of_ne xnonneg h
  apply lt_of_lt_of_le this
  simp only [le_add_iff_nonneg_right, gt_iff_lt]
  apply mul_nonneg
  linarith
  linarith
  rw [ht, ←sub_eq_zero, ←sub_smul, smul_eq_zero]
  left
  ring

/-- Given two rays $ray_1$ and $ray_2$ with same direction, if the source of $ray_1$ lies on $ray_2$, and if $A$ is a point on $ray_1$, then $A$ lies on $ray_2$. -/
theorem every_pt_lies_on_ray_of_source_lies_on_ray_and_same_dir {ray₁ ray₂ : Ray P} (e : ray₁.toDir = ray₂.toDir) (h : ray₁.source LiesOn ray₂) {A : P} (ha : A LiesOn ray₁) : A LiesOn ray₂ := by
  rcases h with ⟨x,xnonneg,hx⟩
  rcases ha with ⟨t,tnonneg,ht⟩
  use x + t
  constructor
  linarith
  rw [←vec_add_vec ray₂.source ray₁.source A, hx, ht, e, add_smul]

/-- Given two rays $ray_1$ and $ray_2$ with same direction, if the source of $ray_1$ lies in the interior of $ray_2$, and if $A$ is a point on $ray_1$, then $A$ lies in the interior of $ray_2$. -/
theorem every_pt_lies_int_ray_of_source_lies_int_ray_and_same_dir {ray₁ ray₂ : Ray P} (e : ray₁.toDir = ray₂.toDir) (h : ray₁.source LiesInt ray₂) {A : P} (ha : A LiesOn ray₁) : A LiesInt ray₂ := by
  apply Ray.lies_int_iff.mpr
  rcases ha with ⟨t, tnonneg, ht⟩
  rcases Ray.lies_int_iff.mp h with ⟨x, xpos, hx⟩
  rw [e] at ht
  use x + t
  constructor
  linarith
  rw [←vec_add_vec ray₂.1 ray₁.1, hx, ht, add_smul]

/--Given a nondegenerate segment $Segnd$ and a point $A$ lies in the interior of it. Then the direction of the nondegenerate segment from the source of $Segnd$ to $A$ equals the direction of $Segnd$.  -/
theorem SegND.source_pt_toDir_eq_toDir_of_lies_int {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd seg_nd.source A h.ne_source).toDir = seg_nd.toDir := by
  show (RAY seg_nd.source A h.ne_source).toDir = seg_nd.toRay.toDir
  congr 1
  have : A LiesInt (seg_nd.toRay) := by
    exact lies_int_toRay_of_lies_int h
  exact Ray.pt_pt_eq_ray this

end lieson_compatibility



section reverse
/-!
## (6) Reverse
-/

/-- Given a ray, this function returns the ray with the same source but with reversed direction. -/
@[pp_dot, simps]
def Ray.reverse (ray : Ray P) : Ray P where
  source := ray.source
  toDir := - ray.toDir

/-- Given a segment $AB$, this function returns its reverse, i.e. the segment $BA$. -/
@[pp_dot, simps]
def Seg.reverse (seg : Seg P) : Seg P where
  source := seg.target
  target := seg.source

/-- The reverse of segment $AB$ is the segment $BA$. -/
@[simp]
theorem seg_rev {A B : P} : (SEG A B).reverse = SEG B A := rfl

/-- If a segment is nondegenerate, so is its reverse segment. -/
theorem nd_of_rev_of_nd {seg : Seg P} (nd : seg.IsND) : seg.reverse.IsND := nd.symm

/-- Given a nondegenerate segment $AB$, this function returns the reversed nondegenerate segment $BA$. -/
def SegND.reverse (seg_nd : SegND P) : SegND P := ⟨seg_nd.1.reverse, nd_of_rev_of_nd seg_nd.2⟩

/-- The reverse of a nondegenerate segment $AB$ is the nondegenerate segment $BA$. -/
@[simp]
theorem seg_nd_rev {A B : P} [_h : PtNe B A] : (SEG_nd A B).reverse = SEG_nd B A := rfl

/-- Given a nondegenerate segment, first viewing it as a segment and then reversing it is the same as first reversing it and then viewing it as a segment. -/
@[simp]
theorem SegND.rev_toseg_eq_toseg_rev {seg_nd : SegND P} :  seg_nd.reverse.1 = seg_nd.1.reverse := rfl

/-- Given a ray, the source of the reversed ray is the source of the ray. -/
@[simp]
theorem Ray.source_of_rev_eq_source {ray : Ray P} : ray.reverse.source = ray.source := rfl

/-- Reversing a ray twice gives back to the original ray. -/
@[simp]
theorem Ray.rev_rev_eq_self {ray : Ray P} : ray.reverse.reverse = ray := by
  simp only [reverse, neg_neg]

/-- Reversing a segment twice gives back to the original segment. -/
@[simp]
theorem Seg.rev_rev_eq_self {seg : Seg P} : seg.reverse.reverse = seg := rfl

/-- Reversing a nondegenerate segment twice gives back to the original nondegenerate segment. -/
@[simp]
theorem SegND.rev_rev_eq_self {seg_nd : SegND P} : seg_nd.reverse.reverse = seg_nd := rfl

/--Given a ray, the direction of the reversed ray is the negative of the direction of the ray. -/
@[simp]
theorem Ray.toDir_of_rev_eq_neg_toDir {ray : Ray P} : ray.reverse.toDir = - ray.toDir := rfl

/-- Given a ray, the direction vector of the reversed ray is the negative of the direction vector of the ray. -/
theorem Ray.unitVecND_of_rev_eq_neg_unitVecND {ray : Ray P} : ray.reverse.toDir.unitVecND = - ray.toDir.unitVecND := by
  simp only [reverse_toDir, Dir.neg_unitVecND]

/-- Given a ray, the direction vector of the reversed ray is the negative of the direction vector of the ray. -/
theorem Ray.unitVec_of_rev_eq_neg_unitVec {ray : Ray P} : ray.reverse.toDir.unitVec = - ray.toDir.unitVec := by
  simp only [reverse_toDir, Dir.neg_unitVec]

/-- Given a ray, the projective direction of the reversed ray is the same as that of the ray. -/
@[simp]
theorem Ray.toProj_of_rev_eq_toProj {ray : Ray P} : ray.reverse.toProj = ray.toProj := by
  apply Dir.toProj_eq_toProj_iff.mpr
  right
  rfl

/-- Given a segment, the vector associated to the reversed segment is the negative of the vector associated to the segment. -/
@[simp]
theorem Seg.toVec_of_rev_eq_neg_toVec {seg : Seg P} : seg.reverse.toVec = - seg.toVec := by
  simp only [reverse,toVec,neg_vec]

/-- Given a nondegenerate segment, the nondegenerate vector associated to the reversed nondegenerate segment is the negative of the nondegenerate vector associated to the nondegenerate segment. -/
@[simp]
theorem SegND.toVecND_of_rev_eq_neg_toVecND {seg_nd : SegND P} : seg_nd.reverse.toVecND = - seg_nd.toVecND := by
  apply Subtype.eq
  apply Seg.toVec_of_rev_eq_neg_toVec

/-- Given a nondegenerate segment, the direction of the reversed nondegenerate segment is the negative direction of the nondegenerate segment. -/
@[simp]
theorem SegND.toDir_of_rev_eq_neg_toDir {seg_nd : SegND P} : seg_nd.reverse.toDir = - seg_nd.toDir := by
  rw [toDir, toDir]
  simp only [toVecND_of_rev_eq_neg_toVecND, VecND.neg_toDir]

/-- Given a nondegenerate segment, the projective direction of the reversed nondegenerate segment is the same projective direction of the nondegenerate segment. -/
@[simp]
theorem SegND.toProj_of_rev_eq_toProj {seg_nd : SegND P} : seg_nd.reverse.toProj = seg_nd.toProj := by
  apply Dir.toProj_eq_toProj_iff.mpr
  simp only [toVecND_of_rev_eq_neg_toVecND, VecND.neg_toDir, or_true]

/-- The source of a ray lies on the reverse of the ray. -/
theorem Ray.source_lies_on_rev {ray : Ray P} : ray.source LiesOn ray.reverse := source_lies_on

/-- The source of a segment lies on the reverse of the segment. -/
theorem Seg.source_lies_on_rev {seg : Seg P} : seg.source LiesOn seg.reverse := target_lies_on

/-- The target of a segment lies on the reverse of the segment. -/
theorem Seg.target_lies_on_rev {seg : Seg P} : seg.target LiesOn seg.reverse := source_lies_on

/-- The source of a nondegenerate segment lies on the reverse of the segment. -/
theorem SegND.source_lies_on_rev {seg_nd : SegND P} : seg_nd.source LiesOn seg_nd.reverse := target_lies_on

/-- The target of a nondegenerate segment lies on the reverse of the segment.-/
theorem SegND.target_lies_on_rev {seg_nd : SegND P} : seg_nd.target LiesOn seg_nd.reverse := source_lies_on

/-- Given a ray, a point $X$ lies on the ray or its reverse if and only if $X$ lies on the reverse ray or the reverse of reverse ray. -/
theorem Ray.lies_on_rev_or_lies_on_iff {X : P} {ray : Ray P} : X LiesOn ray ∨ X LiesOn ray.reverse ↔ X LiesOn ray.reverse ∨ X LiesOn ray.reverse.reverse := by
  simp only [Ray.rev_rev_eq_self]
  exact ⟨ Or.symm, Or.symm ⟩

/-- If a point lies on a segment, then it lies on the reversed segment. -/
theorem Seg.lies_on_rev_of_lies_on {A : P} {seg : Seg P} : A LiesOn seg → A LiesOn seg.reverse := by
  unfold lies_on Fig.carrier instIntFigSeg
  simp only [Set.setOf_mem_eq]
  intro h
  rcases h with ⟨t, ⟨ h1, ⟨ h2, h3 ⟩⟩⟩
  use 1-t
  constructor
  · linarith
  · constructor
    · linarith
    · simp only [reverse]
      rw [(vec_add_vec seg.target seg.source A).symm, h3, ← neg_vec seg.target seg.source, sub_smul]
      rw [one_smul, smul_neg, sub_eq_add_neg]

/-- A point lies on the reverse of a segment if and only if it lies on the segment. -/
@[simp]
theorem Seg.lies_on_rev_iff_lies_on {A : P} {seg : Seg P} : A LiesOn seg.reverse ↔ A LiesOn seg := ⟨ Seg.lies_on_rev_of_lies_on (seg := seg.reverse), Seg.lies_on_rev_of_lies_on ⟩

/-- A point lies in the interior of the reverse of a segment if and only if it lies in the interior of the segment. -/
@[simp]
theorem Seg.lies_int_rev_iff_lies_int {A : P} {seg : Seg P} : A LiesInt seg.reverse ↔ A LiesInt seg := ⟨
  fun ⟨ha, nonsource, nontarget⟩ ↦ ⟨Seg.lies_on_rev_iff_lies_on.mp ha, nontarget,nonsource⟩,
  fun ⟨ha, nonrevsource, nonrevtarget⟩ ↦ ⟨Seg.lies_on_rev_iff_lies_on.mpr ha, nonrevtarget,nonrevsource⟩⟩

/-- Given a nondegenerate segment, a point lies on the reverse of the segment if and only if it lies on the segment. -/
@[simp]
theorem SegND.lies_on_rev_iff_lies_on {A : P} {seg_nd : SegND P} : A LiesOn seg_nd.reverse ↔ A LiesOn seg_nd :=
  seg_nd.1.lies_on_rev_iff_lies_on

/-- Given a nondegenerate segment, a point lies in the interior of the reverse of the segment if and only if it lies in the interior of the segment. -/
@[simp]
theorem SegND.lies_int_rev_iff_lies_int {A : P} {seg_nd : SegND P} : A LiesInt seg_nd.reverse ↔ A LiesInt seg_nd :=
  seg_nd.1.lies_int_rev_iff_lies_int

/-- Given a ray, a point $A$ lies on the reverse of the ray if and only if there exists a nonpositive real number $t$ such that the vector from the source of the ray to $A$ is $t$ times the direction vector of the ray. -/
theorem pt_lies_on_ray_rev_iff_vec_opposite_dir {A : P} {ray : Ray P} : A LiesOn ray.reverse ↔ ∃ t : ℝ, (t ≤ 0) ∧ VEC ray.source A = t • ray.toDir.unitVec := by
  constructor <;>
  · rintro ⟨u, ⟨hu, h⟩⟩
    use -u
    try -- bug?
      dsimp at h
    rw [neg_smul]
    simp [hu, h]

/-- A point $A$ lies on the lines determined by a ray $ray$ (i.e. lies on the ray or its reverse) if and only if the vector from the source of ray to $A$ is a real multiple of the direction vector of $ray$. -/
theorem pt_lies_on_line_from_ray_iff_vec_parallel {A : P} {ray : Ray P} : (A LiesOn ray ∨ A LiesOn ray.reverse) ↔ ∃t : ℝ, VEC ray.source A = t • ray.toDir.unitVec := by
  constructor
  · rintro (⟨t, _, ha⟩ | ⟨t, _, ha⟩)
    · use t
    · use -t
      simpa using ha
  · rintro ⟨t, h⟩
    by_cases g : 0 ≤ t
    · exact .inl ⟨t, ⟨g, h⟩⟩
    · right
      use -t
      have : t ≤ 0 := by linarith
      simp only [Left.nonneg_neg_iff, this, Ray.reverse_source, h, Ray.reverse_toDir,
        Dir.neg_unitVec, smul_neg, neg_smul, neg_neg, and_self]

/-- A point is equal to the source of a ray if and only if it lies on the ray and it lies on the reverse of the ray. -/
theorem Ray.eq_source_iff_lies_on_and_lies_on_rev {A : P} {ray : Ray P} : A = ray.source ↔ (A LiesOn ray) ∧ (A LiesOn ray.reverse) := by
  constructor
  intro h
  constructor
  use 0
  simp only [le_refl, zero_smul, true_and]
  rw [h,vec_same_eq_zero]
  use 0
  simp only [le_refl, smul_neg, zero_smul, neg_zero, true_and,Ray.reverse]
  rw [h,vec_same_eq_zero]
  simp only [and_imp]
  rintro ⟨a,⟨anneg,h⟩⟩ ⟨b,⟨bnneg,h'⟩⟩
  replace h' : a + b = 0
  · simp only [Ray.reverse, smul_neg,h] at h'
    rw [←add_zero a,← sub_self b,add_sub,sub_smul] at h'
    simpa using h'
  have : a = 0 := by linarith
  subst this
  rw [zero_add] at h'
  subst h'
  rw [zero_smul] at h
  rw [eq_iff_vec_eq_zero, h]

/-- If a point lies in the interior of the reverse of a ray, then it does not lie on the ray. -/
theorem Ray.not_lies_on_of_lies_int_rev {A : P} {ray : Ray P} (liesint : A LiesInt ray.reverse) : ¬ A LiesOn ray := by
  by_contra h
  rcases liesint with ⟨h',nsource⟩
  have: A LiesOn ray.reverse:=by
    apply h'
  have : A=ray.source:=by
    rw [Ray.eq_source_iff_lies_on_and_lies_on_rev]
    constructor
    exact h
    exact this
  trivial

/-- If a point lies on of the reverse of a ray, then it does not lie in the interior of the ray. -/
theorem Ray.not_lies_int_of_lies_on_rev {A : P} {ray : Ray P} (liesint : A LiesOn ray.reverse) : ¬ A LiesInt ray := by
  by_contra h
  rw [← Ray.rev_rev_eq_self (ray:=ray)] at h
  have : ¬ (A LiesOn ray.reverse) := by
    apply not_lies_on_of_lies_int_rev
    exact h
  trivial

/-- A point lies on a nondegenerate segment $AB$ if and only if it lies on the ray $AB$ and on the reverse ray $BA$. -/
theorem lies_on_iff_lies_on_toRay_and_rev_toRay {X : P} {seg_nd : SegND P} : X LiesOn seg_nd.1 ↔ (X LiesOn seg_nd.toRay) ∧ (X LiesOn seg_nd.reverse.toRay) := by
  constructor
  intro liesonseg
  constructor
  apply SegND.lies_on_toRay_of_lies_on
  trivial
  apply SegND.lies_on_toRay_of_lies_on
  apply Seg.lies_on_rev_iff_lies_on.mp
  trivial
  rintro ⟨⟨a,anneg,h⟩,b,bnneg,h'⟩
  simp only [SegND.toRay] at h h'
  rw [SegND.toDir_of_rev_eq_neg_toDir, Dir.neg_unitVec] at h'
  simp only [SegND.reverse, Seg.reverse] at h'
  simp only [RayVector.coe_neg, smul_neg] at h'
  have asumbvec : (a + b) • seg_nd.toDir.unitVecND.1 = seg_nd.toVecND.1 := by
    have := vec_add_vec seg_nd.source X seg_nd.target
    rw [← neg_vec seg_nd.target X, h, h'] at this
    simpa [← add_smul] using this
  have asumbeqnorm : a + b = ‖seg_nd.toVecND‖ := by
    rw [SegND.toDir, ← seg_nd.toVecND.norm_smul_toDir_unitVec] at asumbvec
    exact smul_left_injective _ (VecND.ne_zero _) asumbvec
  use a * ‖seg_nd.toVecND‖⁻¹
  have : VEC seg_nd.1.source seg_nd.1.target = seg_nd.toVecND :=by
    rfl
  constructor
  apply mul_nonneg anneg
  simp only [ne_eq, inv_nonneg]
  linarith
  constructor
  rw [← mul_inv_cancel (VecND.norm_ne_zero seg_nd.toVecND)]
  apply mul_le_mul
  linarith
  trivial
  simp only[inv_nonneg]
  linarith
  linarith
  rw [h, mul_smul, this, ← VecND.norm_smul_toDir_unitVec seg_nd.toVecND, smul_smul, smul_smul, mul_assoc, inv_mul_cancel (VecND.norm_ne_zero seg_nd.toVecND), mul_one]

-- `This theorem really concerns about the total order on a line`
/-- Let $ray$ be a ray, and let $A$ be a point on $ray$, and $B$ a point on the reverse of $ray$. Then $A$ lies on the ray starting at $B$ in the same direction of $\ray$. -/
theorem lies_on_pt_toDir_of_pt_lies_on_rev {A B : P} {ray : Ray P} (hA : A LiesOn ray) (hB : B LiesOn ray.reverse) : A LiesOn Ray.mk B ray.toDir := by
  rcases hA with ⟨a, anonneg, ha⟩
  rcases hB with ⟨b, bnonneg, hb⟩
  dsimp at hb
  use a + b
  constructor; · linarith
  dsimp
  rw [add_smul, ← vec_sub_vec ray.source, ha, hb]
  simp only [Dir.neg_unitVec, smul_neg, sub_neg_eq_add]

/-- Given two rays $ray_1$ and $ray_2$ in same direction, the source of $ray_1$ lies on $ray_2$ if and only if the source of $ray_2$ lies on the reverse of $ray_1$. -/
theorem lies_on_iff_lies_on_rev_of_same_toDir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = ray₂.toDir) : ray₁.source LiesOn ray₂ ↔ ray₂.source LiesOn ray₁.reverse := by
  constructor
  · intro ⟨t, ht, eq⟩
    refine' ⟨t, ht, _⟩
    simp only [Ray.reverse_source, Ray.reverse_toDir, h, Dir.neg_unitVec, smul_neg, ← eq, neg_vec]
  · intro ⟨t, ht, eq⟩
    refine' ⟨t, ht, _⟩
    dsimp at eq
    simp only [← neg_vec ray₁.source, eq, h, Dir.neg_unitVec, smul_neg, neg_neg]

/-- Given two rays $ray_1$ and $ray_2$ in same direction, the source of $ray_1$ lies in the interior of $ray_2$ if and only if the source of $ray_2$ lies in the interior of the reverse of $ray_1$. -/
theorem lies_int_iff_lies_int_rev_of_same_toDir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = ray₂.toDir) : ray₁.source LiesInt ray₂ ↔ ray₂.source LiesInt ray₁.reverse := ⟨
  fun ⟨hl, ne⟩ ↦ ⟨(lies_on_iff_lies_on_rev_of_same_toDir h).mp hl, ne.symm⟩,
  fun ⟨hl, ne⟩ ↦ ⟨(lies_on_iff_lies_on_rev_of_same_toDir h).mpr hl, ne.symm⟩⟩

/-- Given two rays $ray_1$ and $ray_2$ in the opposite direction, the source of $ray_1$ lies on $ray_2$ if and only if the source of $ray_2$ lies on $ray_1$. -/
theorem lies_on_iff_lies_on_of_neg_toDir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = - ray₂.toDir) : ray₁.source LiesOn ray₂ ↔ ray₂.source LiesOn ray₁ := by
  constructor
  · intro ⟨t, ht, eq⟩
    refine' ⟨t, ht, _⟩
    simp only [h, Dir.neg_unitVec, smul_neg, ← eq, neg_vec]
  · intro ⟨t, ht, eq⟩
    refine' ⟨t, ht, _⟩
    simp only [← neg_vec ray₁.source, eq, h, Dir.neg_unitVec, smul_neg, neg_neg]

/-- Given two rays $ray_1$ and $ray_2$ in the opposite direction, the source of $ray_1$ lies in the interior of $ray_2$ if and only if the source of $ray_2$ lies in the interior of $ray_1$. -/
theorem lies_int_iff_lies_int_of_neg_toDir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = - ray₂.toDir) : ray₁.source LiesInt ray₂ ↔ ray₂.source LiesInt ray₁ := ⟨
  fun ⟨hl, ne⟩ ↦ ⟨(lies_on_iff_lies_on_of_neg_toDir h).mp hl, ne.symm⟩,
  fun ⟨hl, ne⟩ ↦ ⟨(lies_on_iff_lies_on_of_neg_toDir h).mpr hl, ne.symm⟩⟩

/-- Given two rays $ray_1$ and $ray_2$ in the opposite direction, the source of $ray_1$ lies on the reverse of $ray_2$ if and only if the source of $ray_2$ lies on the reverse of $ray_1$. -/
theorem lies_on_rev_iff_lies_on_rev_of_neg_toDir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = - ray₂.toDir) : ray₁.source LiesOn ray₂.reverse ↔ ray₂.source LiesOn ray₁.reverse := by
  have h₁ : ray₁.reverse.toDir = - ray₂.reverse.toDir := by
    apply neg_eq_iff_eq_neg.mp
    simp only [Ray.toDir_of_rev_eq_neg_toDir, neg_neg, h]
  apply lies_on_iff_lies_on_of_neg_toDir h₁

/-- Given two rays $ray_1$ and $ray_2$ in the opposite direction, the source of $ray_1$ lies in the interior of the reverse of $ray_2$ if and only if the source of $ray_2$ lies in the interior of the reverse of $ray_1$. -/
theorem lies_int_rev_iff_lies_int_rev_of_neg_toDir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = - ray₂.toDir) : ray₁.source LiesInt ray₂.reverse ↔ ray₂.source LiesInt ray₁.reverse := ⟨
  fun ⟨hl, ne⟩ ↦ ⟨(lies_on_rev_iff_lies_on_rev_of_neg_toDir h).mp hl, ne.symm⟩,
  fun ⟨hl, ne⟩ ↦ ⟨(lies_on_rev_iff_lies_on_rev_of_neg_toDir h).mpr hl, ne.symm⟩⟩

/-- Given a ray, a point $A$ lies on the ray or its reverse ray if and only if there exists a real number $t$ such that the vector from the source of the ray to $A$ is $t$ times the direction of the ray. -/
theorem lies_on_or_rev_iff_exist_real_vec_eq_smul {A : P} {ray : Ray P} : (A LiesOn ray ∨ A LiesOn ray.reverse) ↔ ∃ t : ℝ, VEC ray.source A = t • ray.toDir.unitVecND := by
  constructor
  · intro h
    rcases h with ⟨t, _, eq⟩ | ⟨t, _, eq⟩
    · use t, eq
    · use - t
      simpa using eq
  · intro h
    choose t ht using h
    by_cases k : 0 ≤ t
    · left
      exact ⟨t,k,ht⟩
    right
    let u := -t
    simp only [not_le] at k
    have hu : VEC ray.reverse.1 A = u • ray.reverse.toDir.unitVecND := by
      simp only [Ray.reverse_source, ne_eq, Ray.reverse_toDir, Dir.neg_unitVecND, RayVector.coe_neg,
        Dir.coe_unitVecND, smul_neg, neg_smul, neg_neg]
      exact ht
    exact ⟨-t, neg_nonneg.mpr k.le, hu⟩

/-- Given two distinct points $A$ and $B$ and a ray, if both $A$ and $B$ lies on the ray or its reversed ray, then the projective direction of the ray is the same as the projective direction of the ray $AB$. -/
theorem ray_toProj_eq_mk_pt_pt_toProj {A B : P} {ray : Ray P} [h : PtNe B A] (ha : A LiesOn ray ∨ A LiesOn ray.reverse) (hb : B LiesOn ray ∨ B LiesOn ray.reverse) : ray.toProj = (RAY A B).toProj := by
  rcases lies_on_or_rev_iff_exist_real_vec_eq_smul.mp ha with ⟨ta, eqa⟩
  rcases lies_on_or_rev_iff_exist_real_vec_eq_smul.mp hb with ⟨tb, eqb⟩
  have heq : VEC A B = (tb - ta) • ray.2.unitVecND := by rw [← vec_sub_vec _ A B, eqa, eqb, sub_smul]
  have h0 : tb - ta ≠ 0 := (smul_ne_zero_iff.mp (heq.symm.trans_ne (vsub_ne_zero.mpr Fact.out))).1
  apply Dir.toProj_eq_toProj_iff_unitVec.mpr
  use (tb - ta)⁻¹ * ‖VEC_nd A B‖
  simp only [← (inv_smul_eq_iff₀ h0).mpr heq, Ray.mkPtPt_toDir, mul_smul,
    VecND.norm_smul_toDir_unitVec, ne_eq, VecND.coe_mkPtPt]

/--Given a nondegenerate segment $Segnd$ and a point $A$ lies in the interior of it. Then the direction of the nondegenerate segment from $A$ to the target of $Segnd$ equals the direction of $Segnd$.  -/
theorem SegND.pt_target_toDir_eq_toDir_of_lies_int {seg_nd : SegND P} {A : P} (h : A LiesInt seg_nd) : (SEG_nd A seg_nd.target h.ne_target.symm).toDir = seg_nd.toDir := by
  show (VEC_nd A seg_nd.target h.ne_target.symm).toDir = (VEC_nd seg_nd.source seg_nd.target seg_nd.2).toDir
  haveI : PtNe A seg_nd.target := ⟨h.3⟩
  have l2: (VEC_nd A seg_nd.target h.3.symm).toDir = - (VEC_nd seg_nd.target A h.3).toDir := by
    rw [← VecND.neg_toDir]
    congr
    rw [VecND.neg_vecND]
  let s1:= seg_nd.reverse
  have h1: A LiesInt s1:= by
    exact lies_int_rev_iff_lies_int.mpr h
  have l22: (VEC_nd seg_nd.target A h.3).toDir = s1.toDir:= by
    rw[← SegND.source_pt_toDir_eq_toDir_of_lies_int h1]
    rfl
  rw [l2, l22, ← VecND.neg_toDir]
  congr
  simp only [toVecND_of_rev_eq_neg_toVecND, neg_neg]
  rfl
/--Given a nondegenerate segment $Segnd$ and a point $A$ lies in the interior of it. Then the direction of the nondegenerate vector from $A$ to the source of $Segnd$ equals the opposite direction of the nondegenerate vector from $A$ to the target of $Segnd$.  -/
theorem SegND.toDir_eq_neg_toDir_of_lies_int {A : P} {seg_nd : SegND P} (h : A LiesInt seg_nd) : (VEC_nd A seg_nd.source h.2.symm).toDir = - (VEC_nd A seg_nd.target h.3.symm).toDir := by
  haveI : PtNe A seg_nd.source := ⟨h.2⟩
  rw [← VecND.neg_vecND, VecND.neg_toDir]
  exact neg_inj.mpr <|
    (source_pt_toDir_eq_toDir_of_lies_int h).trans (pt_target_toDir_eq_toDir_of_lies_int h).symm

end reverse

section extension
/-!
## (7) Extension
-/

namespace SegND

/-- Define the extension ray of a nondegenerate segment to be the ray whose origin is the target of the segment whose direction is the same as that of the segment. -/
def extension (seg_nd : SegND P) : Ray P where
  source := seg_nd.target
  toDir := seg_nd.toDir

/-- The extension of a nondegenerate segment is the same as first reverse the segment, then take the ray associated to the segment, and finally reverse the ray. -/
theorem extn_eq_rev_toRay_rev {seg_nd : SegND P} : seg_nd.extension = seg_nd.reverse.toRay.reverse := by
  ext : 1
  · rfl
  · simp only [Ray.toDir_of_rev_eq_neg_toDir, SegND.toRay_toDir_eq_toDir, SegND.toDir_of_rev_eq_neg_toDir, neg_neg]
    rfl

/-- The extension of the reverse of a nondegenerate segment is the same as the reverse of the ray associated to the segment. -/
theorem rev_extn_eq_toRay_rev {seg_nd : SegND P} : seg_nd.reverse.extension = seg_nd.toRay.reverse :=
  seg_nd.reverse.extn_eq_rev_toRay_rev

/-- The direction of the extension ray of a nondegenerate segment is the same as the direction of the segment. -/
@[simp]
theorem extn_toDir {seg_nd : SegND P} : seg_nd.extension.toDir = seg_nd.toDir := by rfl

/-- The projective direction of the extension ray of a nondegenerate segment is the same as the projective direction of the segment. -/
@[simp]
theorem extn_toProj {seg_nd : SegND P} : seg_nd.extension.toProj = seg_nd.toProj := by rfl

/-- Given a nondegenerate segment, a point is equal to its target if and only if it lies on the segment and its extension ray. -/
theorem eq_target_iff_lies_on_lies_on_extn {A : P} {seg_nd : SegND P} : (A LiesOn seg_nd) ∧ (A LiesOn seg_nd.extension) ↔ A = seg_nd.target := by
  constructor
  · intro ⟨ h1, h2 ⟩
    rw [extn_eq_rev_toRay_rev] at h2
    rw [← SegND.lies_on_rev_iff_lies_on] at h1
    exact Ray.eq_source_iff_lies_on_and_lies_on_rev.mpr ⟨ (SegND.lies_on_toRay_of_lies_on h1), h2 ⟩
  · intro h
    rw [h]
    exact ⟨SegND.target_lies_on, Ray.source_lies_on⟩

/-- Given a nondegenerate segment $AB$, if a point $X$ belongs to the interior of the extension ray of $AB$, then $B$ lies in the interior of $AX$. -/
theorem target_lies_int_seg_source_pt_of_pt_lies_int_extn {X : P} {seg_nd : SegND P}
(liesint : X LiesInt seg_nd.extension) : seg_nd.target LiesInt SEG seg_nd.source X  := by
  rcases liesint with ⟨⟨a, anonneg, ha⟩, nonsource⟩
  have raysourcesegtarget:seg_nd.1.target = seg_nd.extension.1 := by
    rfl
  have sourcetargetA : VEC seg_nd.1.source seg_nd.1.target + VEC seg_nd.1.target X =
  VEC seg_nd.1.source X := by
    rw [vec_add_vec]
  have vec_ndtoVec : VEC seg_nd.1.source seg_nd.1.target = seg_nd.toVecND.1 := by
    rfl
  have apos:0 < a := by
    contrapose! nonsource
    have : a = 0 := by
      linarith
    rw [this] at ha
    simp only [smul_neg, zero_smul, neg_zero] at ha
    apply eq_iff_vec_eq_zero.mpr
    exact ha
  have raysourcesource : seg_nd.extension.source = seg_nd.1.target := by
    rfl
  have seg_pos : 0 < norm (SegND.toVecND seg_nd) := by
    simp only [VecND.norm_pos]
  have seg_nonzero : norm (SegND.toVecND seg_nd) ≠ 0 := by linarith
  have aseg_pos : 0 <norm (SegND.toVecND seg_nd) + a:=by
    linarith
  have aseg_nonzero : norm (SegND.toVecND seg_nd) + a ≠ 0:=by
    linarith
  constructor
  use (norm (SegND.toVecND seg_nd)) * (norm (seg_nd.toVecND) + a)⁻¹
  constructor
  apply mul_nonneg
  linarith[seg_pos]
  norm_num
  linarith
  constructor
  rw [←mul_inv_cancel aseg_nonzero]
  apply mul_le_mul
  linarith
  linarith
  norm_num
  linarith
  linarith
  simp only [Seg.target]
  rw [←raysourcesegtarget] at ha
  rw [←sourcetargetA, ha, vec_ndtoVec]
  have raydir : seg_nd.extension.toDir.unitVec = seg_nd.toVecND.toDir.unitVec := by
    exact rfl
  rw [raydir, ←VecND.norm_smul_toDir_unitVec (seg_nd.toVecND), ←add_smul,
  ← mul_smul,mul_assoc,inv_mul_cancel,mul_one]
  linarith
  exact seg_nd.2
  rw [←raysourcesegtarget] at nonsource
  symm
  exact nonsource


/-- If a point lies on the ray associated to a segment, then either it lies on the segment or it lies on the extension ray of the segment. -/
theorem lies_on_seg_nd_or_extension_of_lies_on_toRay {seg_nd : SegND P} {A : P} (h : A LiesOn seg_nd.toRay) : A LiesOn seg_nd ∨ A LiesOn seg_nd.extension := by
  rcases h with ⟨t, tpos, eq⟩
  let v : VecND := seg_nd.toVecND
  by_cases h : t > ‖v.1‖
  · refine' Or.inr ⟨t - ‖v.1‖, sub_nonneg.mpr (le_of_lt h), _⟩
    dsimp at eq ⊢
    rw [sub_smul, ← eq]
    refine' eq_sub_of_add_eq (add_eq_of_eq_sub' _)
    rw [vec_sub_vec']
    exact v.norm_smul_toDir_unitVec
  · have eq : VEC seg_nd.1.1 A = t • v.toDir.unitVecND := eq
    exact Or.inl ⟨t * ‖v.1‖⁻¹, mul_nonneg tpos (inv_nonneg.mpr (norm_nonneg v.1)),
      (mul_inv_le_iff (norm_pos_iff.2 v.2)).mpr (by rw [mul_one]; exact not_lt.mp h), by
      simp [eq, mul_smul]
      rfl⟩

/--If a point lies on the extension ray associated to a nondegenerate segment, then it lies on the
interior of the ray associated to the segment-/
theorem lies_int_toRay_of_lies_on_extn {seg_nd : SegND P} (A : P) (h : A LiesOn seg_nd.extension) : A LiesInt seg_nd.toRay := by
  by_cases H : A = seg_nd.target
  rw [H]
  apply SegND.target_lies_int_toRay
  have H1: A LiesInt seg_nd.extension := by
    rw [Ray.lies_int_def]; constructor
    apply h
    exact H
  have H2: seg_nd.target LiesInt SEG seg_nd.source A := by
    exact target_lies_int_seg_source_pt_of_pt_lies_int_extn H1
  by_cases L : A ≠ seg_nd.source
  haveI : PtNe A seg_nd.source:= ⟨ L⟩
  have H4: seg_nd.toRay = (SEG_nd seg_nd.source A).toRay := by
    apply (SEG_nd seg_nd.source A).toRay.pt_pt_eq_ray
    exact lies_int_toRay_of_lies_int H2
  rw [H4]
  apply SegND.target_lies_int_toRay
  rw [ne_eq, not_not] at L
  have H5: A LiesOn seg_nd := by
    rw [L]
    exact source_lies_on
  have H6: A = seg_nd.target := by
    rw [← eq_target_iff_lies_on_lies_on_extn]
    exact ⟨H5, h⟩
  by_contra
  exact H H6

theorem not_lies_int_rev_extn_of_lies_on {A : P} {seg_nd : SegND P} (lieson : A LiesOn seg_nd.1) : ¬ A LiesInt seg_nd.reverse.extension := by
  apply Ray.not_lies_int_of_lies_on_rev
  rw [rev_extn_eq_toRay_rev, Ray.rev_rev_eq_self]
  exact lies_on_toRay_of_lies_on lieson

theorem not_lies_int_extn_of_lies_on {A : P} {seg_nd : SegND P} (lieson : A LiesOn seg_nd.1) : ¬ A LiesInt seg_nd.extension := by
  rw [← seg_nd.rev_rev_eq_self]
  exact not_lies_int_rev_extn_of_lies_on (Seg.lies_on_rev_of_lies_on lieson)

end SegND

namespace Ray

-- Define the extpoint of a ray to be a point lies on the ray.toLine which has given distance to the ray.source
def extpoint (l : Ray P) (t : ℝ) : P := t • l.toDir.unitVec +ᵥ l.source

theorem extpoint_lies_on_of_nonneg {r : Ray P} {t : ℝ} (ht : 0 ≤ t) : r.extpoint t LiesOn r := by
  rw [extpoint, Ray.lies_on_iff]
  use t
  constructor
  apply ht
  simp only [vec_of_pt_vadd_pt_eq_vec]

theorem lies_on_of_eq_nonneg_extpoint {r : Ray P} {A : P} {t : ℝ} (ht : 0 ≤ t) (h : A = Ray.extpoint r t) : A LiesOn r := by
  rw [h]
  exact extpoint_lies_on_of_nonneg ht

theorem extpoint_lies_int_of_pos {r : Ray P} {t : ℝ} (ht : 0 < t) : r.extpoint t LiesInt r := by
  rw [extpoint, Ray.lies_int_iff]
  use t
  constructor
  apply ht
  simp only [vec_of_pt_vadd_pt_eq_vec]

theorem lies_int_of_eq_pos_extpoint {r : Ray P} {A : P} {t : ℝ} (ht : 0 < t) (h : A = Ray.extpoint r t) : A LiesInt r := by
  rw[h]
  exact extpoint_lies_int_of_pos ht

theorem dist_of_extpoint {r : Ray P}  {t : ℝ} (ht : 0 ≤ t) : dist r.source (r.extpoint t) = t := by
  rw [dist_comm, NormedAddTorsor.dist_eq_norm', extpoint, vadd_vsub, norm_smul,
  Dir.norm_unitVec, mul_one]
  exact Real.norm_of_nonneg ht

theorem dist_eq_of_eq_extpoint {r : Ray P} {A : P} {t : ℝ} (ht : 0 ≤ t) (h : A = Ray.extpoint r t) : dist r.source A = t := by
  rw[h]
  exact dist_of_extpoint ht

end Ray

end extension

section length
/-!
## (8) Length
-/

/-- This function gives the length of a given segment, which is the distance between the source and target of the segment. -/
@[pp_dot]
def Seg.length (seg : Seg P) : ℝ := dist seg.source seg.target

/-- The length of segment $AB$ is the same as the distance form $A$ to $B$. -/
@[simp]
theorem Seg.length_eq_dist {A B : P} : (SEG A B).length = dist A B := rfl

/-- The length of a given segment is the same as the norm of the vector associated to the segment. -/
theorem Seg.length_eq_norm_toVec {seg : Seg P} : seg.length = norm seg.toVec :=
  Eq.trans (dist_comm seg.source seg.target) (NormedAddTorsor.dist_eq_norm' _ _)

/-- This function defines the length of a nondegenerate segment, which is just the length of the segment. -/
abbrev SegND.length (seg_nd : SegND P) : ℝ := seg_nd.1.length

/-- Every segment has nonnegative length. -/
theorem Seg.length_nonneg {seg : Seg P} : 0 ≤ seg.length := dist_nonneg

/-- A segment has positive length if and only if it is nondegenerate. -/
theorem Seg.length_pos_iff_nd {seg : Seg P} : 0 < seg.length ↔ seg.IsND :=
  dist_pos.trans ne_comm
--norm_pos_iff.trans toVec_eq_zero_of_deg.symm.not

/-- The length of a given segment is nonzero if and only if the segment is nondegenerate. -/
theorem Seg.length_ne_zero_iff_nd {seg : Seg P} : 0 ≠ seg.length ↔ seg.IsND :=
  (ne_iff_lt_iff_le.mpr dist_nonneg).trans length_pos_iff_nd

/--  A nondegenerate segment has strictly positive length. -/
theorem SegND.length_pos {seg_nd : SegND P} : 0 < seg_nd.length := Seg.length_pos_iff_nd.mpr seg_nd.2

/-- Given a segment, the square of its length is equal to the the inner product of the associated vector with itself. -/
theorem Seg.length_sq_eq_inner_toVec_toVec {seg : Seg P} : seg.length ^ 2 = inner seg.toVec seg.toVec := by
  rw [Seg.length_eq_norm_toVec]
  exact (real_inner_self_eq_norm_sq (Seg.toVec seg)).symm

/-- The length of a segment is zero if and only if it is degenerate, i.e. it has same source and target. -/
theorem Seg.length_eq_zero_iff_deg {seg : Seg P} : seg.length = 0 ↔ (seg.target = seg.source) := by
  rw [Seg.length_eq_norm_toVec]
  exact ((toVec_eq_zero_of_deg).trans norm_eq_zero.symm).symm

/-- Reversing a segment does not change its length. -/
@[simp]
theorem Seg.length_of_rev_eq_length {seg : Seg P} : seg.reverse.length = seg.length := by
  rw [Seg.length_eq_norm_toVec]
  simp only [Complex.norm_eq_abs, Seg.toVec_of_rev_eq_neg_toVec, norm_neg]
  exact (seg.length_eq_norm_toVec).symm

/-- Reversing a segment does not change its length. -/
@[simp]
theorem SegND.length_of_rev_eq_length {seg_nd : SegND P} : seg_nd.reverse.length = seg_nd.length := by
  unfold SegND.length
  simp only [rev_toseg_eq_toseg_rev, Seg.length_of_rev_eq_length]

/-- The length of segment $AB$ is the same as the length of segment $BA$. -/
theorem length_of_rev_eq_length' {A B : P} : (SEG B A).length = (SEG A B).length := by
  rw [Seg.length_eq_norm_toVec]
  simp only [seg_toVec_eq_vec, Complex.norm_eq_abs]
  rw [← neg_vec, norm_neg]
  exact ((SEG A B).length_eq_norm_toVec).symm

/-- Given a segment and a point that lies on the segment, the additional point will separate the segment into two segments, whose lengths add up to the length of the original segment. -/
theorem length_eq_length_add_length {seg : Seg P} {A : P} (lieson : A LiesOn seg) : seg.length = (SEG seg.source A).length + (SEG A seg.target).length := by
  rcases lieson with ⟨t, ⟨a, b, c⟩⟩
  have h : VEC seg.source seg.target = VEC seg.source A + VEC A seg.target := by rw [vec_add_vec]
  have s : VEC A seg.target = (1 - t) • VEC seg.source seg.target := by
    rw [c] at h
    rw [sub_smul, one_smul]
    exact eq_sub_of_add_eq' h.symm
  rw [Seg.length_eq_norm_toVec, Seg.length_eq_norm_toVec, Seg.length_eq_norm_toVec, seg_toVec_eq_vec, seg_toVec_eq_vec, seg_toVec_eq_vec, c, s,
    norm_smul, norm_smul, ← add_mul, Real.norm_of_nonneg a, Real.norm_of_nonneg (sub_nonneg.mpr b)]
  linarith

theorem SegND.length_eq_length_add_length_of_lies_on_extn {seg_nd : SegND P} {A : P}
(h : A LiesOn seg_nd.extension) : (SEG seg_nd.source A).length =
seg_nd.1.length + (SEG seg_nd.target A).length := by
  have H1: seg_nd.target LiesOn SEG seg_nd.source A:= by
    by_cases H: A = seg_nd.target
    rw [H]
    exact Seg.target_lies_on
    have h1: A LiesInt seg_nd.extension:= by
      rw [Ray.lies_int_def]; constructor
      apply h
      exact H
    have h2: seg_nd.target LiesInt SEG seg_nd.source A := by
      exact target_lies_int_seg_source_pt_of_pt_lies_int_extn h1
    exact Seg.lies_on_of_lies_int h2
  rw [length_eq_length_add_length H1]

end length

section midpoint

/-!
## (9) Midpoint
-/

variable {X A : P}

/-- Given a segment $AB$, this function returns the midpoint of $AB$, defined as moving from $A$ by the vector $\overrightarrow{AB}/2$. -/
@[pp_dot]
def Seg.midpoint (seg : Seg P): P := (1 / 2 : ℝ) • seg.toVec +ᵥ seg.source

abbrev SegND.midpoint (seg_nd : SegND P): P := seg_nd.1.midpoint

theorem Seg.vec_source_midpt {seg : Seg P} : VEC seg.1 seg.midpoint = (1 / 2 : ℝ) • VEC seg.1 seg.2 := by
  simp only [midpoint, one_div, Complex.real_smul, Complex.ofReal_inv, vec_of_pt_vadd_pt_eq_vec]
  rfl

/-- Given a segment $AB$, the vector from the midpoint of $AB$ to $B$ is half of the vector from $A$ to $B$-/
theorem SegND.vec_source_midpt {seg_nd : SegND P} : VEC seg_nd.source seg_nd.midpoint = (1 / 2 : ℝ) • VEC seg_nd.source seg_nd.target := by
  simp only [SegND.midpoint]
  exact seg_nd.1.vec_source_midpt

theorem Seg.vec_midpt_target {seg : Seg P} : VEC seg.midpoint seg.2 = (1 / 2 : ℝ) • VEC seg.1 seg.2 := by
  rw [midpoint, ← vec_add_vec _ seg.1 _, ← neg_vec, vec_of_pt_vadd_pt_eq_vec]
  apply smul_right_injective _ (two_ne_zero' ℝ)
  simp [two_smul]

theorem SegND.vec_midpt_target {seg_nd : SegND P} : VEC seg_nd.midpoint seg_nd.target = (1 / 2 : ℝ) • VEC seg_nd.source seg_nd.target := by
  simp only [SegND.midpoint]
  exact seg_nd.1.vec_midpt_target

/-- Given a segment $AB$, the vector from $A$ to the midpoint of $AB$ is same as the vector from the midpoint of $AB$ to $B$ -/
theorem Seg.vec_midpt_eq {seg : Seg P} : VEC seg.1 seg.midpoint = VEC seg.midpoint seg.2 := by
  rw [seg.vec_source_midpt, seg.vec_midpt_target]

theorem SegND.vec_midpt_eq {seg_nd : SegND P} : VEC seg_nd.source seg_nd.midpoint = VEC seg_nd.midpoint seg_nd.target := by
  exact seg_nd.1.vec_midpt_eq

/-- Given a segment $AB$ and its midpoint P, the vector from $A$ to $P$ is same as the vector from $P$ to $B$ -/
theorem Seg.vec_eq_of_eq_midpt {seg : Seg P} (h : X = seg.midpoint) : VEC seg.1 X = VEC X seg.2 := by
  rw [h]
  exact seg.vec_midpt_eq

theorem SegND.vec_eq_of_eq_midpt {seg_nd : SegND P} (h : A = seg_nd.midpoint) : VEC seg_nd.source A = VEC A seg_nd.target := by
  exact seg_nd.1.vec_eq_of_eq_midpt h

/-- Given a segment $AB$ and a point P, if vector $\overrightarrow{AP}$ is half of vector $\overrightarrow{AB}$, P is the midpoint of $AB$. -/
theorem Seg.midpt_of_vector_from_source {seg : Seg P} (h : VEC seg.1 A = (1 / 2 : ℝ) • VEC seg.1 seg.2) : A = seg.midpoint := by
  rw [← start_vadd_vec_eq_end seg.1 A, h, Seg.midpoint]
  norm_num

theorem SegND.midpt_of_vector_from_source {seg_nd : SegND P} (h : VEC seg_nd.source A = (1 / 2 : ℝ) • VEC seg_nd.source seg_nd.target) : A = seg_nd.midpoint :=
  Seg.midpt_of_vector_from_source h

/-- Given a segment $AB$ and a point P, if vector $\overrightarrow{PB}$ is half of vector $\overrightarrow{AB}$, P is the midpoint of $AB$. -/
theorem Seg.midpt_of_vector_to_target {seg : Seg P} (h : VEC A seg.2 = (1 / 2 : ℝ) • VEC seg.1 seg.2) : A = seg.midpoint := by
  refine' midpt_of_vector_from_source _
  rw [← add_left_inj (VEC A seg.target), vec_add_vec, h, ← add_smul]
  norm_num

theorem SegND.midpt_of_vector_to_target {seg_nd : SegND P} (h : VEC A seg_nd.target = (1 / 2 : ℝ) • VEC seg_nd.source seg_nd.target) : A = seg_nd.midpoint :=
  Seg.midpt_of_vector_to_target h

/-- Given a segment $AB$ and a point P, if vector $\overrightarrow{AP}$ is same as vector $\overrightarrow{PB}$, P is the midpoint of $AB$. -/
theorem Seg.midpt_of_same_vector_to_source_and_target {seg : Seg P} (h : VEC seg.1 A = VEC A seg.2) : A = seg.midpoint := by
  refine' Seg.midpt_of_vector_from_source _
  apply smul_right_injective _ (two_ne_zero' ℝ)
  dsimp
  rw [two_smul]
  nth_rw 2 [h]
  rw [two_smul, vec_add_vec, ← add_smul]
  norm_num

theorem SegND.midpt_of_same_vector_to_source_and_target {seg_nd : SegND P} (h : VEC seg_nd.source A = VEC A seg_nd.target) : A = seg_nd.midpoint :=
  Seg.midpt_of_same_vector_to_source_and_target h

/-- The midpoint of a segment lies on the segment. -/
theorem Seg.midpt_lies_on {seg : Seg P} : seg.midpoint LiesOn seg :=
  ⟨1 / 2, by norm_num; exact seg.vec_source_midpt⟩

/-- The midpoint of a segment lies on the segment. -/
theorem Seg.lies_on_of_eq_midpt {seg : Seg P} (h : A = seg.midpoint) : A LiesOn seg := by
  rw [h]
  exact seg.midpt_lies_on

/-- The midpoint of a nondegenerate segment lies in the interior of the segment. -/
theorem SegND.midpt_lies_int {seg_nd : SegND P} :seg_nd.midpoint LiesInt seg_nd :=
  Seg.lies_int_iff.mpr ⟨seg_nd.2, ⟨1 / 2, by norm_num; exact seg_nd.vec_source_midpt⟩⟩

/-- The midpoint of a nondegenerate segment is not equal to the source of the segment. -/
theorem SegND.midpt_ne_source {seg_nd : SegND P} : seg_nd.midpoint ≠ seg_nd.source :=
  (seg_nd.midpt_lies_int).2

/-- The midpoint of a nondegenerate segment is not equal to the target of the segment. -/
theorem SegND.midpt_ne_target {seg_nd : SegND P} : seg_nd.midpoint ≠ seg_nd.target :=
  (seg_nd.midpt_lies_int).3

/-- The midpoint of a nondegenerate segment lies in the interior of the segment. -/
theorem SegND.lies_int_of_eq_midpt {seg_nd : SegND P} (h : A = seg_nd.midpoint) : A LiesInt seg_nd := by
  rw [h]
  exact seg_nd.midpt_lies_int

/-- A point $X$ on a given segment $AB$ is the midpoint if and only if the vector $\overrightarrow{AX}$ is the same as the vector $\overrightarrow{XB}$. -/
theorem Seg.midpt_iff_same_vector_to_source_and_target {X : P} {seg : Seg P} : X = seg.midpoint ↔ (SEG seg.source X).toVec = (SEG X seg.target).toVec :=
  ⟨fun h ↦ vec_eq_of_eq_midpt h, fun h ↦ midpt_of_same_vector_to_source_and_target h⟩

theorem SegND.midpt_iff_same_vector_to_source_and_target {X : P} {seg_nd : SegND P} : X = seg_nd.midpoint ↔ (SEG seg_nd.source X).toVec = (SEG X seg_nd.target).toVec :=
  ⟨fun h ↦ vec_eq_of_eq_midpt h, fun h ↦ midpt_of_same_vector_to_source_and_target h⟩

/-- The midpoint of a segment has same distance to the source and to the target of the segment. -/
theorem Seg.dist_target_eq_dist_source_of_midpt {seg : Seg P} : (SEG seg.source seg.midpoint).length = (SEG seg.midpoint seg.target).length := by
  rw [Seg.length_eq_norm_toVec, Seg.length_eq_norm_toVec]
  exact congrArg norm seg.vec_midpt_eq

/-- The midpoint of a segment has same distance to the source and to the target of the segment. -/
theorem Seg.dist_target_eq_dist_source_of_eq_midpt {X : P} {seg : Seg P} (h : X = seg.midpoint) : (SEG seg.1 X).length = (SEG X seg.2).length := by
  rw [h]
  exact dist_target_eq_dist_source_of_midpt

/-- A point $X$ is the midpoint of a segment $AB$ if and only if $X$ lies on $AB$ and $X$ has equal distance to $A$ and $B$. -/
theorem Seg.eq_midpt_iff_in_seg_and_dist_target_eq_dist_source {X : P} {seg : Seg P} : X = seg.midpoint ↔ (X LiesOn seg) ∧ (SEG seg.source X).length = (SEG X seg.target).length := by
  refine' ⟨fun h ↦ ⟨Seg.lies_on_of_eq_midpt h, dist_target_eq_dist_source_of_eq_midpt h⟩, _⟩
  intro ⟨⟨t, ht0, ht1, ht⟩, hv⟩
  rw [Seg.length_eq_norm_toVec, Seg.length_eq_norm_toVec] at hv
  simp only [seg_toVec_eq_vec] at hv
  by_cases h0 : ‖VEC X seg.2‖ = 0
  · apply midpt_of_same_vector_to_source_and_target
    rw [h0] at hv
    rw [norm_eq_zero.mp h0, norm_eq_zero.mp hv]
  · have h := ht
    rw [← one_smul ℝ (VEC seg.1 X), ← vec_add_vec seg.1 X seg.2, smul_add, add_comm] at h
    have h := sub_eq_of_eq_add h
    rw [← sub_smul 1 t _] at h
    have h := congrArg norm h
    simp only [norm_smul, hv, Real.norm_of_nonneg ht0, Real.norm_of_nonneg (sub_nonneg.mpr ht1)] at h
    have h : t = 1 / 2 := by
      apply eq_one_div_of_mul_eq_one_left
      rw [mul_two]
      exact (eq_add_of_sub_eq (mul_right_cancel₀ h0 h)).symm
    exact midpt_of_vector_from_source (by rw [ht, h])

theorem SegND.eq_midpt_iff_in_seg_and_dist_target_eq_dist_source {X : P} {seg_nd : SegND P} :
X = seg_nd.midpoint ↔
(X LiesOn seg_nd) ∧ (SEG seg_nd.source X).length = (SEG X seg_nd.target).length :=
  seg_nd.1.eq_midpt_iff_in_seg_and_dist_target_eq_dist_source

theorem Seg.reverse_midpt_eq_midpt {seg : Seg P} : seg.reverse.midpoint = seg.midpoint := by
  rw [Seg.eq_midpt_iff_in_seg_and_dist_target_eq_dist_source]
  let m := seg.reverse.midpoint
  have H2: (m LiesOn seg.reverse) ∧ (SEG seg.reverse.source m).length = (SEG m seg.reverse.target).length:= by
    exact eq_midpt_iff_in_seg_and_dist_target_eq_dist_source.mp rfl
  rcases H2 with ⟨H1, H2⟩
  constructor
  exact lies_on_rev_iff_lies_on.mp H1
  show (SEG seg.reverse.target m).length = (SEG m seg.reverse.source).length
  rw [length_of_rev_eq_length', ←H2, length_of_rev_eq_length']



theorem SegND.reverse_midpt_eq_midpt {seg_nd : SegND P} : seg_nd.reverse.midpoint = seg_nd.midpoint :=
  seg_nd.1.reverse_midpt_eq_midpt

end midpoint

section existence_theorem
/-!
## (10) Existence theorem
-/

/-- Given a segment $AB$, the midpoint of $A$ and $B + \overrightarrow{AB}$ is B. -/
theorem Seg.target_eq_vec_vadd_target_midpt {seg : Seg P} : seg.2 = (SEG seg.1 (seg.toVec +ᵥ seg.2)).midpoint :=
  midpt_of_same_vector_to_source_and_target (vadd_vsub seg.toVec seg.2).symm

theorem SegND.target_eq_vec_vadd_target_midpt {seg_nd : SegND P} : seg_nd.target = (SEG seg_nd.source (seg_nd.toVecND.1 +ᵥ seg_nd.target)).midpoint :=
  Seg.midpt_of_same_vector_to_source_and_target (vadd_vsub seg_nd.toVecND.1 seg_nd.target).symm

/-- `This theorem should be replaced! B is midpt of A and B + VEC A B, midpt liesint a seg_nd` Given a nondegenerate segment $AB$, B lies in the interior of the segment of $A(B + \overrightarrow{AB})$. -/
theorem SegND.target_lies_int_seg_source_vec_vadd_target {seg_nd : SegND P} : seg_nd.target LiesInt (SEG seg_nd.source (seg_nd.toVecND.1 +ᵥ seg_nd.target)) := by
  have H1: seg_nd.target LiesOn (SEG seg_nd.source (seg_nd.toVecND.1 +ᵥ seg_nd.target)):= by
    nth_rw 1[SegND.target_eq_vec_vadd_target_midpt]
    exact Seg.midpt_lies_on
  have H2: seg_nd.target ≠ seg_nd.source:= seg_nd.2
  have H3: seg_nd.target ≠ (seg_nd.toVecND.1 +ᵥ seg_nd.target):= by
    by_contra H4
    nth_rw 1 [← zero_vadd Vec seg_nd.target] at H4
    have H5: (0 : Vec)  = seg_nd.toVecND.1 := by
      exact vadd_right_cancel _ H4
    have H6: seg_nd.toVecND.1 ≠ (0: Vec) := by
      simp only [ne_eq, VecND.ne_zero, not_false_eq_true]
    exact H6 (id H5.symm)
  exact ⟨H1, H2, H3⟩


  /- (SEG_nd seg_nd.1.1  <| fun h ↦ seg_nd.2 <| toVec_eq_zero_of_deg.mpr <| zero_eq_bit0.mp <|
    (vsub_eq_zero_iff_eq.mpr h).symm.trans <| vadd_vsub_assoc seg_nd.1.toVec
      seg_nd.1.2 seg_nd.1.1).lies_int_of_eq_midpt seg_nd.target_eq_vec_vadd_target_midpt -/

/-- Archimedean property I : given a directed segment AB (with A ≠ B), then there exists a point P such that B lies on the directed segment AP and P ≠ B. -/
theorem SegND.exist_pt_beyond_pt (l : SegND P) : (∃ q : P, l.target LiesInt (SEG l.source q)) :=
  ⟨l.1.toVec +ᵥ l.1.target, l.target_lies_int_seg_source_vec_vadd_target⟩

/-- Archimedean property II: On an nontrivial directed segment, one can always find a point in its interior.  `This will be moved to later disccusion about midpoint of a segment, as the midpoint is a point in the interior of a nontrivial segment`
    If a segment contains an interior point, then it is nondegenerate-/
theorem Seg.nd_of_exist_int_pt {X : P} {seg : Seg P} (h : X LiesInt seg) : seg.IsND := by
  rcases h with ⟨⟨_, ⟨_, _, e⟩⟩, p_ne_s, _⟩
  have t : VEC seg.source X ≠ 0 := ne_iff_vec_ne_zero.mp p_ne_s
  rw [e] at t
  exact Iff.mp vsub_ne_zero (right_ne_zero_of_smul t)

/-- A segment is nondegenerate if and only if it contains an interior point. -/
theorem Seg.nd_iff_exist_int_pt {seg : Seg P} : (∃ (X : P), X LiesInt seg) ↔ seg.IsND :=
  ⟨fun ⟨_, b⟩ ↦ nd_of_exist_int_pt b, fun h ↦ ⟨seg.midpoint, SegND.midpt_lies_int (seg_nd :=⟨seg, h⟩)⟩⟩

/-- If a segment is nondegenerate, it contains an interior point. -/
theorem SegND.exist_int_pt {seg_nd : SegND P} : ∃ (X : P), X LiesInt seg_nd := ⟨seg_nd.midpoint, midpt_lies_int⟩

/-- A segment contains an interior point if and only if its length is positive. -/
theorem Seg.length_pos_iff_exist_int_pt {seg : Seg P} : 0 < seg.length ↔ (∃ (X : P), X LiesInt seg) :=
  length_pos_iff_nd.trans nd_iff_exist_int_pt.symm

theorem SegND.length_pos_iff_exist_int_pt {seg_nd : SegND P} : 0 < seg_nd.length ↔ (∃ (X : P), X LiesInt seg_nd) := by
  exact Seg.length_pos_iff_exist_int_pt

/-- A ray contains two distinct points. -/
theorem Ray.nontriv (ray : Ray P) : ∃ (A B : P), (A ∈ ray.carrier) ∧ (B ∈ ray.carrier) ∧ (B ≠ A) :=
  ⟨ray.1, (ray.2.unitVec +ᵥ ray.1), source_lies_on,
  ⟨1 ,zero_le_one ,(vec_of_pt_vadd_pt_eq_vec ray.1 ray.2.unitVecND).trans (one_smul ℝ ray.toDir.unitVec).symm⟩, by
  rw [ne_eq, vadd_eq_self_iff_vec_eq_zero]
  exact VecND.ne_zero _⟩

end existence_theorem

end EuclidGeom
