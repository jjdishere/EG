import EuclideanGeometry.Foundation.Index

/-!
# Geometry Problems of 48th International Mathematical Olympiad (2007)
-/

noncomputable section

namespace EuclidGeom

open Line Angle AngValue Triangle TriangleND

/-!
### Problem 2

Consider ﬁve points $A$, $B$, $C$, $D$, $E$ such that $ABCD$ is a parallelogram and $BCED$
is a cyclic quadrilateral. Let $l$ be a line passing through $A$, and let $l$ intersect segment
$DC$ and line $BC$ at points $F$ and $G$, respectively. Suppose that $EF$ = $EG$ = $EC$. Prove
that $l$ is the bisector of angle $DAB$.
-/

namespace IMO_2007_2

structure Setting (P : Type*) [EuclideanPlane P] where
  -- Consider ﬁve points $A$, $B$, $C$, $D$, $E$.
  A : P
  B : P
  C : P
  D : P
  E : P
  -- $ABCD$ is a nondegenerate parallelogram.
  hp : (QDR A B C D).IsPrgND
  -- $BCED$ is a cyclic quadrilateral.
  ω : Circle P
  hbo : B LiesOn ω
  hco : C LiesOn ω
  heo : E LiesOn ω
  hdo : D LiesOn ω
  -- $l$ is a line passing through $A$.
  l : Line P
  ha : A LiesOn l
  -- $l$ intersects segment $DC$ at the point $F$.
  F : P
  hf : F LiesOn l
  hfdc : F LiesInt (SEG D C)
  -- $l$ intersects line $BC$ at the point $G$.
  G : P
  hg : G LiesOn l
  hglbc : G LiesOn (LIN B C (Quadrilateral.isND_of_is_convex hp.1).2)
  -- $|EF| = |EG|$.
  hefg : dist E F = dist E G
  -- $|EG| = |EC|$.
  hegc : dist E G = dist E C

variable {P : Type*} [EuclideanPlane P] (e : Setting P)

namespace Setting

/-- $C$ ≠ $B$ since $ABCD$ is a nondegenerate parallelogram. -/
instance C_ne_B : PtNe e.C e.B := ⟨(Quadrilateral.isND_of_is_convex e.hp.1).2⟩

/-- $D$ ≠ $C$ since $ABCD$ is a nondegenerate parallelogram. -/
instance D_ne_C : PtNe e.D e.C := ⟨(Quadrilateral.isND_of_is_convex e.hp.1).3⟩

/-- $D$ ≠ $A$ since $ABCD$ is a nondegenerate parallelogram. -/
instance D_ne_A : PtNe e.D e.A := ⟨(Quadrilateral.isND_of_is_convex e.hp.1).4⟩

/-- $B$ ≠ $A$ since $ABCD$ is a nondegenerate parallelogram. -/
instance B_ne_A : PtNe e.B e.A := ⟨(Quadrilateral.isND_of_is_convex e.hp.1).1⟩

/-- $F$ ≠ $C$ since $F$ lies in the interior the segment $DC$. -/
instance F_ne_C : PtNe e.F e.C := ⟨e.hfdc.3⟩

/-- Rename line $BC$ as `lbc`. -/
@[pp_dot]
def lbc : Line P := LIN e.B e.C

/-- Rename line $DC$ as `ldc`. -/
@[pp_dot]
def ldc : Line P := LIN e.D e.C

/-- Rename the nondegenerate parallelogram $ABCD$ as `prg`. -/
@[pp_dot]
abbrev prg : ParallelogramND P := PRG_nd e.A e.B e.C e.D e.hp

/-- $B$, $C$ and $D$ are not collinear since $ABCD$ is a nondegenerate parallelogram. -/
@[pp_dot]
lemma hbcd : ¬ Collinear e.B e.C e.D := e.prg.not_collinear₂₃₄

/-- $C$, $D$ and $A$ are not collinear since $ABCD$ is a nondegenerate parallelogram. -/
@[pp_dot]
lemma hcda : ¬ Collinear e.C e.D e.A := e.prg.not_collinear₃₄₁

/-- $C$, $D$ and $A$ are not collinear since $ABCD$ is a nondegenerate parallelogram. -/
@[pp_dot]
lemma habd : ¬ Collinear e.A e.B e.D := fun h ↦ e.prg.not_collinear₄₁₂ h.perm₃₁₂

/-- $B$ lies on line $BC$. -/
@[pp_dot]
lemma hblbc : e.B LiesOn e.lbc := fst_pt_lies_on_mk_pt_pt

/-- $C$ lies on line $BC$. -/
@[pp_dot]
lemma hclbc : e.C LiesOn e.lbc := snd_pt_lies_on_mk_pt_pt

/-- $D$ lies on line $DC$. -/
@[pp_dot]
lemma hdldc : e.D LiesOn e.ldc := fst_pt_lies_on_mk_pt_pt

/-- $C$ lies on line $DC$. -/
@[pp_dot]
lemma hcldc : e.C LiesOn e.ldc := snd_pt_lies_on_mk_pt_pt

/-- $A$ lies on line $AB$. -/
@[pp_dot]
lemma halab : e.A LiesOn LIN e.A e.B := fst_pt_lies_on_mk_pt_pt

/-- $B$ lies on line $AB$. -/
@[pp_dot]
lemma hblab : e.B LiesOn LIN e.A e.B := snd_pt_lies_on_mk_pt_pt

/-- $D$ lies on line $DA$. -/
@[pp_dot]
lemma hdlda : e.D LiesOn LIN e.D e.A := fst_pt_lies_on_mk_pt_pt

/-- $A$ lies on line $DA$. -/
@[pp_dot]
lemma halda : e.A LiesOn LIN e.D e.A := snd_pt_lies_on_mk_pt_pt

/-- $F$ lies on line $DC$ since $F$ lies in the interior the segment $DC$. -/
@[pp_dot]
lemma hfldc : e.F LiesOn e.ldc := (SEG_nd e.D e.C).lies_on_toLine e.hfdc.1

/-- Line $DC$ is not equal to line $BC$ since $B$, $C$ and $D$ are not collinear.-/
@[pp_dot]
lemma hln : e.ldc ≠ e.lbc := ne_pt_pt_of_not_collinear_of_lies_on e.hdldc e.hbcd

/-- Line $DC$ is not equal to line $AB$ since $A$, $B$ and $D$ are not collinear.-/
@[pp_dot]
lemma hnab : e.ldc ≠ (LIN e.A e.B) := ne_pt_pt_of_not_collinear_of_lies_on e.hdldc e.habd

/-- Line $DC$ is not equal to line $BC$ since $B$, $C$ and $D$ are not collinear.-/
@[pp_dot]
lemma hdan : LIN e.D e.A ≠ e.lbc := ne_pt_pt_of_not_collinear_of_lies_on e.hdlda e.hbcd

/-- Line $DC$ is parallel to line $AB$ since $ABCD$ is a nondegenerate parallelogram. -/
@[pp_dot]
lemma hdcab : e.ldc ∥ (LIN e.A e.B) :=
  SegND.rev_para_of_para (para_of_isPrgND e.prg).symm

/-- Line $DA$ is parallel to line $BC$ since $ABCD$ is a nondegenerate parallelogram. -/
@[pp_dot]
lemma hdabc : (LIN e.D e.A) ∥ e.lbc := para_of_isPrgND' e.prg

/-- $G$ ≠ $A$. -/
instance G_ne_A : PtNe e.G e.A where
  out := by
    -- To the contrary, assuming that $G = A$.
    intro h
    -- $G$ lies on line $DA$ since $G = A$.
    have hg : e.G LiesOn LIN e.D e.A := by
      rw [h]
      exact e.halda
    -- Then $G$ lies both on line $DA$ and on line $BC$. Combining with the fact that line $DA$ is parallel to line $BC$, it follows that these two lines are equal, which contradicts the established conclusion that line $DC$ is not equal to line $BC$.
    exact e.hdan (eq_of_parallel_and_pt_lies_on hg e.hglbc e.hdabc)

/-- $G$ ≠ $F$. -/
instance G_ne_F : PtNe e.G e.F where
  out := by
    -- To the contrary, assuming that $G = C$.
    intro h
    -- $F$ lies on line $BC$ since $G$ lies on line $BC$ and $G = F$.
    have hfbc : e.F LiesOn e.lbc := by
      rw [← h]
      exact e.hglbc
    -- Only need to show that line $DC$ and line $BC$ are identical, since it contradicts the non-collinearity of $B$, $C$, and $D$.
    apply ne_pt_pt_of_not_collinear_of_lies_on e.hdldc e.hbcd
    -- line $DC$ and line $BC$ are identical since they have two distinct intersection points $C$ and $F$.
    exact eq_of_pt_pt_lies_on_of_ne snd_pt_lies_on_mk_pt_pt e.hfldc snd_pt_lies_on_mk_pt_pt hfbc

/-- $G$ ≠ $B$. -/
instance G_ne_B : PtNe e.G e.B where
  out := by
    -- To the contrary, assuming that $G = B$.
    intro h
    -- $G$ lies on line $AB$ since $B$ lies on line $AB and $G = B$.
    have hgab : e.G LiesOn (LIN e.A e.B) := by
      rw [h]
      exact e.hblab
    -- Line $AB$ and $l$ are identical since have two distinct intersection points $A$ and $G$. Thus $F$ lies on $l$ implys $F$ lies on line $AB$.
    have hfab : e.F LiesOn (LIN e.A e.B) := by
      rw [eq_of_pt_pt_lies_on_of_ne e.halab hgab e.ha e.hg]
      exact e.hf
    -- Line $DC$ and line $AB$ are identical since they are parallel to each other and intersect at point $F$, which contradicts the established conclusion that line $DC$ is not equal to line $AB$.
    exact e.hnab (eq_of_parallel_and_pt_lies_on e.hfldc hfab e.hdcab)

/-- $G$ ≠ $C$. -/
instance G_ne_C : PtNe e.G e.C where
  out := by
    -- To the contrary, assuming that $G = C$.
    intro h
    -- Only need to prove that $l$ and line $CD$ are identical, since it contradicts the non-collinearity of $C$, $D$, and $A$.
    apply ne_pt_pt_of_not_collinear_of_lies_on e.ha e.hcda
    -- $C$ lies on $l$ since $G$ lies on $l$ and $G = C$.
    have hc : e.C LiesOn e.l := by
      rw [← h]
      exact e.hg
    -- $l$ and line $CD$ are identical since they have two distinct intersection points $F$ and $C$.
    exact e.l.eq_of_pt_pt_lies_on_of_ne e.hf hc
      ((SEG_nd e.C e.D).lies_on_toLine (Seg.lies_on_rev_of_lies_on e.hfdc.1)) fst_pt_lies_on_mk_pt_pt

/-- $|EF| = |EC|$. -/
lemma hefc : dist e.E e.F = dist e.E e.C := e.hefg.trans e.hegc

/-- $F$ lies in the interior the segment $AG$ due to the conditions of parallel lines. -/
@[pp_dot]
lemma hfag : e.F LiesInt SEG e.A e.G :=
  (line_inx_lies_int_seg_iff_of_para e.hdlda e.halda e.hclbc e.hglbc e.hdabc
    e.hdan (pt_pt_linear e.hfldc) (linear e.ha e.hg e.hf)).mp e.hfdc

/-- $C$ lies in the interior the segment $BG$ due to the conditions of parallel lines. -/
@[pp_dot]
lemma hbcg : e.C LiesInt SEG e.B e.G :=
  (lies_int_seg_line_inx_iff_of_para e.hfldc e.hcldc e.halab e.hblab e.hdcab
    e.hnab (linear e.hf e.ha e.hg) (linear e.hclbc e.hblbc e.hglbc)).mp e.hfag

/-- $E$ ≠ $B$. -/
instance E_ne_B : PtNe e.E e.B where
  out := by
    -- To the contrary, assuming that $E = B$.
    intro h
    -- $C$ lies in the interior the segment $EG$ since $E = B$ and $C$ lies in the interior the segment $BG$.
    have hc : e.C LiesInt SEG e.E e.G := by
      rw [h]
      exact e.hbcg
    -- $|EC| < |EG|$ since $C$ lies in the interior the segment $EG$, which contradicts the assumption.
    exact ne_of_lt (Seg.dist_lt_length_of_lies_int hc) e.hegc.symm

/-- $E$ ≠ $C$. -/
instance E_ne_C : PtNe e.E e.C where
  out h :=
    -- To the contrary, assuming that $E = C$. Then $|EC| = 0$, thus $|EG| = |EC| = 0$. As a result, $C = E =G$, which contradicts the established conclusion $G$ ≠ $C$.
    e.G_ne_C.1 ((dist_eq_zero.mp (e.hegc.trans (dist_eq_zero.mpr h))).symm.trans h)

/-- $E$ ≠ $D$. -/
instance E_ne_D : PtNe e.E e.D where
  out := by
    -- To the contrary, assuming that $E = D$.
    intro h
    -- $F$ lies in the interior the segment $EC$ since $F$ lies in the interior the segment $DC$ and $E = D$.
    have hf : e.F LiesInt (SEG e.E e.C) := by
      rw [h]
      exact e.hfdc
    -- $|EF| < |EC|$ since $F$ lies in the interior the segment $EC$, which contradicts the assumption.
    exact ne_of_lt (Seg.dist_lt_length_of_lies_int hf) e.hefc

/-- ∠$CBE$ and ∠$CDE$ are congruent modulo π since $BCED$ is a cyclic quadrilateral. -/
@[pp_dot]
lemma hbcde : ∡ e.C e.B e.E = ∡ e.C e.D e.E :=
  e.ω.dvalue_eq_of_lies_on e.hco e.heo e.hbo e.hdo

/-- $E$ is not lies on line $BC$. -/
@[pp_dot]
lemma helbc : ¬ e.E LiesOn e.lbc := by
  -- To the contrary, assuming that $E$ lies on line $BC$.
  intro h
  -- ∠$CBE$ is equal to 0 modulo π since $E$ lies on the line $BC$. Since ∠$CBE$ and ∠$CDE$ are congruent modulo π, ∠$CDE$ modulo π is also 0, which means $E$ lies on the line $DC$.
  have he : e.E LiesOn e.ldc := pt_pt_maximal <| collinear_iff_dvalue_eq_zero.mpr <|
    e.hbcde.symm.trans (collinear_iff_dvalue_eq_zero.mp (pt_pt_linear h))
  -- Line $DC$ and line $BC$ are identical since they have two distinct intersection points $C$ and $E$, which contradicts the established conclusion line $DC$ is not equal to line $BC$.
  exact e.hln (eq_of_pt_pt_lies_on_of_ne e.hcldc he e.hclbc h)

/-- $E$ is not lies on line $DC$. -/
@[pp_dot]
lemma heldc : ¬ e.E LiesOn e.ldc := by
  -- To the contrary, assuming that $E$ lies on line $DC$.
  intro h
  -- ∠$CDE$ is equal to 0 modulo π since $E$ lies on the line $DC$. Since ∠$CBE$ and ∠$CDE$ are congruent modulo π, then ∠$CBE$ modulo π is also 0, which means $E$ lies on the line $BC$.
  have he : e.E LiesOn e.lbc := pt_pt_maximal <| collinear_iff_dvalue_eq_zero.mpr <|
    e.hbcde.trans (collinear_iff_dvalue_eq_zero.mp (pt_pt_linear h))
  -- Line $DC$ and line $BC$ are identical since they have two distinct intersection points $C$ and $E$, which contradicts the established conclusion line $DC$ is not equal to line $BC$.
  exact e.hln (eq_of_pt_pt_lies_on_of_ne e.hcldc h e.hclbc he)

/-- $G$ is not lies on line $DC$. -/
@[pp_dot]
lemma hgldc : ¬ e.G LiesOn e.ldc := by
  -- To the contrary, assuming that $G$ lies on line $DC$.
  intro h
  -- Then line $DC$ and line $BC$ are identical since they have two distinct intersection points $C$ and $G$, which contradicts the established conclusion line $DC$ is not equal to line $BC$.
  exact e.hln (eq_of_pt_pt_lies_on_of_ne e.hcldc h e.hclbc e.hglbc)

/-- Let $K$ be the midpoint of segment $CG$. -/
@[pp_dot]
abbrev K : P := (SEG e.C e.G).midpoint

/-- Let $L$ be the midpoint of segment $FC$. -/
@[pp_dot]
abbrev L : P := (SEG e.F e.C).midpoint

/-- $K$ ≠ $B$ since it is the midpoint of the nondegenerate segment $CG$. -/
instance K_ne_B : PtNe e.K e.B where
  out := by
    -- To the contrary, assuming that $K = B$.
    intro h
    -- $C$ lies in the interior the segment $KG$ since $K = B$ and $C$ lies in the interior the segment $BG$.
    have hc : e.C LiesInt SEG e.K e.G := by
      rw [h]
      exact e.hbcg
    -- $|KC| < |KG|$ since $C$ lies in the interior the segment $KG$, which contradicts the fact that $K$ is the midpoint of segment $CG$.
    exact ne_of_lt (Seg.dist_lt_length_of_lies_int hc) (SEG e.C e.G).dist_target_eq_dist_source_of_midpt'

/-- $K$ ≠ $C$ since it is the midpoint of the nondegenerate segment $CG$. -/
instance K_ne_C : PtNe e.K e.C := ⟨(SEG_nd e.C e.G).midpt_ne_source⟩

/-- $L$ ≠ $F$ since it is the midpoint of the nondegenerate segment $FC$. -/
instance L_ne_F : PtNe e.L e.F := ⟨(SEG_nd e.F e.C).midpt_ne_source⟩

/-- $L$ ≠ $C$ since it is the midpoint of the nondegenerate segment $FC$. -/
instance L_ne_C : PtNe e.L e.C := ⟨(SEG_nd e.F e.C).midpt_ne_target⟩

/-- $L$ ≠ $D$ since $L$ lies in the interior the segment $DC$. -/
instance L_ne_D : PtNe e.L e.D where
  out :=
    (@every_int_pt_lies_int_seg_of_source_and_target_lies_on_seg P _ (SEG e.F e.C) (SEG e.D e.C)
      e.hfdc.1 Seg.target_lies_on e.L (SEG_nd e.F e.C).midpt_lies_int).2

/-- $K$ is the perpendicular foot from $E$ to line $BC$. -/
@[pp_dot]
lemma hkp : e.K = perp_foot e.E e.lbc := by
  -- Only need to prove $L$ is the perpendicular foot from $E$ to line $CG$ since line $BC$ and line $CG$ are identical.
  rw [← eq_line_of_pt_pt_of_ne e.hclbc e.hglbc]
  -- $K$ is the perpendicular foot from $E$ to line $CG$ since it is the midpoint on the base edge of the isosceles ▵$ECG$.
  exact midpt_eq_perp_foot_of_isIsoceles ((dist_comm e.G e.E).trans e.hegc)

/-- $L$ is the perpendicular foot from $E$ to line $DC$. -/
@[pp_dot]
lemma hlp : e.L = perp_foot e.E e.ldc := by
  -- Only need to prove $K$ is the perpendicular foot from $E$ to line $FC$ since line $DC$ and line $FC$ are identical.
  rw [← eq_line_of_pt_pt_of_ne e.hfldc e.hcldc]
  -- $L$ is the perpendicular foot from $E$ to line $FC$ since it is the midpoint on the base edge of the isosceles ▵$ECG$.
  exact midpt_eq_perp_foot_of_isIsoceles ((dist_comm e.C e.E).trans (hefc e).symm)

/-- $K$ lies on line $BC$ since it is the perpendicular foot from $E$ to line $BC$. -/
@[pp_dot]
lemma hklbc : e.K LiesOn e.lbc := by
  rw [e.hkp]
  exact perp_foot_lies_on_line e.E e.lbc

/-- $L$ lies on line $DC$ since it is the perpendicular foot from $E$ to line $DC$. -/
@[pp_dot]
lemma hlldc : e.L LiesOn e.ldc := by
  rw [e.hlp]
  exact perp_foot_lies_on_line e.E e.ldc

/-- Rename nondegenerate ▵$KBE$ as `KBE`. -/
@[pp_dot]
def KBE : TriangleND P :=
  ⟨▵ e.K e.B e.E, (e.lbc.maximal e.hklbc e.hblbc).mt e.helbc⟩

/-- Rename nondegenerate ▵$LDE$ as `LDE`. -/
@[pp_dot]
def LDE : TriangleND P :=
  ⟨▵ e.L e.D e.E, (e.ldc.maximal e.hlldc e.hdldc).mt e.heldc⟩

/-- Rename nondegenerate ▵$KCE$ as `KCE`. -/
@[pp_dot]
def KCE : TriangleND P :=
  ⟨▵ e.K e.C e.E, (e.lbc.maximal e.hklbc e.hclbc).mt e.helbc⟩

/-- Rename nondegenerate ▵$LCE$ as `LCE`. -/
@[pp_dot]
def LCE : TriangleND P :=
  ⟨▵ e.L e.C e.E, (e.ldc.maximal e.hlldc e.hcldc).mt e.heldc⟩

end Setting

/-- $|EK| / |EL| = |KC| / |LC|$. -/
theorem ratio_eq : dist e.E e.K / dist e.E e.L = dist e.K e.C / dist e.L e.C := by
  -- Using the condition of parallel lines to chase the ratio, we can obtain $\overline{DF}/\overline{DC} = \overline{BC}/\overline{BG}$.
  have hr : divratio e.B e.C e.G = divratio e.D e.F e.C := Eq.symm <|
    (divratio_eq_of_para₂₁₃ e.hdlda e.halda e.hclbc e.hglbc e.hdabc e.hdan
      (pt_pt_linear e.hfldc) (linear e.ha e.hg e.hf)).trans <|
        divratio_eq_of_para₃₂₁ e.hfldc e.hcldc e.halab e.hblab e.hdcab e.hnab
          (linear e.hf e.ha e.hg) (linear e.hclbc e.hblbc e.hglbc)
  -- Note that $K$ and $L$ are the midpoints of segments $CG$ and $FC$ respectively, so chasing the ratio on the lines shows that $|KB| / |LD| = |KC| / |LF|$.
  have h : dist e.K e.B / dist e.L e.D = dist e.K e.C / dist e.L e.F :=
    Real.div_eq_div_of_div_eq_div (dist_ne_zero.mpr e.L_ne_D.1) (dist_ne_zero.mpr e.L_ne_F.1) <|
      ratio_eq_of_divratio_eq (linear e.hklbc e.hblbc e.hclbc) (linear e.hlldc e.hdldc e.hfldc) <|
        ratio_eq_ratio_trans e.hklbc e.hblbc e.hclbc e.hglbc e.hlldc e.hdldc e.hfldc e.hcldc
          ((seg_midpt_ratio e.C e.G).trans (seg_midpt_ratio e.F e.C).symm) hr
  -- $|LC| = |LF|$ since $L$ is the midpoint of the nondegenerate segment $FC$.
  have hl : dist e.L e.F = dist e.L e.C := (SEG e.F e.C).dist_target_eq_dist_source_of_midpt'
  -- Only need to show $|EK| / |EL| = |KB| / |LD|$ since $|LC| = |LF|$ and $|KB| / |LD| = |KC| / |LF|$.
  rw [← hl, ← h]
  -- ▵$KBE$ ∼ ▵$LDE$ since they are both right triangles and have a pair of angles equal in the sense modulo π.
  have hs : e.KBE ∼ e.LDE := sim_of_AA_of_isRt e.KBE e.LDE
    (isRt_at_perp_foot e.hblbc e.hkp e.helbc) (isRt_at_perp_foot e.hdldc e.hlp e.heldc)
      (((dvalue_eq_of_lies_on_line_pt_pt snd_pt_lies_on_mk_pt_pt e.hklbc).trans
        (e.ω.dvalue_eq_of_lies_on e.heo e.hco e.hbo e.hdo)).trans
          (dvalue_eq_of_lies_on_line_pt_pt snd_pt_lies_on_mk_pt_pt e.hlldc).symm)
  -- $|EK| / |EL| = |KB| / |LD|$ since ▵$KBE$ ∼ ▵$LDE$.
  exact hs.ratio₂.symm.trans hs.ratio₃

/-- ▵$CGF$ is a isosceles triangle. -/
theorem tri_CGF_isIsoceles : (▵ e.C e.G e.F).IsIsoceles := by
  -- Since $K$ and $L$ are the midpoints of segment $CG$ and segment $CF$ respectively, we have $|CG| = 2 • |CK|$ and $|CF| = 2 • |CL|$. Therefore, it suffices to show that $|CK| = |CL|$.
  refine' Eq.symm <| ((SEG e.C e.G).two_nsmul_dist_midpt_source_eq_length).symm.trans <|
    ((smul_right_inj two_ne_zero).mpr _).trans (SEG e.F e.C).two_nsmul_dist_midpt_target_eq_length
  -- Since ∠$CKE$ and ∠$CLE$ are both right angles, either ∠$CKE$ = ∠$CLE$ or ∠$CKE$ = -∠$CLE$.
  rcases eq_or_eq_neg_of_isRt
    (isRt_at_perp_foot e.hclbc e.hkp e.helbc) (isRt_at_perp_foot e.hcldc e.hlp e.heldc) with h | h
  -- If ∠$CKE$ =∠$CLE$, then ▵$KCE$ and ▵$LCE$ are similar by the SAS criterion, so ∠$ECK$ =∠$ECL$.
  · have ha : ∠ e.E e.C e.K = ∠ e.E e.C e.L := (sim_of_SAS e.KCE e.LCE (ratio_eq e) h).2
    -- Then ▵$KCE$ and ▵$LCE$ are congruent by the AAS criterion. As a result, $|CK| = |CL|$.
    exact (@congr_of_AAS P _ e.KCE e.LCE h ha rfl).3
  -- If ∠$CKE$ = - ∠$CLE$, then ▵$KCE$ and ▵$LCE$ are anti-similar by the SAS criterion, so ∠$ECK$ = - ∠$ECL$.
  · have ha : ∠ e.E e.C e.K = - ∠ e.E e.C e.L := (asim_of_SAS e.KCE e.LCE (ratio_eq e) h).2
    -- Then ▵$KCE$ and ▵$LCE$ are anti-congruent by the AAS criterion. As a result, $|CK| = |CL|$.
    exact (@acongr_of_AAS P _ e.KCE e.LCE h ha rfl).3

/-- $l$ is the bisector of angle $DAB$. -/
theorem Result : IsAngBisLine (ANG e.D e.A e.B) e.l := by
  -- $l$ and line $AG$ are identical since they have two distinct intersection points $A$ and $G$. As a result,only need to show line $AG$ is the bisector of angle $DAB$.
  rw [eq_of_pt_pt_lies_on_of_ne e.ha e.hg fst_pt_lies_on_mk_pt_pt snd_pt_lies_on_mk_pt_pt]
  -- Only need to show ∠$DAG$ = ∠$GAB$ due to the definition of angle bisector.
  apply isAngBisLine_of_value_eq
  -- ∠$GFC$ = ∠$CGF$ since they are the angles corresponding to the legs of isosceles ▵$CGF$.
  have h : ∠ e.G e.F e.C = ∠ e.C e.G e.F :=
    (is_isoceles_tri_iff_ang_eq_ang_of_nd_tri ⟨▵ e.C e.F e.G, (maximal e.hcldc e.hfldc).mt e.hgldc⟩).mp
      (is_isoceles_of_flip_vert_isoceles (tri_CGF_isIsoceles e))
  -- Only need to show ∠$DAG$ = ∠$CGF$ and ∠$DAG$ = ∠$CGF$ since ∠$GFC$ and ∠$CGF$.
  refine' (Eq.trans _ h.symm).trans _
  -- Only need to show that ∠$DAG$ and ∠$CGF$ are alternate interior angles.
  · apply value_eq_of_dir_eq_neg_dir
    -- Due to the transferability of the equation, only need to show $\overrightarrow{AD}$ and $\overrightarrow{BC}$ have the same direction and the direction of $\overrightarrow{BC}$ equals the opposite direction of $\overrightarrow{GC}$.
    · calc
        -- Firstly show that $\overrightarrow{AD}$ and $\overrightarrow{BC}$ have the same direction.
        (VEC_nd e.A e.D).toDir = (VEC_nd e.B e.C).toDir := by
          -- Only need to show $\overrightarrow{AD} = \overrightarrow{BC}$.
          congr 1
          -- $\overrightarrow{AD} = \overrightarrow{BC}$ since $ABCD$ is a nondegenerate parallelogram.
          exact VecND.ext ((prgND_iff_perm_prgND (QDR e.A e.B e.C e.D)).mp e.hp).2.symm
        -- The direction of $\overrightarrow{BC}$ equals the opposite direction of $\overrightarrow{GC}$ since $C$ lies in the interior the segment $BG$.
        _ = - (VEC_nd e.G e.C).toDir := (SEG_nd e.B e.G).toDir_eq_neg_toDir_of_lies_int' e.hbcg
    -- The direction of $\overrightarrow{AG}$ equals the opposite direction of $\overrightarrow{GF}$ since $F$ lies in the interior the segment $AG$.
    · exact ((SEG_nd e.A e.G).source_pt_toDir_eq_toDir_of_lies_int e.hfag).symm.trans <|
        (SEG_nd e.A e.G).toDir_eq_neg_toDir_of_lies_int' e.hfag
  -- Only need to show that ∠$DAG$ and ∠$CGF$ are corresponding angles.
  · apply value_eq_of_dir_eq
    -- The direction of $\overrightarrow{FG}$ equals the direction of $\overrightarrow{AG}$ since $F$ lies in the interior the segment $AG$.
    · exact (SEG_nd e.A e.G).pt_target_toDir_eq_toDir_of_lies_int e.hfag
    -- The direction of $\overrightarrow{FC}$ equals the direction of $\overrightarrow{DC}$ since $F$ lies in the interior the segment $DC$.
    · apply ((SEG_nd e.D e.C).pt_target_toDir_eq_toDir_of_lies_int e.hfdc).trans
      -- As a result, only need to show The direction of $\overrightarrow{DC}$ equals the direction of $\overrightarrow{AB}$.
      show (VEC_nd e.D e.C).toDir = (VEC_nd e.A e.B).toDir
      -- Only need to show $\overrightarrow{DC} = \overrightarrow{AB}$.
      congr 1
      -- $\overrightarrow{DC} = \overrightarrow{AB}$ since $ABCD$ is a nondegenerate parallelogram.
      exact VecND.ext e.hp.2.symm

/- In fact, it is only necessary reqiure $F$ lying on line $DC$, $F$ ≠ $C$, $E$ ≠ $B$ and $E$ ≠ $D$,
not necessarily reqiure $F$ lying in the interior the segment $DC$. -/

end IMO_2007_2

end EuclidGeom
