import EuclideanGeometry.Foundation.Construction.Polygon.Quadrilateral
import EuclideanGeometry.Foundation.Construction.Polygon.Trapezoid
import EuclideanGeometry.Foundation.Tactic.Congruence.Congruence
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel_trash

/-!

-/
noncomputable section
namespace EuclidGeom

-- `Add class parallelogram and state every theorem in structure`
@[pp_dot]
def Quadrilateral.IsParallelogram {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃

scoped postfix : 50 "IsParallelogram" => Quadrilateral.IsParallelogram

@[ext]
structure Parallelogram (P : Type _) [EuclideanPlane P] extends Quadrilateral P where
  is_parallelogram : toQuadrilateral IsParallelogram

@[ext]
structure Parallelogram_nd (P : Type _) [EuclideanPlane P] extends Quadrilateral_cvx P, Parallelogram P

def Parallelogram.mk_pt_pt_pt_pt {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D) IsParallelogram) : Parallelogram P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h

def Parallelogram_nd.mk_pt_pt_pt_pt {P : Type _} [EuclideanPlane P] (A B C D : P) (h : (QDR A B C D) IsParallelogram) (h': (QDR A B C D) IsConvex): Parallelogram_nd P where
  toQuadrilateral := (QDR A B C D)
  is_parallelogram := h
  convex := h'

scoped notation "PRG" => Parallelogram.mk_pt_pt_pt_pt
scoped notation "PRG_nd" => Parallelogram_nd.mk_pt_pt_pt_pt

def mk_parallelogram {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) : Parallelogram P where
  toQuadrilateral := qdr
  is_parallelogram := h

def mk_parallelogram_nd {P : Type _} [EuclideanPlane P] {qdr : Quadrilateral P} (h : qdr IsParallelogram) (h': qdr IsConvex): Parallelogram_nd P where
  toQuadrilateral := qdr
  is_parallelogram := h
  convex := h'

@[pp_dot]
def Quadrilateral_cvx.IsParallelogram_nd {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P) : Prop := ( qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) ∧ (qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃)

@[pp_dot]
def Quadrilateral.IsParallelogram_nd {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P) : Prop := by
  by_cases h : qdr IsConvex
  · exact (Quadrilateral_cvx.mk_is_convex h).IsParallelogram_nd
  · exact False

@[pp_dot]
def Parallelogram.ParallelogramIs_nd {P : Type _} [EuclideanPlane P] (qdr_para : Parallelogram P) : Prop := qdr_para.1 IsConvex

postfix : 50 "IsPRG_nd" => Quadrilateral.IsParallelogram_nd
postfix : 50 "IsPRG" => Quadrilateral.IsParallelogram
postfix : 50 "PRGIs_nd" => Parallelogram.ParallelogramIs_nd

variable {P : Type _} [EuclideanPlane P]

section criteria
variable {A B C D : P} (h : (QDR A B C D) IsConvex)
variable {P : Type _} [EuclideanPlane P] (qdr_cvx : Quadrilateral_cvx P)
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)

/-- Given Quadrilateral_cvx qdr_cvx, qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄ and qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃, then qdr_cvx is a Parallelogram_nd. -/
theorem is_prg_nd_of_para_para (h₁ : qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) (h₂ : qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃) : qdr_cvx.IsParallelogram_nd := by
  unfold Quadrilateral_cvx.IsParallelogram_nd
  constructor
  exact h₁
  exact h₂

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, AB ∥ CD and AD ∥ BC, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_nd_of_para_para_variant (h₁ : (SEG_nd A B (Quadrilateral_cvx.nd₁₂ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd C D (Quadrilateral_cvx.nd₃₄ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (SEG_nd A D (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd B C (Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex h)))) : QDR A B C D IsPRG_nd := by
  unfold Quadrilateral.IsParallelogram_nd
  rw [dif_pos h]
  unfold Quadrilateral_cvx.IsParallelogram_nd
  constructor
  exact h₁
  exact h₂

/-- Given Quadrilateral_cvx qdr_cvx, and (qdr_cvx.edge_nd₁₂).1.length = (qdr_cvx.edge_nd₃₄).1.length and qdr_cvx.edge_nd₁₄.1.length = qdr_cvx.edge_nd₂₃.1.length, qdr_cvx is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_length_eq_length (h₁ : (qdr_cvx.edge_nd₁₂).1.length = (qdr_cvx.edge_nd₃₄).1.length) (h₂ : qdr_cvx.edge_nd₁₄.1.length = qdr_cvx.edge_nd₂₃.1.length) : qdr_cvx.IsParallelogram_nd := by
  unfold Quadrilateral_cvx.IsParallelogram_nd
  unfold Quadrilateral_cvx.edge_nd₁₂ at h₁
  unfold Quadrilateral_cvx.edge_nd₃₄ at h₁
  unfold Quadrilateral_cvx.edge_nd₁₄ at h₂
  unfold Quadrilateral_cvx.edge_nd₂₃ at h₂
  have prep₁: (qdr_cvx.triangle₁).1.edge₁ = SEG_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.nd₁₂ := rfl
  have prep₂: (qdr_cvx.triangle₃).1.edge₁ = SEG_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.nd₃₄ := rfl
  have t₁: (qdr_cvx.triangle₁).1.edge₁.length = (qdr_cvx.triangle₃).1.edge₁.length := by
    rw [prep₁, prep₂]
    exact h₁
  have prep₃: (qdr_cvx.triangle₁).1.edge₂.length = (SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.nd₂₄).1.length := rfl
  have prep₄: (qdr_cvx.triangle₃).1.edge₂.length = (SEG_nd qdr_cvx.point₄ qdr_cvx.point₂ qdr_cvx.nd₂₄.symm).1.length := rfl
  have prep₅: (SEG_nd qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.nd₂₄).1.length = (SEG_nd qdr_cvx.point₄ qdr_cvx.point₂ qdr_cvx.nd₂₄.symm).1.length := by
    apply SegND.length_of_rev_eq_length.symm
  have prep₈: (SEG_nd qdr_cvx.point₁ qdr_cvx.point₄ qdr_cvx.nd₁₄).1.length = (SEG_nd qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.nd₁₄.symm).1.length := by
    apply SegND.length_of_rev_eq_length.symm
  have t₂: (qdr_cvx.triangle₁).1.edge₂.length = (qdr_cvx.triangle₃).1.edge₂.length := by
    rw [prep₃, prep₄]
    exact prep₅
  have prep₆: (qdr_cvx.triangle₁).1.edge₃ = SEG_nd qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.nd₁₄.symm := rfl
  have prep₇: (qdr_cvx.triangle₃).1.edge₃ = SEG_nd qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.nd₂₃ := rfl
  have t₃: (qdr_cvx.triangle₁).1.edge₃.length = (qdr_cvx.triangle₃).1.edge₃.length := by
    rw [prep₆, prep₇, prep₈.symm]
    exact h₂
  have u: qdr_cvx.triangle₁ ≅ qdr_cvx.triangle₃ := (TriangleND.congr_of_SSS_of_eq_orientation t₁ t₂ t₃ qdr_cvx.cclock_eq)
  -- have A: qdr_cvx.triangle₁.1.isND ∧ qdr_cvx.triangle₃.1.isND := by
  --     constructor
  --     apply qdr_cvx.triangle₁.2
  --     apply qdr_cvx.triangle₃.2
  have prepa₁: qdr_cvx.triangle₁.angle₁.value = qdr_cvx.triangle₃.angle₁.value := by exact u.4

  have prepa₂: qdr_cvx.triangle₁.angle₃.value = qdr_cvx.triangle₃.angle₃.value := by exact u.6
  -- have rex: qdr_cvx.diag_nd₂₄.toRay.toDir = - (qdr_cvx.diag_nd₂₄).toRay.reverse.toDir := by
  --   exact neg_eq_iff_eq_neg.mp rfl
  have J: qdr_cvx.triangle₁.angle₁.end_ray = qdr_cvx.diag_nd₂₄.reverse.toRay := by rfl
  have K: qdr_cvx.triangle₁.angle₃.start_ray = qdr_cvx.diag_nd₂₄.toRay := by rfl
  have Q: qdr_cvx.triangle₃.angle₁.end_ray = qdr_cvx.diag_nd₂₄.toRay := by rfl
  have joker: qdr_cvx.triangle₃.angle₃.start_ray = qdr_cvx.diag_nd₂₄.reverse.toRay := by rfl
  have prepa₃: qdr_cvx.triangle₁.angle₃.start_ray.toDir = qdr_cvx.triangle₃.angle₃.start_ray.reverse.toDir := by
    have JOKER: qdr_cvx.diag_nd₂₄.reverse.toRay.reverse.toDir = - qdr_cvx.diag_nd₂₄.reverse.toRay.toDir := qdr_cvx.diag_nd₂₄.reverse.toRay.toDir_of_rev_eq_neg_toDir
    have SpadeA: qdr_cvx.diag_nd₂₄.reverse.toRay.toDir = - qdr_cvx.diag_nd₂₄.toRay.toDir := qdr_cvx.diag_nd₂₄.toDir_of_rev_eq_neg_toDir
    rw [K, joker, JOKER, SpadeA]
    simp only [neg_neg]
  have prepa₄: qdr_cvx.triangle₁.angle₁.end_ray.toDir = qdr_cvx.triangle₃.angle₁.end_ray.reverse.toDir := by
    have JOKER: qdr_cvx.diag_nd₂₄.reverse.toRay.toDir = - qdr_cvx.diag_nd₂₄.toRay.toDir := qdr_cvx.diag_nd₂₄.toDir_of_rev_eq_neg_toDir
    have SpadeA: qdr_cvx.diag_nd₂₄.toRay.reverse.toDir = -qdr_cvx.diag_nd₂₄.toRay.toDir := qdr_cvx.diag_nd₂₄.toRay.toDir_of_rev_eq_neg_toDir
    rw [J, Q, JOKER, SpadeA]
  have near₁: qdr_cvx.triangle₁.angle₁.start_ray.toDir = - qdr_cvx.triangle₃.angle₁.start_ray.toDir := by
    have prepar: qdr_cvx.triangle₁.angle₁.start_ray.toDir = qdr_cvx.triangle₃.angle₁.start_ray.reverse.toDir := start_ray_toDir_rev_toDir_of_ang_rev_ang prepa₄ prepa₁
    have prepar': qdr_cvx.triangle₃.angle₁.start_ray.reverse.toDir = - qdr_cvx.triangle₃.angle₁.start_ray.toDir := qdr_cvx.triangle₃.angle₁.start_ray.toDir_of_rev_eq_neg_toDir
    rw [prepar, prepar']
  have near₂: qdr_cvx.triangle₁.angle₃.end_ray.toDir = - qdr_cvx.triangle₃.angle₃.end_ray.toDir := by
    have prepar: qdr_cvx.triangle₁.angle₃.end_ray.toDir = qdr_cvx.triangle₃.angle₃.end_ray.reverse.toDir := end_ray_toDir_rev_toDir_of_ang_rev_ang prepa₃ prepa₂
    have prepar': qdr_cvx.triangle₃.angle₃.end_ray.reverse.toDir = - qdr_cvx.triangle₃.angle₃.end_ray.toDir := qdr_cvx.triangle₃.angle₃.end_ray.toDir_of_rev_eq_neg_toDir
    rw [prepar, prepar']
  have very_near₁: qdr_cvx.triangle₁.angle₁.start_ray.toProj = qdr_cvx.triangle₃.angle₁.start_ray.toProj := by
    apply Dir.toProj_eq_toProj_iff.mpr
    right
    exact near₁
  have very_close₁: qdr_cvx.triangle₁.angle₁.start_ray ∥ qdr_cvx.triangle₃.angle₁.start_ray := very_near₁
  have very_near₂: qdr_cvx.triangle₁.angle₃.end_ray.toProj = qdr_cvx.triangle₃.angle₃.end_ray.toProj := by
    apply Dir.toProj_eq_toProj_iff.mpr
    right
    exact near₂
  have very_close₂: qdr_cvx.triangle₁.angle₃.end_ray ∥ qdr_cvx.triangle₃.angle₃.end_ray := very_near₂
  have close₁: qdr_cvx.edge_nd₁₄.toProj = qdr_cvx.triangle₁.angle₁.start_ray.toProj := by
    have third: qdr_cvx.edge_nd₁₄.reverse.toProj = qdr_cvx.edge_nd₁₄.toProj := qdr_cvx.edge_nd₁₄.toProj_of_rev_eq_toProj
    exact id third.symm
  have close₂: qdr_cvx.edge_nd₂₃.toProj = qdr_cvx.triangle₃.angle₁.start_ray.toProj := by rfl
  have close₃: qdr_cvx.edge_nd₁₂.toProj = qdr_cvx.triangle₁.angle₃.end_ray.toProj := by
    have last: qdr_cvx.edge_nd₁₂.reverse.toRay = qdr_cvx.triangle₁.angle₃.end_ray := by rfl
    have second: qdr_cvx.edge_nd₁₂.reverse.toProj = qdr_cvx.triangle₁.angle₃.end_ray.toProj := by rfl
    have third: qdr_cvx.edge_nd₁₂.reverse.toProj = qdr_cvx.edge_nd₁₂.toProj := qdr_cvx.edge_nd₁₂.toProj_of_rev_eq_toProj
    rw [third.symm, second, last.symm]
  have close₄: qdr_cvx.edge_nd₃₄.toProj = qdr_cvx.triangle₃.angle₃.end_ray.toProj := by
    have last: qdr_cvx.edge_nd₃₄.reverse.toRay = qdr_cvx.triangle₃.angle₃.end_ray := by rfl
    have second: qdr_cvx.edge_nd₃₄.reverse.toProj = qdr_cvx.triangle₃.angle₃.end_ray.toProj := by rfl
    have third: qdr_cvx.edge_nd₃₄.reverse.toProj = qdr_cvx.edge_nd₃₄.toProj := qdr_cvx.edge_nd₃₄.toProj_of_rev_eq_toProj
    rw [third.symm, second, last.symm]
  have win₁: qdr_cvx.edge_nd₁₂.toProj = qdr_cvx.edge_nd₃₄.toProj := by
    rw [close₃, close₄]
    exact very_close₂
  have win₂: qdr_cvx.edge_nd₁₄.toProj = qdr_cvx.edge_nd₂₃.toProj := by
    rw [close₁, close₂]
    exact very_close₁
  exact ⟨win₁, win₂⟩

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AB = CD and AD = BC, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_length_eq_length_variant (h₁ : (SEG A B).length = (SEG C D).length) (h₂ : (SEG A D).length = (SEG B C).length) : QDR A B C D IsPRG_nd := by
  unfold Quadrilateral.IsParallelogram_nd
  by_cases j: QDR A B C D IsConvex
  simp only [j, dite_true]
  exact
    is_prg_nd_of_eq_length_eq_length
      (Quadrilateral_cvx.mk_is_convex (Eq.mpr_prop (eq_true j) True.intro)) h₁ h₂
  simp only [j, dite_false]
  exact j h

/-- Given Quadrilateral_cvx qdr_cvx, and qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄ and (qdr_cvx.edge_nd₁₂).1.length = (qdr_cvx.edge_nd₃₄).1.length, qdr_cvx is a Parallelogram_nd. -/
theorem is_prg_nd_of_para_eq_length (h₁ : qdr_cvx.edge_nd₁₂ ∥ qdr_cvx.edge_nd₃₄) (h₂ : qdr_cvx.edge_nd₁₂.1.length = qdr_cvx.edge_nd₃₄.1.length) : qdr_cvx.IsParallelogram_nd := by
  unfold Quadrilateral_cvx.IsParallelogram_nd
  unfold Quadrilateral_cvx.edge_nd₁₂
  unfold Quadrilateral_cvx.edge_nd₃₄
  unfold Quadrilateral_cvx.edge_nd₁₄
  unfold Quadrilateral_cvx.edge_nd₂₃
  unfold parallel at h₁
  have h: qdr_cvx.edge_nd₁₂.toDir = qdr_cvx.edge_nd₃₄.toDir ∨ qdr_cvx.edge_nd₁₂.toDir = - qdr_cvx.edge_nd₃₄.toDir := by
    apply Dir.toProj_eq_toProj_iff.mp
    exact h₁
  have diag_ng_para: ¬ qdr_cvx.diag_nd₁₃.toProj = qdr_cvx.diag_nd₂₄.toProj := qdr_cvx.diag_not_para
  rcases h with case_not_convex | case_convex
  -- Case that is not convex, goal is prove contra
  have angle₁_eq_angle₄: (ANG qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.nd₃₄.symm qdr_cvx.nd₁₄.symm).value = (ANG qdr_cvx.point₂ qdr_cvx.point₁ qdr_cvx.point₄ qdr_cvx.nd₁₂ qdr_cvx.nd₁₄).value := by
    apply ang_eq_ang_of_toDir_rev_toDir
    have ray₁₂_toDir_eq_SegND₁₂_toDir: qdr_cvx.edge_nd₁₂.toDir = (ANG qdr_cvx.point₂ qdr_cvx.point₁ qdr_cvx.point₄ qdr_cvx.nd₁₂ qdr_cvx.nd₁₄).start_ray.toDir := by rfl
    have ray₄₃_toDir_eq_SegND₃₄_rev_toDir: qdr_cvx.edge_nd₃₄.reverse.toDir = (ANG qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.nd₃₄.symm qdr_cvx.nd₁₄.symm).start_ray.toDir := by rfl
    have SegND₄₃_toDir_neg_SegND₃₄_rev_toDir: qdr_cvx.edge_nd₃₄.reverse.toDir = - qdr_cvx.edge_nd₃₄.toDir := by apply SegND.toDir_of_rev_eq_neg_toDir
    rw [ray₁₂_toDir_eq_SegND₁₂_toDir.symm, ray₄₃_toDir_eq_SegND₃₄_rev_toDir.symm, SegND₄₃_toDir_neg_SegND₃₄_rev_toDir, case_not_convex]
    exact qdr_cvx.edge_nd₁₄.toDir_of_rev_eq_neg_toDir
  have IsCongrTo₁₄: TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁ IsCongrTo TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄ := by
    have edge₂_eq: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).1.edge₂.length = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).1.edge₂.length := by apply length_of_rev_eq_length'
    have edge₃_eq: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).1.edge₃.length = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).1.edge₃.length := by
      have eq_length: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).1.edge₃.length = qdr_cvx.edge_nd₃₄.length := by apply length_of_rev_eq_length'
      rw [eq_length]
      exact h₂.symm
    apply TriangleND.congr_of_SAS edge₂_eq angle₁_eq_angle₄ edge₃_eq
  unfold TriangleND.IsCongr at IsCongrTo₁₄
  have A: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).1.IsND ∧ (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).1.IsND := by
      constructor
      apply qdr_cvx.not_colinear₄₃₁
      apply qdr_cvx.not_colinear₁₂₄
  -- Use IsCongrTo to prove angle eq
  have prepa₁: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).angle₃.value = (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.value := by
    rcases IsCongrTo₁₄ with ⟨_, _, _, _, _, propf⟩
    exact propf.symm
  -- Use angle_eq to prove two diag para.
  have prepa₂: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.start_ray.reverse.toDir = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).angle₃.start_ray.toDir := by
    have prepaA: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.start_ray.reverse.toDir = - (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.start_ray.toDir := (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.start_ray.toDir_of_rev_eq_neg_toDir
    have prepaB: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.start_ray.toDir = qdr_cvx.edge_nd₁₄.toDir := by rfl
    have prepaC: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).angle₃.start_ray.toDir = qdr_cvx.edge_nd₁₄.reverse.toDir := by rfl
    have prepaD: qdr_cvx.edge_nd₁₄.reverse.toDir = - qdr_cvx.edge_nd₁₄.toDir := qdr_cvx.edge_nd₁₄.toDir_of_rev_eq_neg_toDir
    rw [prepaA, prepaB, prepaC, prepaD]
  have prepa₃: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.end_ray.reverse.toDir = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).angle₃.end_ray.toDir := (end_ray_toDir_rev_toDir_of_ang_rev_ang prepa₂.symm prepa₁).symm
  have prepa₄: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.end_ray.reverse.toDir = - (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.end_ray.toDir := by
    apply (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.end_ray.toDir_of_rev_eq_neg_toDir
  rw [prepa₄] at prepa₃
  have very_nr₂: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.end_ray.toProj = (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).angle₃.end_ray.toProj := by
    apply Dir.toProj_eq_toProj_iff.mpr
    right
    exact neg_eq_iff_eq_neg.mp prepa₃
  have prepa₅: (TRI_nd qdr_cvx.point₄ qdr_cvx.point₃ qdr_cvx.point₁ qdr_cvx.not_colinear₄₃₁).angle₃.end_ray.toProj = qdr_cvx.diag_nd₁₃.toProj := by rfl
  have prepa₆: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₄ qdr_cvx.not_colinear₁₂₄).angle₃.end_ray.toProj = qdr_cvx.diag_nd₂₄.reverse.toProj := by rfl
  have prepa₇: qdr_cvx.diag_nd₂₄.reverse.toProj = qdr_cvx.diag_nd₂₄.toProj := qdr_cvx.diag_nd₂₄.toProj_of_rev_eq_toProj
  rw [prepa₇, very_nr₂.symm, prepa₅] at prepa₆
  -- Two diags para, not allowed in a qdr_cvx
  contradiction
  -- Case that is convex, using para to prove angle eq
  have angle₁_eq_angle₃: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).angle₁.value = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₁.value := by
    apply ang_eq_ang_of_toDir_rev_toDir
    exact case_convex
    have K₁: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).angle₁.end_ray.toDir = qdr_cvx.diag_nd₁₃.toDir := by rfl
    have K₂: (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₁.end_ray.toDir = qdr_cvx.diag_nd₁₃.reverse.toDir := by rfl
    have K₃: qdr_cvx.diag_nd₁₃.reverse.toDir = - qdr_cvx.diag_nd₁₃.toDir := qdr_cvx.diag_nd₁₃.toDir_of_rev_eq_neg_toDir
    rw [K₁.symm, K₂.symm] at K₃
    exact neg_eq_iff_eq_neg.mp (id K₃.symm)
  -- Prove IsCongrTo
  have prepar₁: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).1.edge₂.length = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).1.edge₂.length := length_of_rev_eq_length'
  have prepar₂: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).1.edge₃.length = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).1.edge₃.length := h₂
  have IsCongrTo₁₃: TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃ IsCongrTo TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁ := TriangleND.congr_of_SAS prepar₁ angle₁_eq_angle₃ prepar₂
  unfold TriangleND.IsCongr at IsCongrTo₁₃
  have A: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).1.IsND ∧ (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).1.IsND := by
      constructor
      apply (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).2
      apply (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).2
  -- Use IsCongrTo to prove angle eq
  have pr₁: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).angle₃.value = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.value := by
    rcases IsCongrTo₁₃ with ⟨_, _, _, _, _, propf⟩
    exact propf
  -- Use angle eq to prove para, hope qdr_cvx becomes prg
  have pr₂: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).angle₃.start_ray.toDir = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.start_ray.reverse.toDir := by
    have K₄: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).angle₃.start_ray.toDir = qdr_cvx.diag_nd₁₃.reverse.toDir := by rfl
    have K₅: (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.start_ray.toDir = qdr_cvx.diag_nd₁₃.toDir := by rfl
    have K₆: qdr_cvx.diag_nd₁₃.reverse.toDir = - qdr_cvx.diag_nd₁₃.toDir := qdr_cvx.diag_nd₁₃.toDir_of_rev_eq_neg_toDir
    rw [K₄.symm, K₅.symm] at K₆
    exact K₆
  have near: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).angle₃.end_ray.toDir = (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.end_ray.reverse.toDir := end_ray_toDir_rev_toDir_of_ang_rev_ang pr₂ pr₁
  have J₁: (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.end_ray.reverse.toDir = - (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.end_ray.toDir := (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.end_ray.toDir_of_rev_eq_neg_toDir
  have J₂: (TRI_nd qdr_cvx.point₁ qdr_cvx.point₂ qdr_cvx.point₃ qdr_cvx.not_colinear₁₂₃).angle₃.end_ray.toDir = qdr_cvx.edge_nd₂₃.reverse.toDir := by rfl
  have J₃: (TRI_nd qdr_cvx.point₃ qdr_cvx.point₄ qdr_cvx.point₁ qdr_cvx.not_colinear₃₄₁).angle₃.end_ray.toDir = qdr_cvx.edge_nd₁₄.toDir := by rfl
  have J₄: qdr_cvx.edge_nd₂₃.reverse.toDir = - qdr_cvx.edge_nd₂₃.toDir := qdr_cvx.edge_nd₂₃.toDir_of_rev_eq_neg_toDir
  rw [J₁, J₂, J₃, J₄] at near
  simp only [neg_inj] at near
  have close: qdr_cvx.edge_nd₂₃.toProj = qdr_cvx.edge_nd₁₄.toProj := by
    apply Dir.toProj_eq_toProj_iff.mpr
    left
    exact near
  constructor
  exact h₁
  exact close.symm
  -- Done!

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AB ∥ CD and AB = CD, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_nd_of_para_eq_length_variant (h₁ : (SEG_nd A B (Quadrilateral_cvx.nd₁₂ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd C D (Quadrilateral_cvx.nd₃₄ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (SEG A B).length = (SEG C D).length) : QDR A B C D IsPRG_nd := by
  unfold Quadrilateral.IsParallelogram_nd
  by_cases j: QDR A B C D IsConvex
  simp only [j, dite_true]
  exact
    is_prg_nd_of_para_eq_length (Quadrilateral_cvx.mk_is_convex (Eq.mpr_prop (eq_true j) True.intro))
      h₁ h₂
  simp only [j, dite_false]
  exact j h

/-- Given Quadrilateral_cvx qdr_cvx, and qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃ and (qdr_cvx.edge_nd₁₄).1.length = (qdr_cvx.edge_nd₂₃).1.length, qdr_cvx is a Parallelogram_nd. -/
theorem is_prg_nd_of_para_eq_length' (h₁ : qdr_cvx.edge_nd₁₄ ∥ qdr_cvx.edge_nd₂₃) (h₂ : qdr_cvx.edge_nd₁₄.1.length = qdr_cvx.edge_nd₂₃.1.length) : qdr_cvx.IsParallelogram_nd := by
  let permute_convex := Quadrilateral_cvx.mk_is_convex qdr_cvx.permute_is_convex
  have K₁: permute_convex.edge_nd₁₂.toProj = qdr_cvx.edge_nd₂₃.toProj := by rfl
  have K₂: permute_convex.edge_nd₁₂.1.length = qdr_cvx.edge_nd₂₃.1.length := by rfl
  have j₂: permute_convex.edge_nd₃₄ = qdr_cvx.edge_nd₁₄.reverse := by rfl
  have K₃: permute_convex.edge_nd₃₄.toProj = qdr_cvx.edge_nd₁₄.toProj := by
    rw [j₂]
    apply SegND.toProj_of_rev_eq_toProj
  have K₄: permute_convex.edge_nd₃₄.1.length = qdr_cvx.edge_nd₁₄.1.length := by
    rw [j₂]
    apply SegND.length_of_rev_eq_length
  have H₁: permute_convex.edge_nd₁₂.toProj = permute_convex.edge_nd₃₄.toProj := by
    rw [K₁, K₃]
    unfold parallel at h₁
    exact h₁.symm
  have H₂: permute_convex.edge_nd₁₂.1.length = permute_convex.edge_nd₃₄.1.length := by
    rw [K₂, K₄]
    exact h₂.symm
  have H: permute_convex.IsParallelogram_nd := is_prg_nd_of_para_eq_length permute_convex H₁ H₂
  unfold Quadrilateral_cvx.IsParallelogram_nd
  unfold Quadrilateral_cvx.IsParallelogram_nd at H
  rcases H with ⟨_,b⟩
  constructor
  have P₁: permute_convex.edge_nd₂₃ = qdr_cvx.edge_nd₃₄ := by rfl
  have p₂: permute_convex.edge_nd₁₄ = qdr_cvx.edge_nd₁₂.reverse := by rfl
  have p₃: permute_convex.edge_nd₃₄ = qdr_cvx.edge_nd₁₄.reverse := by rfl
  have P₂: permute_convex.edge_nd₁₄.reverse.toProj = permute_convex.edge_nd₁₄.toProj := by apply permute_convex.edge_nd₁₄.toProj_of_rev_eq_toProj
  rw [P₁, p₂] at b
  have b': qdr_cvx.edge_nd₃₄∥qdr_cvx.edge_nd₁₂.reverse := b.symm
  apply SegND.para_rev_of_para at b'
  -- constructor
  exact b'.symm
  exact h₁

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and AD ∥ BC and AD = BC, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_nd_of_para_eq_length'_variant (h₁ : (SEG_nd A D (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex h))) ∥ (SEG_nd B C (Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (SEG A D).length = (SEG B C).length) : QDR A B C D IsPRG_nd := by
  unfold Quadrilateral.IsParallelogram_nd
  by_cases j: QDR A B C D IsConvex
  simp only [j, dite_true]
  exact
    is_prg_nd_of_para_eq_length' (Quadrilateral_cvx.mk_is_convex (Eq.mpr_prop (eq_true j) True.intro))
      h₁ h₂
  simp only [j, dite_false]
  exact j h

/-- Given Quadrilateral_cvx qdr_cvx, and angle₁ = angle₃ and angle₂ = angle₄, qdr_cvx is a Parallelogram_nd. -/
theorem is_prg_nd_of_eq_angle_value_eq_angle_value (h₁ : qdr_cvx.angle₁ = qdr_cvx.angle₃) (h₂ : qdr_cvx.angle₂ = qdr_cvx.angle₄) : qdr_cvx.IsParallelogram_nd := by
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and ∠DAB = ∠BCD and ∠ABC = ∠CDA, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_of_eq_angle_value_eq_angle_value_variant (h₁ : (ANG D A B (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex h)) (Quadrilateral_cvx.nd₁₂ (Quadrilateral_cvx.mk_is_convex h))) = (ANG B C D (Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex h)).symm (Quadrilateral_cvx.nd₃₄ (Quadrilateral_cvx.mk_is_convex h)))) (h₂ : (ANG A B C (Quadrilateral_cvx.nd₁₂ (Quadrilateral_cvx.mk_is_convex h)).symm (Quadrilateral_cvx.nd₂₃ (Quadrilateral_cvx.mk_is_convex h))) = (ANG C D A (Quadrilateral_cvx.nd₃₄ (Quadrilateral_cvx.mk_is_convex h)).symm (Quadrilateral_cvx.nd₁₄ (Quadrilateral_cvx.mk_is_convex h)).symm)) : QDR A B C D IsPRG_nd := by
  unfold Quadrilateral.IsParallelogram_nd
  by_cases j: QDR A B C D IsConvex
  simp only [j, dite_true]
  exact
    is_prg_nd_of_eq_angle_value_eq_angle_value
      (Quadrilateral_cvx.mk_is_convex (Eq.mpr_prop (eq_true j) True.intro)) h₁ h₂
  simp only [j, dite_false]
  exact j h

/-- Given Quadrilateral_cvx qdr_cvx, and qdr_cvx.diag_nd₁₃.1.midpoint = qdr_cvx.diag_nd₂₄.1.midpoint, qdr_cvx is a Parallelogram_nd. -/
theorem is_prg_nd_of_diag_inx_eq_mid_eq_mid (h' : qdr_cvx.diag_nd₁₃.1.midpoint = qdr_cvx.diag_nd₂₄.1.midpoint) : qdr_cvx.IsParallelogram_nd := by
  /-let midpoint := qdr_cvx.diag_nd₁₃.1.midpoint
  have qdr_cvx_eq_midpoint_of_diag₂₄: qdr_cvx.diag_nd₂₄.1.midpoint = midpoint := by rw [h'.symm]
  have midpoint_Liesint_diag₁₃: midpoint LiesInt qdr_cvx.diag_nd₁₃ := by apply SegND.midpt_lies_int
  have midpoint_Liesint_diag₂₄: midpoint LiesInt qdr_cvx.diag_nd₂₄ := by
    rw [qdr_cvx_eq_midpoint_of_diag₂₄.symm]
    apply SegND.midpt_lies_int
  have nd₁₅: qdr_cvx.point₁ ≠ midpoint := by apply (SegND_midpoint_not_eq_source qdr_cvx.diag_nd₁₃).symm
  have nd₂₅: qdr_cvx.point₂ ≠ midpoint := by
    have h: qdr_cvx.point₂ ≠ qdr_cvx.diag_nd₂₄.1.midpoint := by apply (SegND_midpoint_not_eq_source qdr_cvx.diag_nd₂₄).symm
    rw [qdr_cvx_eq_midpoint_of_diag₂₄] at h
    exact h
  have nd₃₅: qdr_cvx.point₃ ≠ midpoint := by apply (SegND_midpoint_not_eq_target qdr_cvx.diag_nd₁₃).symm
  have nd₄₅: qdr_cvx.point₄ ≠ midpoint := by
    have h: qdr_cvx.point₄ ≠ qdr_cvx.diag_nd₂₄.1.midpoint := by apply (SegND_midpoint_not_eq_target qdr_cvx.diag_nd₂₄).symm
    rw [qdr_cvx_eq_midpoint_of_diag₂₄] at h
    exact h
  have prep₁_pre: (SEG_nd qdr_cvx.point₁ midpoint nd₁₅.symm).length = (SEG_nd midpoint qdr_cvx.point₃ nd₃₅).length := by apply dist_target_eq_dist_source_of_midpt
  have prep₁_pre': (SEG_nd qdr_cvx.point₁ midpoint nd₁₅.symm).length = (SEG_nd midpoint qdr_cvx.point₁ nd₁₅).length := by   apply length_of_rev_eq_length'-/

  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsConvex, and the midpoint of the diagonal AC and BD is the same, Quadrilateral ABCD is a Parallelogram_nd. -/
theorem is_prg_of_diag_inx_eq_mid_eq_mid_variant (h' : (SEG A C).midpoint = (SEG B D).midpoint) : QDR A B C D IsPRG_nd := by
  unfold Quadrilateral.IsParallelogram_nd
  by_cases j: QDR A B C D IsConvex
  simp only [j, dite_true]
  exact
    is_prg_nd_of_diag_inx_eq_mid_eq_mid
      (Quadrilateral_cvx.mk_is_convex (Eq.mpr_prop (eq_true j) True.intro)) h'
  simp only [j, dite_false]
  exact j h

/-- Given Quadrilateral qdr and qdr IsParallelogram, and qdr.1, qdr.2, qdr.3 are not colinear, then qdr IsParallelogram_nd.  -/
theorem is_prg_nd_of_is_prg_not_colinear₁₂₃ (h₁ : qdr.IsParallelogram) (h₂ : ¬ colinear qdr.1 qdr.2 qdr.3) : qdr.IsParallelogram_nd := by sorry

/-- Given Quadrilateral qdr and qdr IsParallelogram, and qdr.2, qdr.3, qdr.4 are not colinear, then qdr IsParallelogram_nd.  -/
theorem is_prg_nd_of_is_prg_not_colinear₂₃₄ (h₁ : qdr.IsParallelogram) (h₂ : ¬ colinear qdr.2 qdr.3 qdr.4) : qdr.IsParallelogram_nd := by sorry

/-- Given Quadrilateral qdr and qdr IsParallelogram, and qdr.3, qdr.4, qdr.1 are not colinear, then qdr IsParallelogram_nd.  -/
theorem is_prg_nd_of_is_prg_not_colinear₃₄₁ (h₁ : qdr.IsParallelogram) (h₂ : ¬ colinear qdr.3 qdr.4 qdr.1) : qdr.IsParallelogram_nd := by sorry

/-- Given Quadrilateral qdr and qdr IsParallelogram, and qdr.4, qdr.1, qdr.2 are not colinear, then qdr IsParallelogram_nd.  -/
theorem is_prg_nd_of_is_prg_not_colinear₄₁₂ (h₁ : qdr.IsParallelogram) (h₂ : ¬ colinear qdr.4 qdr.1 qdr.2) : qdr.IsParallelogram_nd := by sorry

end criteria

section property
variable {A B C D : P}
variable {P : Type _} [EuclideanPlane P] (qdr : Quadrilateral P)

/-- Given Quadrilateral qdr IsPRG_nd, Quadrilateral qdr IsConvex. -/
theorem is_convex_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.IsConvex := by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases j: qdr.IsConvex
  · simp only [j]
  · simp only [j, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, Quadrilateral ABCD IsConvex. -/
theorem is_convex_of_is_prg_nd_variant (h : QDR A B C D IsPRG_nd) : (QDR A B C D) IsConvex := by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases j: QDR A B C D IsConvex
  · simp only [j]
  · simp only [j, dite_false] at h

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₃ ≠ qdr.point₁. -/
theorem nd₁₃_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₃ ≠ qdr.point₁ := by
  have s : qdr.IsConvex:= is_convex_of_is_prg_nd qdr h
  unfold Quadrilateral.IsConvex at s
  by_cases j: qdr.point₃ ≠ qdr.point₁
  · simp only [ne_eq, j, not_false_eq_true]
  simp at j
  · simp only [j, ne_eq, not_true_eq_false, false_and, dite_not, dite_false] at s

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, C ≠ A. -/
theorem nd₁₃_of_is_prg_nd_variant (h : QDR A B C D IsPRG_nd) : C ≠ A := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_nd_variant h
  unfold Quadrilateral.IsConvex at s
  by_cases j: C ≠ A
  · simp only [ne_eq, j, not_false_eq_true]
  simp at j
  · simp only [j, ne_eq, not_true_eq_false, false_and, dite_not, dite_false] at s

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₄ ≠ qdr.point₂. -/
theorem nd₂₄_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₄ ≠ qdr.point₂ := by
  have s : qdr.IsConvex:= is_convex_of_is_prg_nd qdr h
  unfold Quadrilateral.IsConvex at s
  by_cases j: qdr.point₄ ≠ qdr.point₂
  · simp only [ne_eq, j, not_false_eq_true]
  simp at j
  · simp only [ne_eq, j, not_true_eq_false, and_false, dite_not, dite_false] at s

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, D ≠ B. -/
theorem nd₂₄_of_is_prg_nd_variant (h : QDR A B C D IsPRG_nd) : D ≠ B := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_nd_variant h
  unfold Quadrilateral.IsConvex at s
  by_cases j: D ≠ B
  · simp only [ne_eq, j, not_false_eq_true]
  simp at j
  · simp only [ne_eq, j, not_true_eq_false, and_false, dite_not, dite_false] at s

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₂ ≠ qdr.point₁. -/
theorem nd₁₂_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₂ ≠ qdr.point₁ := by
  have s : qdr.IsConvex:= is_convex_of_is_prg_nd qdr h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₂

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, B ≠ A. -/
theorem nd₁₂_of_is_prg_nd_variant (h : QDR A B C D IsPRG_nd) : B ≠ A := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_nd_variant h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₂

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₃ ≠ qdr.point₂. -/
theorem nd₂₃_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₃ ≠ qdr.point₂ := by
  have s : qdr.IsConvex:= is_convex_of_is_prg_nd qdr h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₂₃

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, C ≠ B. -/
theorem nd₂₃_of_is_prg_nd_variant (h : QDR A B C D IsPRG_nd) : C ≠ B := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_nd_variant h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₂₃

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₄ ≠ qdr.point₃. -/
theorem nd₃₄_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₄ ≠ qdr.point₃ := by
  have s : qdr.IsConvex:= is_convex_of_is_prg_nd qdr h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₃₄

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, D ≠ C. -/
theorem nd₃₄_of_is_prg_nd_variant (h : QDR A B C D IsPRG_nd) : D ≠ C := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_nd_variant h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₃₄

/-- Given Quadrilateral qdr IsPRG_nd, qdr.point₄ ≠ qdr.point₁. -/
theorem nd₁₄_of_is_prg_nd (h : qdr.IsParallelogram_nd) : qdr.point₄ ≠ qdr.point₁ := by
  have s : qdr.IsConvex:= is_convex_of_is_prg_nd qdr h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₄

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, D ≠ A. -/
theorem nd₁₄_of_is_prg_nd_variant (h : QDR A B C D IsPRG_nd) : D ≠ A := by
  have s : (QDR A B C D) IsConvex:= is_convex_of_is_prg_nd_variant h
  exact (Quadrilateral_cvx.mk_is_convex s).nd₁₄

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are parallel namely (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_abstract qdr h)) ∥ (SEG_nd qdr.point₃ qdr.point₄ (nd₃₄_of_is_prg_abstract qdr h)). -/
theorem para_of_is_prg_nd (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_nd qdr h)) ∥ (SEG_nd qdr.point₃ qdr.point₄ (nd₃₄_of_is_prg_nd qdr h)):= by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases k: qdr.IsConvex
  simp only [k, dite_true] at h
  unfold Quadrilateral_cvx.IsParallelogram_nd at h
  rcases h with ⟨a,b⟩
  exact a
  simp only [k, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are parallel namely AB ∥ CD. -/
theorem para_of_is_prg_nd_variant (h : QDR A B C D IsPRG_nd) : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ (SEG_nd C D (nd₃₄_of_is_prg_nd_variant h)) := by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  unfold Quadrilateral_cvx.IsParallelogram_nd at h
  rcases h with ⟨a,b⟩
  exact a
  simp only [k, dite_false] at h

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are parallel namely (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_abstract qdr h)) ∥ (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_abstract qdr h)). -/
theorem para_of_is_prg_nd' (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_nd qdr h)) ∥ (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_nd qdr h)):= by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases k: qdr.IsConvex
  simp only [k, dite_true] at h
  unfold Quadrilateral_cvx.IsParallelogram_nd at h
  rcases h with ⟨_,b⟩
  exact b
  simp only [k, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are parallel namely AD ∥ BC. -/
theorem para_of_is_prg_nd'_variant (h : QDR A B C D IsPRG_nd) : (SEG_nd A D (nd₁₄_of_is_prg_nd_variant h)) ∥ SEG_nd B C (nd₂₃_of_is_prg_nd_variant h) := by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  unfold Quadrilateral_cvx.IsParallelogram_nd at h
  rcases h with ⟨a,b⟩
  exact b
  simp only [k, dite_false] at h

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are equal namely (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_abstract qdr h)).1.length = (SEG_nd qdr.point₃ qdr.point₄ (nd₁₂_of_is_prg_abstract qdr h)).1.length. -/
theorem eq_length_of_is_prg_nd (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₂ (nd₁₂_of_is_prg_nd qdr h)).1.length = (SEG_nd qdr.point₃ qdr.point₄ (nd₃₄_of_is_prg_nd qdr h)).1.length := by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases k: qdr.IsConvex
  simp only [k, dite_true] at h
  let qdr_cvx := Quadrilateral_cvx.mk_is_convex k

  sorry
  simp only [k, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are equal namely (SEG A B).length = (SEG C D).length. -/
theorem eq_length_of_is_prg_nd_variant  (h : QDR A B C D IsPRG_nd) : (SEG A B).length = (SEG C D).length := by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  sorry
  simp only [k, dite_false] at h

/-- Given Quadrilateral qdr IsPRG_nd, the opposite sides are equal namely (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_abstract qdr h)).1.length = (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_abstract qdr h)).1.length. -/
theorem eq_length_of_is_prg_nd'  (h : qdr.IsParallelogram_nd) : (SEG_nd qdr.point₁ qdr.point₄ (nd₁₄_of_is_prg_nd qdr h)).1.length = (SEG_nd qdr.point₂ qdr.point₃ (nd₂₃_of_is_prg_nd qdr h)).1.length := by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases k: qdr.IsConvex
  simp only [k, dite_true] at h
  sorry
  simp only [k, dite_false] at h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite sides are equal namely (SEG A D).length = (SEG B C).length. -/
theorem eq_length_of_is_prg_nd'_variant  (h : QDR A B C D IsPRG_nd) : (SEG A D).length = (SEG B C).length := by
  unfold Quadrilateral.IsParallelogram_nd at h
  by_cases k: (QDR A B C D) IsConvex
  simp only [k, dite_true] at h
  sorry
  simp only [k, dite_false] at h

/-- Given Quadrilateral qdr IsPRG_nd, the opposite angles are equal namely ANG qdr.point₁ qdr.point₂ qdr.point₃ = ANG qdr.point₃ qdr.point₄ qdr.point₁. -/
theorem eq_angle_value_of_is_prg_nd (h : qdr.IsParallelogram_nd) : ANG qdr.point₁ qdr.point₂ qdr.point₃ ((nd₁₂_of_is_prg_nd qdr h).symm) (nd₂₃_of_is_prg_nd qdr h) = ANG qdr.point₃ qdr.point₄ qdr.point₁ ((nd₃₄_of_is_prg_nd qdr h).symm) ((nd₁₄_of_is_prg_nd qdr h).symm) := by
  unfold Quadrilateral.IsParallelogram_nd at h
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite angles are equal namely ANG A B C = ANG C D A. -/
theorem eq_angle_value_of_is_prg_nd_variant (h : QDR A B C D IsPRG_nd) : ANG A B C ((nd₁₂_of_is_prg_nd_variant h).symm) (nd₂₃_of_is_prg_nd_variant h) = ANG C D A ((nd₃₄_of_is_prg_nd_variant h).symm) ((nd₁₄_of_is_prg_nd_variant h).symm) := by
  have h₁ : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ SEG_nd C D (nd₃₄_of_is_prg_nd_variant h) := para_of_is_prg_nd_variant h
  have h₂ : (SEG_nd A D (nd₁₄_of_is_prg_nd_variant h)) ∥ SEG_nd B C (nd₂₃_of_is_prg_nd_variant h) := para_of_is_prg_nd'_variant h
  unfold Quadrilateral.IsParallelogram_nd at h
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the opposite angles are equal namely ANG qdr.point₄ qdr.point₁ qdr.point₂ = ANG qdr.point₂ qdr.point₃ qdr.point₄. -/
theorem eq_angle_value_of_is_prg_nd' (h : qdr.IsParallelogram_nd) : ANG qdr.point₄ qdr.point₁ qdr.point₂ ((nd₁₄_of_is_prg_nd qdr h)) ((nd₁₂_of_is_prg_nd qdr h)) = ANG qdr.point₂ qdr.point₃ qdr.point₄ ((nd₂₃_of_is_prg_nd qdr h).symm) (nd₃₄_of_is_prg_nd qdr h):= by
  unfold Quadrilateral.IsParallelogram_nd at h
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the opposite angles are equal namely ANG D A B = ANG B C D. -/
theorem eq_angle_value_of_is_prg_nd'_variant (h : QDR A B C D IsPRG_nd) : ANG D A B (nd₁₄_of_is_prg_nd_variant h) (nd₁₂_of_is_prg_nd_variant h) = ANG B C D ((nd₂₃_of_is_prg_nd_variant h).symm) (nd₃₄_of_is_prg_nd_variant h) := by
  have h₁ : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ SEG_nd C D (nd₃₄_of_is_prg_nd_variant h) := para_of_is_prg_nd_variant h
  have h₂ : (SEG_nd A D (nd₁₄_of_is_prg_nd_variant h)) ∥ SEG_nd B C (nd₂₃_of_is_prg_nd_variant h) := para_of_is_prg_nd'_variant h
  unfold Quadrilateral.IsParallelogram_nd at h
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ = (SEG qdr.point₁ qdr.point₃).midpoint. -/
theorem eq_midpt_of_diag_inx_of_is_prg_nd (h : qdr.IsParallelogram_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ (is_convex_of_is_prg_nd qdr h)) = (SEG qdr.point₁ qdr.point₃).midpoint :=
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx A B C D = (SEG A C).midpoint. -/
theorem eq_midpt_of_diag_inx_of_is_prg_nd_variant (h : QDR A B C D IsPRG_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg_nd_variant h)) = (SEG A C).midpoint :=
  have h : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ SEG_nd C D (nd₃₄_of_is_prg_nd_variant h) := para_of_is_prg_nd_variant h
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ = (SEG qdr.point₂ qdr.point₄).midpoint. -/
theorem eq_midpt_of_diag_inx_of_is_prg_nd' (h : qdr.IsParallelogram_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx qdr.point₁ qdr.point₂ qdr.point₃ qdr.point₄ (is_convex_of_is_prg_nd qdr h)) = (SEG qdr.point₂ qdr.point₄).midpoint :=
  sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the intersection of diagonals is the midpoint of one diagonal namely Quadrilateral_cvx.diag_inx QDR_cvx A B C D = (SEG B D).midpoint. -/
theorem eq_midpt_of_diag_inx_of_is_prg_nd'_variant (h : QDR A B C D IsPRG_nd) : Quadrilateral_cvx.diag_inx (QDR_cvx A B C D (is_convex_of_is_prg_nd_variant h)) = (SEG B D).midpoint :=
  have h : (SEG_nd A B (nd₁₂_of_is_prg_nd_variant h)) ∥ SEG_nd C D (nd₃₄_of_is_prg_nd_variant h) := para_of_is_prg_nd_variant h
  sorry

/-- Given Quadrilateral qdr IsPRG_nd, the midpoints of the diagonals are the same. -/
theorem eq_midpt_of_diag_of_is_prg (h : qdr.IsParallelogram_nd) : (SEG qdr.point₁ qdr.point₃).midpoint = (SEG qdr.point₂ qdr.point₄).midpoint := by
  rw [← eq_midpt_of_diag_inx_of_is_prg_nd qdr h]
  rw [eq_midpt_of_diag_inx_of_is_prg_nd' qdr h]

/-- Given four points A B C D and Quadrilateral ABCD IsPRG_nd, the midpoints of the diagonals are the same. -/
theorem eq_midpt_of_diag_of_is_prg_variant (h : QDR A B C D IsPRG_nd) : (SEG A C).midpoint = (SEG B D).midpoint := eq_midpt_of_diag_of_is_prg (QDR A B C D) h

/-- Given Quadrilateral qdr IsPRG_nd, then Quadrilateral IsPRG. -/
theorem prg_nd_is_prg (h : qdr.IsParallelogram_nd) : qdr.IsParallelogram := by sorry

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, then Quadrilateral ABCD IsPRG. -/
theorem prg_nd_is_prg_variant (h : QDR A B C D IsPRG_nd) : QDR A B C D IsPRG := prg_nd_is_prg (QDR A B C D) h

/-- Given Quadrilateral qdr IsPRG_nd, then VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃. -/
theorem eq_vec_of_is_prg_nd (h : qdr.IsParallelogram_nd) : VEC qdr.point₁ qdr.point₂ = VEC qdr.point₄ qdr.point₃ := prg_nd_is_prg qdr h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, then VEC A B = VEC D C. -/
theorem eq_vec_of_is_prg_nd_variant (h : QDR A B C D IsPRG_nd) : VEC A B = VEC D C := eq_vec_of_is_prg_nd (QDR A B C D) h

/-- Given Quadrilateral qdr IsPRG_nd, then VEC qdr.point₁ qdr.point₄ = VEC qdr.point₂ qdr.point₃. -/
theorem eq_vec_of_is_prg_nd' (h : qdr.IsParallelogram_nd) : VEC qdr.point₁ qdr.point₄ = VEC qdr.point₂ qdr.point₃ := by
  rw [← vec_add_vec qdr.point₁ qdr.point₂ qdr.point₄]
  rw [← vec_add_vec qdr.point₂ qdr.point₄ qdr.point₃]
  rw [eq_vec_of_is_prg_nd qdr h]
  exact add_comm (VEC qdr.point₄ qdr.point₃) (VEC qdr.point₂ qdr.point₄)

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, then VEC A D = VEC B C. -/
theorem eq_vec_of_is_prg_nd'_variant (h : QDR A B C D IsPRG_nd) : VEC A D = VEC B C := eq_vec_of_is_prg_nd' (QDR A B C D) h

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the sum of the squares of each side equals to the sum of the squares of the diagonals namely 2 * (SEG qdr.point₁ qdr.point₂).length ^ 2 + 2 * (SEG qdr.point₂ qdr.point₃).length ^ 2 = (SEG qdr.point₁ qdr.point₃).length ^ 2 + (SEG qdr.point₂ qdr.point₄).length ^ 2. -/
theorem parallelogram_law (h : qdr.IsParallelogram_nd) : 2 * (SEG qdr.point₁ qdr.point₂).length ^ 2 + 2 * (SEG qdr.point₂ qdr.point₃).length ^ 2 = (SEG qdr.point₁ qdr.point₃).length ^ 2 + (SEG qdr.point₂ qdr.point₄).length ^ 2 := by
  repeat rw [Seg.length]
  repeat rw [seg_tovec_eq_vec]
  dsimp
  rw [(vec_add_vec qdr.point₁ qdr.point₂ qdr.point₃).symm]
  rw [(vec_add_vec qdr.point₂ qdr.point₃ qdr.point₄).symm]
  rw [← neg_vec qdr.point₄ qdr.point₃]
  rw [← eq_vec_of_is_prg_nd qdr h]
  rw [← sub_eq_add_neg (VEC qdr.point₂ qdr.point₃) (VEC qdr.point₁ qdr.point₂)]
  rw [add_comm (VEC qdr.point₁ qdr.point₂) (VEC qdr.point₂ qdr.point₃)]
  repeat rw [sq]
  rw [(parallelogram_law_with_norm ℝ (VEC qdr.point₂ qdr.point₃) (VEC qdr.point₁ qdr.point₂))]
  ring

/-- Given four points ABCD and Quadrilateral ABCD IsPRG_nd, the sum of the squares of each side equals to the sum of the squares of the diagonals namely 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2. -/
theorem parallelogram_law_variant (h : QDR A B C D IsPRG_nd) : 2 * (SEG A B).length ^ 2 + 2 * (SEG B C).length ^ 2 = (SEG A C).length ^ 2 + (SEG B D).length ^ 2 := parallelogram_law (QDR A B C D) h

end property

end EuclidGeom
