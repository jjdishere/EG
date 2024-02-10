import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

namespace Problem_25

/-
Let $\triangle ABC$ be an isoceles triangle with $AB = AC$. Let $D, E$ be two points lying on segment $BC$ such that $B, D, E, C$ lies on segment $BC$ in this order and that $AD = AE$.
Prove that $\triangle ABD \cong \triangle ACE$
-/

structure Setting (Plane : Type _) [EuclideanPlane Plane] where
-- Let $\triangle ABC$ be an isoceles triangle with $AB = AC$.
  A : Plane
  B : Plane
  C : Plane
  not_collinear_ABC : ¬ Collinear A B C
  ABC_isoceles : (▵ A B C).IsIsoceles
-- Let $D, E$ be two points lying on segment $BC$ such that $B, D, E, C$ lies on segment $BC$ in this order
  D : Plane
  E : Plane
  D_int_BE : D LiesInt (SEG B E)
  E_int_DC : E LiesInt (SEG D C)
-- such that $AD = AE$
  AD_eq_AE : (SEG A D).length = (SEG A E).length

abbrev lelem {P : Type _} [EuclideanPlane P] (A : P) {l : DirLine P} (ha : A LiesOn l) : l.carrier.Elem := ⟨A, ha⟩

theorem result {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane) : (▵ e.A e.B e.D) ≅ₐ (▵ e.A e.C e.E) := by
  haveI : PtNe e.A e.C := ⟨(ne_of_not_collinear e.not_collinear_ABC).2.1⟩
  haveI : PtNe e.B e.A := ⟨(ne_of_not_collinear e.not_collinear_ABC).2.2⟩
  haveI : PtNe e.D e.B := ⟨e.D_int_BE.2⟩
  haveI : PtNe e.E e.C := ⟨(Seg.lies_int_rev_iff_lies_int.mpr e.E_int_DC).2⟩
  sorry

end Problem_25

end EuclidGeom
