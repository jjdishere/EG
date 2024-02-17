import EuclideanGeometry.Foundation.Axiom.Linear.Ratio

noncomputable section
namespace EuclidGeom

variable {P : Type*} [EuclideanPlane P] {A B C D X Y Z W : P}

theorem ratio_eq_ratio_perm (ha : Collinear A B C) (hx : Collinear X Y Z) (h : divratio A B C = divratio X Y Z) : divratio B C A = divratio Y Z X := sorry

theorem ratio_eq_ratio_flip₁ (ha : Collinear A B C) (hx : Collinear X Y Z) (h : divratio A B C = divratio X Y Z) : divratio A C B = divratio X Z Y := sorry

theorem ratio_eq_ratio_flip₂ (ha : Collinear A B C) (hx : Collinear X Y Z) (h : divratio A B C = divratio X Y Z) : divratio C B A = divratio Z Y X := sorry

theorem ratio_eq_ratio_flip₃ (ha : Collinear A B C) (hx : Collinear X Y Z) (h : divratio A B C = divratio X Y Z) : divratio B A C = divratio Y X Z := sorry

theorem ratio_eq_ratio_trans [PtNe C D] [PtNe Z W] {l₁ l₂ : Line P} (ha : A LiesOn l₁) (hb : B LiesOn l₁) (hc : C LiesOn l₁) (hd : D LiesOn l₁) (hx : X LiesOn l₂) (hy : Y LiesOn l₂) (hz : Z LiesOn l₂) (hw : W LiesOn l₂) (h₁ : divratio A C D = divratio X Z W) (h₂ : divratio B C D = divratio Y Z W) : divratio A B C = divratio X Y Z := sorry

theorem Seg.midpt_ratio {s : Seg P} : divratio s.midpoint s.source s.target = - 1 := sorry

theorem seg_midpt_ratio (A B : P) : divratio (SEG A B).midpoint A B = - 1 := sorry

theorem ratio_eq_of_divratio_eq [PtNe A C] [PtNe X Z] (ha : Collinear A B C) (hx : Collinear X Y Z) (h : divratio A B C = divratio X Y Z) : dist A B / dist A C = dist X Y / dist X Z := sorry

end EuclidGeom
