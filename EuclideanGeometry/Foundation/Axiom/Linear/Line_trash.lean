import EuclideanGeometry.Foundation.Axiom.Linear.Line
import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem is_inx_of_line_inx {A : P} {l₁ l₂ : Line P} (h₁ : A LiesOn l₁) (h₂ : A LiesOn l₂) (h : ¬ l₁ ∥ l₂) : A IsInxOf l₁ l₂ := sorry

theorem lieson_seg_nd_toline_lieson_seg_nd {A : P} {l : Seg_nd P} (h : A LiesOn l) : A LiesOn l.toLine := sorry

end EuclidGeom
