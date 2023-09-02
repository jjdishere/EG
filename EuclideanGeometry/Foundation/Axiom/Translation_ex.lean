import EuclideanGeometry.Foundation.Axiom.Ray
import EuclideanGeometry.Foundation.Axiom.Ray_ex1

/- The purpose of of this file is to establish results about parallel translate along a vector. Presumably, all results are "invariant" under parallel translation. -/

namespace EuclidGeom

namespace GDSeg

variable {P: Type _} [EuclideanPlane P] (v : ℝ × ℝ) (gseg : GDSeg P)

-- parallel translate a generalized directed segments

def translate (gseg : GDSeg P) (v : ℝ × ℝ) : GDSeg P where
  source := v +ᵥ gseg.source
  target := v +ᵥ gseg.target

-- parallel translate a nontrivial generalized directed segment is nontrivial

theorem GDSeg.non_triv_of_trans_non_triv (gseg : GDSeg P) (v : ℝ × ℝ) (nontriv : gseg.source ≠ gseg.target) : (GDSeg.translate gseg v).source ≠ (GDSeg.translate gseg v).target := by sorry


end GDSeg

namespace DSeg

variable {P: Type _} [EuclideanPlane P] (v : ℝ × ℝ) (seg : DSeg P)

-- parallel translate a directed segments

def translate (seg : DSeg P) (v : ℝ × ℝ) : DSeg P where
  source := sorry
  target := v +ᵥ seg.target
  direction := sorry
  on_ray := sorry
  non_triv := sorry

end DSeg

namespace Ray

variable {P: Type _} [EuclideanPlane P] (v : ℝ × ℝ) (ray : Ray P)

-- parallel translate a ray

def translate (ray : Ray P) (v : ℝ × ℝ) : Ray P where
  source := sorry
  direction := sorry

end Ray

section compatibility

variable {P: Type _} [EuclideanPlane P] (v : ℝ × ℝ) (gseg : GDSeg P) (seg : DSeg P) (ray : Ray P)

-- check compatibility between coersion and prallel translation

theorem DSeg.trans_of_toGDSeg_eq_toGDSeg_trans : (DSeg.translate seg v).toGDSeg = GDSeg.translate seg.toGDSeg v := by sorry

theorem GDSeg.trans_of_toDSeg_eq_toDSeg_trans (nontriv : gseg.source ≠ gseg.target) : (GDSeg.translate gseg v).toDSeg_of_nontriv (GDSeg.non_triv_of_trans_non_triv gseg v nontriv) = DSeg.translate (gseg.toDSeg_of_nontriv nontriv) v := by sorry


end compatibility








end EuclidGeom