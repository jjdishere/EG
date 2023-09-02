import EuclideanGeometry.Foundation.Axiom.Ray
import EuclideanGeometry.Foundation.Axiom.Ray_ex1


namespace EuclidGeom

variable {P: Type _} [EuclideanPlane P] (gseg : GDirSeg P) (seg : DirSeg P) (ray : Ray P) (v : ℝ × ℝ)

/- Parallel transport a (generalized) directed segments or a ray along a vector -/

def GDirSeg.trans_by_vec : GDirSeg P where
  source := v +ᵥ gseg.source
  target := v +ᵥ gseg.target

def DirSeg.trans_by_vec : DirSeg P where
  source := sorry
  target := v +ᵥ seg.target
  direction := sorry
  on_ray := sorry
  non_triv := sorry

def Ray.trans_by_vec : Ray P where
  source := sorry
  direction := sorry


theorem GDirSeg.non_triv_of_trans_non_triv (nontriv : gseg.source ≠ gseg.target) : (GDirSeg.trans_by_vec gseg v).source ≠ (GDirSeg.trans_by_vec gseg v).target := by sorry

-- check compatibility between coersion and prallel transport

theorem DirSeg.trans_of_toGDirSeg_eq_toGDirSeg_trans : (DirSeg.trans_by_vec seg v).toGDirSeg = GDirSeg.trans_by_vec seg.toGDirSeg v := by sorry

theorem GDirSeg.trans_of_toDirSeg_eq_toDirSeg_trans (nontriv : gseg.source ≠ gseg.target) : (GDirSeg.trans_by_vec gseg v).toDirSeg_of_nontriv (GDirSeg.non_triv_of_trans_non_triv gseg v nontriv) = DirSeg.trans_by_vec (gseg.toDirSeg_of_nontriv nontriv) v := by sorry



/- Parallel transport a (generalized) directed segments to start at a given point  -/

-- Parallel transport generalized directed segment gseg to start at a given point a ∈ P.


def GDirSeg.parellel_trans_to_source (a : P) : GDirSeg P where
  source := a
  target := gseg.toVec +ᵥ a




end EuclidGeom