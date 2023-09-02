import EuclideanGeometry.Foundation.Axiom.Ray


namespace EuclidGeom

variable {P: Type _} [EuclideanPlane P] (gseg : GDirSeg P) (seg : DirSeg P) (ray : Ray P)

/- source and targets are on (generalized) directed segments -/

theorem GDirSeg.source_lies_on_segments : gseg.source LiesOnGDirSeg gseg := by sorry

theorem DirSeg.source_lies_on_segments : seg.source LiesOnDirSeg seg := by sorry

theorem GDirSeg.target_lies_on_segments : gseg.source LiesOnGDirSeg gseg := by sorry

theorem DirSeg.target_lies_on_segments : seg.source LiesOnDirSeg seg := by sorry


/- reverse the direction of a (generalized) directed segment -/

-- definition of reversion of the direction of a generalized directed segment

def GDirSeg.reverse  : GDirSeg P where
  source := gseg.target
  target := gseg.source

-- double reverse a generalized directed segment gets back to itself
theorem GDirSeg.double_rev_eq_self  : gseg.reverse.reverse = gseg := rfl


-- definition of the reversion of the direction of a directed segment
def DirSeg.reverse : DirSeg P where
  source := seg.target
  target := seg.source
  direction := -seg.direction
  on_ray := sorry
  non_triv := sorry

-- double reverse a directed segment gets back to itself
theorem DirSeg.double_rev_eq_self  : seg.reverse.reverse = seg := sorry

-- reversing the direction does not change the property that a point lies on the (generalized) directed segments.
theorem DirSeg.IsOnDirSeg_of_rev_of_IsOnDirSeg (a : P) (lieson : a LiesOnDirSeg seg) : a LiesOnDirSeg seg.reverse := sorry

theorem GDirSeg.IsOnGDirSeg_of_rev_of_IsOnGDirSeg (a : P) (lieson : a LiesOnGDirSeg gseg) : a LiesOnGDirSeg gseg.reverse := sorry

-- reversing the direction does not change the nontriviality of a generalized directed segment.
theorem GDirSeg.nontriv_of_rev_of_nontriv (nontriv : gseg.source ≠ gseg.target) : gseg.reverse.source ≠ gseg.reverse.target := sorry

-- the operation of reversing the direction commutes with coersion between directed segments and generalized directed segments.
theorem DirSeg.rev_toGDirSeg_eq_toGDirSeg_rev : seg.reverse.toGDirSeg = (seg.toGDirSeg).reverse := sorry

theorem GDirSeg.rev_toDirSeg_eq_toDirSeg_rev (nontriv : gseg.source ≠ gseg.target) : (gseg.reverse).toDirSeg_of_nontriv (GDirSeg.nontriv_of_rev_of_nontriv gseg nontriv) = (gseg.toDirSeg_of_nontriv nontriv).reverse := sorry

-- reversing the direction of a generalized directed segment will negate the coersion to vectors
theorem GDirSeg.neg_toVec_of_rev : gseg.reverse.toVec = - gseg.toVec := sorry


/- reverse the direction of a ray -/


def Ray.reverse : Ray P where
  source := ray.source
  direction := -ray.direction

theorem Ray.double_rev_eq_self : ray.reverse.reverse = ray := sorry

-- If a point lies on ray and its reversion, then it is the source

theorem Ray.eq_source_of_lies_on_and_lies_on_rev (a : P) (lieson : a LiesOnRay ray) (liesonrev : a LiesOnRay ray.reverse) : a = ray.source := by sorry



end EuclidGeom