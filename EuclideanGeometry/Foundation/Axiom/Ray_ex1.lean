import EuclideanGeometry.Foundation.Axiom.Ray


namespace EuclidGeom

namespace GDSeg 
variable {P: Type _} [EuclideanPlane P] (gseg : GDSeg P) 

-- source and targets are on generalized directed segments
theorem source_lies_on_seg : gseg.source LiesOnGDSeg gseg := by sorry

theorem target_lies_on_seg : gseg.source LiesOnGDSeg gseg := by sorry

-- definition of reversion of the direction of a generalized directed segment
def reverse : GDSeg P where
  source := gseg.target
  target := gseg.source

-- reversion of generalized directed vector is compatible with make process




-- double reverse a generalized directed segment gets back to itself
theorem double_rev_eq_self  : gseg.reverse.reverse = gseg := rfl

-- reversing the direction does not change the property that a point lies on the generalized directed segments.
theorem IsOnGDSeg_of_rev_of_IsOnGDSeg (a : P) (lieson : a LiesOnGDSeg gseg) : a LiesOnGDSeg gseg.reverse := sorry

-- reversing the direction does not change the nontriviality of a generalized directed segment.
theorem nontriv_of_rev_of_nontriv (nontriv : gseg.target ≠ gseg.source) : gseg.reverse.target ≠ gseg.reverse.source := sorry

-- reversing the direction does not change the length
theorem length_eq_length_of_rev : gseg.length = gseg.reverse.length := sorry

end GDSeg



namespace DSeg

variable {P: Type _} [EuclideanPlane P] (seg : DSeg P)

-- source and targets are on generalized directed segments
theorem source_lies_on_seg : seg.source LiesOnDSeg seg := by sorry


theorem target_lies_on_seg : seg.target LiesOnDSeg seg := by sorry

-- definition of the reversion of the direction of a directed segment
def reverse : DSeg P where
  source := seg.target
  target := seg.source
  direction := -seg.direction
  on_ray := sorry
  non_triv := sorry

-- double reverse a directed segment gets back to itself
theorem double_rev_eq_self  : seg.reverse.reverse = seg := sorry

-- reversing the direction does not change the property that a point lies on the directed segments.
theorem IsOnDSeg_of_rev_of_IsOnDSeg (a : P) (lieson : a LiesOnDSeg seg) : a LiesOnDSeg seg.reverse := sorry


end DSeg



section compatibility_with_coersion


variable {P: Type _} [EuclideanPlane P] (gseg : GDSeg P) (seg : DSeg P)

-- the operation of reversing the direction commutes with coersion between directed segments and generalized directed segments.
theorem DSeg.rev_toGDSeg_eq_toGDSeg_rev : seg.reverse.toGDSeg = (seg.toGDSeg).reverse := sorry

theorem GDSeg.rev_toDSeg_eq_toDSeg_rev (nontriv : gseg.target ≠ gseg.source) : (gseg.reverse).toDSeg_of_nontriv (GDSeg.nontriv_of_rev_of_nontriv gseg nontriv) = (gseg.toDSeg_of_nontriv nontriv).reverse := sorry

-- reversing the direction of a generalized directed segment will negate the coersion to vectors
theorem GDSeg.neg_toVec_of_rev : gseg.reverse.toVec = - gseg.toVec := sorry


end compatibility_with_coersion




namespace Ray

variable {P: Type _} [EuclideanPlane P]  (ray : Ray P)


-- reverse the direction of a ray
def reverse : Ray P where
  source := ray.source
  direction := -ray.direction


theorem double_rev_eq_self : ray.reverse.reverse = ray := sorry

-- If a point lies on ray and its reversion, then it is the source

theorem eq_source_of_lies_on_and_lies_on_rev (a : P) (lieson : a LiesOnRay ray) (liesonrev : a LiesOnRay ray.reverse) : a = ray.source := by sorry

end Ray





end EuclidGeom