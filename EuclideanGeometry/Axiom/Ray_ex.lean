import EuclideanGeometry.Axiom.Ray


namespace EuclidGeom

-- reversing directions of a (generalized) directed segment

variable {P: Type _} [EuclideanPlane P] (gseg : GDirSeg P)
def GDirSeg.reverse  : GDirSeg P where
  source := gseg.target
  target := gseg.source

theorem GDirSeg.double_rev_eq_self  : gseg.reverse.reverse = gseg := rfl

variable (seg : DirSeg P)
def DirSeg.reverse : DirSeg P where
  source := seg.target
  target := seg.source
  direction := -seg.direction
  on_ray := sorry
  non_triv := sorry

theorem DirSeg.double_rev_eq_self  : seg.reverse.reverse = seg := sorry

theorem DirSeg.rev_toGDirSeg_eq_toGDirSeg_rev : seg.reverse.toGDirSeg = (seg.toGDirSeg).reverse := sorry

-- reversing direction of a ray

variable (ray : Ray P)
def Ray.reverse : Ray P where
  source := ray.source
  direction := -ray.direction

theorem Ray.double_rev_eq_self : ray.reverse.reverse = ray := sorry

-- move a ray/GDirSeg


end EuclidGeom