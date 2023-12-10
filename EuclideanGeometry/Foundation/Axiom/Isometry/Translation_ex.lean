import EuclideanGeometry.Foundation.Axiom.Linear.Ray

/- The purpose of of this file is to establish results about parallel translate along a vector. Presumably, all results are "invariant" under parallel translation. -/

noncomputable section


namespace EuclidGeom

variable {P: Type _} [EuclideanPlane P] (v : Vec)

-- We fix the amount of translation to be v

-- parallel translate a generalized directed segments

def Seg.translate (l : Seg P) (v : Vec)  : Seg P where
  source := v +ᵥ l.source
  target := v +ᵥ l.target

-- parallel translate a nontrivial generalized directed segment is nontrivial

theorem non_triv_of_trans_seg_non_triv {l : Seg P}(nontriv : l.IsND) : (l.translate v).IsND := by sorry

def SegND.translate (seg_nd : SegND P) (v : Vec) : SegND P := ⟨seg_nd.1.translate v, non_triv_of_trans_seg_non_triv v seg_nd.2⟩

theorem reverse_of_trans_eq_trans_of_reverse_of_seg (l : Seg P) : (l.translate v).reverse = l.reverse.translate v := by sorry

-- parallel translation does not change the length of a generalized directed segement.

theorem length_eq_length_of_translate_of_seg (l : Seg P) : l.length = (l.translate v).length := by sorry


-- parallel translate a ray

def Ray.translate (l : Ray P) : Ray P where
  source := v +ᵥ l.source
  toDir := l.toDir


theorem reverse_of_trans_eq_trans_of_reverse_of_ray (l : Ray P) : (l.translate v).reverse = l.reverse.translate v := by sorry

theorem trans_of_seg_of_nontriv_toray (seg_nd : SegND P) : (seg_nd.toRay).translate v = (seg_nd.translate v).toRay := sorry

end EuclidGeom
