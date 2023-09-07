import EuclideanGeometry.Foundation.Index

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]


/- Exercise 8.1.11 : Let tr be a nontrivial triangle. 
Let A be a point in the extension line of tr.point₃ tr.point₁ (i.e. tr.edge₂).
Let B be a point in the extension line of tr.point₂ tr.point₁ (i.e. reverse of tr.edge₃).
Let C be a point in the extension line of tr.point₂ tr.point₃ (i.e. tr.edge₁).
Let D be a point in the extension line of tr.point₁ tr.point₃ (i.e. reverse of tr.edge₂).
Let E be a point in the extension line of tr.point₁ tr.point₂ (i.e. tr.edge₃).
Let F be a point in the extension line of tr.point₃ tr.point₂ (i.e. reverse of tr.edge₁).
Then ∠ tr.point₁ A B + ∠ A B tr.point₂ + ∠ tr.point₃ C D + ∠ C D tr.point₃ + ∠ tr.point₂ E F + ∠ E F tr.point₂ = 2 * π.
-/ 

example (tr : Triangle P) (nontriv : tr.is_nontriv) (A B C D E F : P) 
(let line1 := tr.edge₂.extension_ray_of_nontriv nontriv.2)
(ha : A LiesOnIntRay line1) 
(hb : B LiesOnIntRay (tr.edge₃.reverse.extension_ray_of_nontriv (Ne.symm nontriv.3))) 
(hc : C LiesOnIntRay (tr.edge₁.extension_ray_of_nontriv nontriv.1)) 
(hd : D LiesOnIntRay (tr.edge₂.reverse.extension_ray_of_nontriv (Ne.symm nontriv.2)))
(he : E LiesOnIntRay (tr.edge₃.extension_ray_of_nontriv nontriv.3)) 
(hf : F LiesOnIntRay (tr.edge₁.reverse.extension_ray_of_nontriv (Ne.symm nontriv.1)))
: ANG tr.point₁ A B ha.2 (pts_are_distinct_of_two_rays_of_oangle )+ ANG A B tr.point₂ + ANG tr.point₃ C D + ANG C D tr.point₃ + ANG tr.point₂ E F + ANG E F tr.point₂ = 2 * π := by sorry

end EuclidGeom

