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

example (tr : Triangle P) (nontriv : tr.is_nontriv) (A B C D E F : P) (ha : A LiesOnIntRay (tr.edge₂.extension_ray nontriv.2)) (hb : B LiesOnIntRay (tr.edge₃.reverse.extension_ray (Ne.symm nontriv.3))) (hc : C LiesOnIntRay (tr.edge₁.extension_ray nontriv.1)) (hd : D LiesOnIntRay)

end EuclidGeom

