import EuclideanGeometry.Foundation.Index

noncomputable section


namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]


/- Exercise 8.1.11 : Let tr be a nontrivial triangle. 
Let A be a point in the extension line of tr.point₃ tr.point₁ (i.e. tr.edge₂).
Let B be a point in the extension line of tr.point₂ tr.point₁ (i.e. reverse of tr.edge₃).
Let C be a point in the extension line of tr.point₂ tr.point₃ (i.e. tr.edge₁).
Let D be a point in the extension line of tr.point₁ tr.point₃ (i.e. reverse of tr.edge₂).
Let E be a point in the extension line of tr.point₁ tr.point₂ (i.e. tr.edge₃).
Let F be a point in the extension line of tr.point₃ tr.point₂ (i.e. reverse of tr.edge₁).
Then ANG tr.point₁ A B + ANG A B tr.point₂ + ANG tr.point₃ C D + ANG C D tr.point₃ + ANG tr.point₂ E F + ANG E F tr.point₂ = 2 * π.
-/ 

example (tri : Triangle P) (nontriv : tri.is_nontriv) :
let line1 := tri.edge₂.extension_ray_of_nontriv (tri.nontriv₂ nontriv)
let line2 := tri.edge₃.reverse.extension_ray_of_nontriv (Ne.symm (tri.nontriv₃ nontriv))
let line3 := tri.edge₁.extension_ray_of_nontriv (tri.nontriv₁ nontriv)
let line4 := tri.edge₂.reverse.extension_ray_of_nontriv (Ne.symm (tri.nontriv₂ nontriv))
let line5 := tri.edge₃.extension_ray_of_nontriv (tri.nontriv₃ nontriv)
let line6 := tri.edge₁.reverse.extension_ray_of_nontriv (Ne.symm (tri.nontriv₁ nontriv))
∀ (A B C D E F : P) [ha : A LiesInt line1] [hb : B LiesInt line2] [hc : C LiesInt line3] [hd : D LiesInt line4] [he : E LiesInt line5] [hf : F LiesInt line6], ∠ tr.point₁ A B ha.2 (pts_are_distinct_of_two_rays_of_angle )+ ∠ A B tr.point₂ + ∠ tr.point₃ C D + ∠ C D tr.point₃ + ∠ tr.point₂ E F + ∠ E F tr.point₂ = 2 * π := by sorry

end EuclidGeom

