import EuclideanGeometry.Foundation.Index

noncomputable section

-- All exercises are from Shan Zun's book Exercise 1

namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

namespace Shan_Problem_1_1
/- In $\triangle ABC$, let $AD$ be the height and $AE$ be the angle bisector of $\triangle ABC$.
Prove that $\angle DAE = (\angle CBA - \angle ACB) / 2$. -/


-- Let $\triangle ABC$ be an nondegenerate triangle.
variable {A B C : P} {hnd : ¬ colinear A B C}


end Shan_Problem_1_1

namespace Shan_Problem_1_2
/- Let $\triangle ABC$ be a nondegenerate isosceles triangle in which $AB = AC$. Let $D$ be a point on the extension of $AB$ and $E$ a point on the extension of $AC$, such that $\angle EBC = \angle BCD$.

Prove that $\angle CDA = \angle BEA$. -/


end Shan_Problem_1_2