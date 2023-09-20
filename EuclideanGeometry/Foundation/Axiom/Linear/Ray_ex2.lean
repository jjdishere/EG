import EuclideanGeometry.Foundation.Axiom.Linear.Ray

noncomputable section
namespace EuclidGeom

variable {P: Type _} [EuclideanPlane P]

section MoreCoercionCompatibility

/- Given two segments $seg_1$ and $seg_2$, if the source and the target of the $seg_1$ both lie on $seg_2$, then every point of $seg_1$ lies on $seg_2$. -/
theorem every_pt_lies_on_seg_of_source_and_target_lies_on_seg {seg₁ seg₂ : Seg P} (h: seg₁.source LiesOn seg₂ ∧ seg₁.target LiesOn seg₂) {A : P} (ha: A LiesOn seg₁): (A LiesOn seg₂) := sorry


-- More theorem of this flavor, please formulate them on your own, following the instructions.  `But be careful that we introduced seg₁ and seg₂ using {}, this is because we want the compute to infer what they are; same applies to the point A.`

/- Given two segments $seg_1$ and $seg_2$, if the source and the target of $seg_1$ both lie in the interior of $seg_2$, and if $A$ is a point on $seg_1$, then $A$ lies in the interior of $seg_2$. -/
theorem
every_pt_lies_int_seg_of_source_and_target_lies_int_seg : sorry := sorry

/- Given two segments $seg_1$ and $seg_2$, if the source and the target of $seg_1$ both lie on $seg_2$, and if $A$ is a point in the interior of $seg_1$, then $A$ lies in the interior of $seg_2$. -/
theorem
every_int_pt_lies_int_seg_of_source_and_target_lies_on_seg : sorry := sorry

/- Given a segment and a ray, if the source and the target of the segment both lie on the ray, and if $A$ is a point on the segment, then $A$ lies on the ray. -/
theorem
every_pt_lies_on_ray_of_source_and_target_lies_on_ray : sorry := sorry

/- Given a segment and a ray, if the source and the target of the segment both lie in the interior of the ray, and if $A$ is a point on the segment, then $A$ lies in the interior of the ray.-/
theorem
every_pt_lies_int_ray_of_source_and_target_lies_int_ray : sorry := sorry

/- Given a segment and a ray, if the source and the target of the segment both lie on the ray, and if $A$ is a point in the interior of the segment, then $A$ lies in the interior of the ray. -/
theorem every_int_pt_lies_int_ray_of_source_and_target_lies_on_ray : sorry := sorry

/- Given two rays $ray_1$ and $ray_2$ with same direction, if the source of $ray_1$ lies on $ray_2$, and if $A$ is a point on $ray_1$, then $A$ lies on $ray_2$. -/
theorem
every_pt_lies_on_ray_of_source_lies_on_ray_and_same_dir : sorry := sorry

/- Given two rays $ray_1$ and $ray_2$ with same direction, if the source of $ray_1$ lies in the interior of $ray_2$, and if $A$ is a point on $ray_1$, then $A$ lies in the interior of $ray_2$. -/
theorem
every_pt_lies_int_ray_of_source_lies_int_ray_and_same_dir : sorry := sorry



end MoreCoercionCompatibility



end EuclidGeom