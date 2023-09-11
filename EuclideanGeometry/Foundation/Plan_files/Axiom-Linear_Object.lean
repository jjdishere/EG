/- Detailed content in the subfolder : Linear objects 

Ray.lean -- Define (directed) segments and rays

  Classes :
    class of Ray -- A ray consists of a pair of a point (source : P) and a direction (toDir : Dir).
    class of Seg -- A segment consists of a pair of points: (source : P) and (target : P). `Note that a segment is always directed` and `we allow the source and target points of a segment to be the same`.
    (defn) Seg.is_nd : Prop -- Given (seg : Seg P), seg.is_nd returns whether a (directed) segment (seg : Seg P) nondegenerate, i.e. seg.target ≠ seg.source. `Note that we will always use target ≠ source for consistency.`
    class of Seg_nd -- A nondegenerate segment, subtype of Seg, is a segment (seg : Seg P) with the property (nd : seg.is_nd)  or equivalently, (seg.source ≠ seg.target)  `which one should we use? Seg.is_nd or seg.source ≠ seg.target?`
  
  Coersion :
    Ray.toProj -- Given a (ray : Ray P), ray.toProj returns the Proj of a ray (defined from Ray.toDir)
    Ray.carrier -- Given a (ray : Ray P), ray.carrier is the set of points on a ray
    Ray.interior -- Given a (ray : Ray P), ray.interior is the set of points in the interior of a ray, namely {p : P | p ∈ ray.carrier ∧ p ≠ ray.source}.
    Seg.toVec -- Given a directed segment (seg : Seg P), seg.toVec is the vector associated to a seg, returning seg.target -ᵥ seg.source
    Seg.carrier -- Given a directed segment (seg : Seg P), seg.carrier is the set of points on a segment.
    Seg.interior -- Given a direceted segment (seg : Seg P), seg.interior is the set of points on its interial, i.e. {p : P | p ∈ seg.carrier ∧ p ≠ seg.source ∧ p ≠ seg.target}.
    Seg_nd.toRay -- Given a nondegenerate segment (seg_nd : Seg_nd P), seg_nd.toRay is the ray associated to seg, whose source is ray.source and whose toDir is the normalization of seg_nd.target -ᵥ seg_nd.source.
    Seg_nd.toDir -- Given a nondegenerate segment (seg_nd : Seg_nd P), seg_nd.toDir is the direction associated to seg, defined as seg_nd.toRay.toDir.
    Seg_nd.toProj -- Given a nondegenerate segment (seg_nd : Seg_nd P), seg_nd.toProj is the projective direction associated to seg, defined by seg_nd.toRay.toProj.
  
  Make :
    SEG = Seg.mk -- Rerwite the standard function of making a segment; i.e. for (A B : P), SEG A B gives the segment with source A and target B.
    SEG_nd = Seg_nd.mk -- Rewrite the standard function of making a nondegenerate segment; i.e. for (A B : P) and (nd : B ≠ A), SEG_nd A B nd gives the nondegenerate segment with source A and target B.
    Ray.mk_pt_pt -- Given two points (A B : P) and that they are not equal (nd : B ≠ A), Ray.mk_pt_pt A B nd returns the ray starting from A in the direction of B, i.e. (SEG_nd A B nd).toRay.
    RAY = Ray.mk_pt_pt -- Rewrite the making function of a ray from points (A B : P) and (nd : B ≠ A).

  (coersion compatibility)
    Ray.source_in_carrier -- Given a (ray : Ray P), the source ray.source ∈ ray.carrier.
    Seg.source_in_carrier -- Given a (seg : Seg P), the source seg.source ∈ seg.carrier.
    Seg.target_in_carrier -- Given a (seg : Seg P), the target seg.target ∈ seg.carrier.
    Ray.source_not_in_inter -- Given a (ray : Ray P), the source seg.source ∉ ray.interior.
    Seg.source_not_in_inter -- Given a (seg : Seg P), the source seg.source ∉ seg.interior.
    Seg.target_not_in_inter -- Given a (seg : Seg P), the source seg.target ∉ seg.interior.

    Seg.inter_in_carrier -- Given a (seg : Seg P), its interior is a subset of its carrier, i.e. seg.interior ⊂ seg.carrier.
    Ray.inter_in_carrer -- Given a (ray : Ray P), its interior is a subset of its carrier, i.e. ray.interior ⊂ ray.carrier.
    Seg_nd.carrier_in_toRay_carrier -- Given a nondegenerate segment (seg_nd : Seg_nd P), its carrier is a subset of the carrier of the associated ray, i.e. seg_nd.1.carrier ⊂ seg_nd.toRay.carrier.  `Here we did not define the carrier/interior of a nondegenerate segment, use the carrier/interior of the associated segment.`
    Seg_nd.inter_in_toRay_inter -- Given a nondegenerate segment (seg_nd : Seg_nd P), its interior is a subset of the interior of the associated ray, i.e. seg_nd.interior ⊂ seg_nd.toRay.interior.

    nd_of_seg_nd_tovec : Given a nondegenerate segment (seg : Seg_nd P), the associated vector is also nondegenerate, i.e. seg_nd_tovec.is_nd
    seg_nd_todir_eq_seg_nd_tovec_toproj : Given a nondegenerate segment (seg_nd : Seg_nd P), we have seg_nd.toDir = (seg_nd.toVec nd_of_seg_nd_tovec).toProj
    seg_nd_toproj_eq_seg_nd_toVec_toproj : Given a nondegenerate segment (seg_nd : Seg_nd P), we have seg_nd.toProj = (seg_nd.toVec nd_of_seg_nd_toVec).toDir

    Ray.is_in_inter_iff_add_pos_Dir -- Given a (ray : Ray P), a point (p : P) lies in the interior of ray iff ∃ t : ℝ, 0 < t ∧ p = t ⬝ ray.toDir +ᵥ ray.source.

  (reverse)
    (defn) Ray.reverse : Ray P -- Given a (ray : Ray P), ray.reverse is a ray obtained by reversing the direction of ray, i.e. its source is ray.source, and its toDir is - ray.toDir.
    (defn) Seg.reverse :  -- Given a (seg : Seg P), seg.reverse is a segment whose source is seg.target and whose target is seg.source.
    (defn) Seg.reverse -- Given a (seg : Seg P), seg.reverse is a segment whose source is seg.target and whose target is seg.source.
    Ray.rev_rev_eq_self -- Given a (ray : Ray P), reversing it twice gives back to itself, i.e. ray.rev.rev = ray.
    Seg.rev_rev_eq_self -- Given a (seg : Seg P), reversing it twice gives back to itself, i.e. seg.rev.rev = seg.
    Seg_nd.rev_rev_eq_self -- Given a (seg_nd : Seg_nd P), reversing it twice gives back to itself, i.e. seg_nd.rev.rev = seg_nd.

  (extension line)
    (defn) Seg_nd.extension : Ray P -- extend a directed segment AB to the ray starting at B, in the direction of VEC A B
    seg_extn_eq_rev_toray_rev -- extending a segment is the same as first reverse the segment, and to ray, and reverse the direction of ray
    Seg.target_in_inter_seg_source_pt_of_pt_in_extn_inter -- Given a directed segment AB, for any point P in the interior extension line of AB, then B lies in the interior of AP

  (length)
    (defn) Seg.length : ℝ -- length of a segment (for Seg_nd, use Seg_nd.1.length)
    seg_length_is_nonneg -- length of a segment is nonnegative
    tovec_ne_zero_iff_seg_nd -- a segment has nonzero tovec iff it is non-degenerate
    length_ne_zero_iff_seg_nd -- a segment has nonzero length iff it is nondegenerate
    length_pos_iff_seg_nd -- a segment has positive length iff it is nondegenerate
    length_eq_length_add_length -- length of segment is the sum of its two parts
    length_rev_seg_eq_length_seg -- the length of the reversed segment is the length of the segment

  (midpoint)
    (defn) Seg.midpiont : P -- return the midpoint of a segment (by (l.target -ᵥ l.source) /2 +ᵥ l.source)
    midpt_in_carrier -- midpoint of a segment lies in its carrier
    midpt_in_interior_of_seg_nd -- if a segment is nondegenerate, the midpoint lies in its interior
    midpt_iff_same_tovec_source_and_target -- a point is the midpoint of a segment iff (SEG l.source p).toVec = (SEG p l.target).toVec
    
    length_pos_iff_exist_inter_pt -- length of a segment is positive iff there exists an interior point (the necessity condition uses the additivity of length function, and the existence is given by the midpoint)

    dist_target_eq_dist_source_of_midpt -- the midpoint of a segment has equal distance to the source and the target
    is_midpoint_iff_in_seg_and_dist_target_eq_dist_source -- a point is the midpoint of a segment if and only if it lies on the segment and it has same distance to the source and target


  (Archimedean property)
    Ray.exist_pt_in_interior -- for any ray, there exists a point in its interior
    
-/