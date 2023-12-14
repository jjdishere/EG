/- Detailed content in the subfolder : Linear -/

/-!
Ray.lean -- Define (directed) segments and rays

  Classes :
    class of Ray -- A ray consists of a pair of a point (source : P) and a direction (toDir : Dir).
    class of Seg -- A segment consists of a pair of points: (source : P) and (target : P). `Note that a segment is always directed` and `we allow the source and target points of a segment to be the same`.
    (defn) Seg.IsND : Prop -- Given (seg : Seg P), seg.IsND returns whether a (directed) segment (seg : Seg P) nondegenerate, i.e. seg.target ≠ seg.source. `Note that we will always use target ≠ source for consistency.`
    class of SegND -- A segment of positive length, subtype of Seg, {seg : Seg P // seg.IsND}

  Make :
    SEG = Seg.mk -- Rerwite the standard function of making a segment; i.e. for (A B : P), SEG A B gives the segment with source A and target B.
    SEG_nd = SegND.mk -- Rewrite the standard function of making a nondegenerate segment; i.e. for (A B : P) and (nd : B ≠ A), SEG_nd A B nd gives the nondegenerate segment with source A and target B.
    Ray.mk_pt_pt -- Given two points (A B : P) and that they are not equal (nd : B ≠ A), Ray.mk_pt_pt A B nd returns the ray starting from A in the direction of B, i.e. (SEG_nd A B nd).toRay.
    RAY = Ray.mk_pt_pt -- Rewrite the making function of a ray from points (A B : P) and (nd : B ≠ A).
  
  Coersion :
    Ray.toProj -- Given a (ray : Ray P), ray.toProj returns the Proj of a ray (defined from Ray.toDir)
    Ray.IsOn -- Given (a : P) (ray : Ray P), IsOn a ray is the property that point lies on a ray, namely, ∃ (t : ℝ), 0 ≤ t ∧ VEC ray.source a = t • ray.toDir.toVec.
    Ray.IsInt -- Given (a : P) (ray : Ray P), IsInt a ray is the property that point a lies in the interior of a ray, namely Ray.IsOn a ray ∧ a ≠ ray.source.
    Ray.carrier -- Given a (ray : Ray P), ray.carrier is the set of points on a ray.
    Ray.interior -- Given a (ray : Ray P), ray.interior is the set of points in the interior of a ray.
    Seg.toVec -- Given a directed segment (seg : Seg P), seg.toVec is the vector associated to a seg, returning seg.target -ᵥ seg.source
    Seg.IsOn -- Given (a : P) (seg : Seg P), IsOn a seg is the property that point lies on a segment.
    Seg.IsInt -- Given (a : P) (seg : Seg P), IsInt a seg is the property that point a lies in the interior of a segment, namely Seg.IsOn a seg ∧ a ≠ seg.source ∧ a ≠ seg.target.
    Seg.carrier -- Given a (seg : Seg P), seg.carrier is the set of points on a segment.
    Seg.interior -- Given a (seg : Seg P), seg.interior is the set of points in the interior of a segment.
    SegND.toVecND -- Given a nondegenerate segment (segnd : SegND P), segnd.toVEC_nd is the vector associated to SegND.
    SegND.toDir -- Given a nondegenerate segment (segnd : SegND P), segnd.toDir is the direction associated to seg, defined by segnd.toVecND.toDir.
    SegND.toRay -- Given a nondegenerate segment (segnd : SegND P), segnd.toRay is the ray associated to seg, whose source is segnd.source and whose toDir is seg_nd.toDir.
    SegND.toProj -- Given a nondegenerate segment (segnd : SegND P), seg_nd.toProj is the projective direction associated to seg, defined by seg_nd.toVecND.toProj.
    `The following definitions is written as comments in the file, they are not used currently`
      SegND.IsOn -- Given (a : P) (seg_nd : SegND P), IsOn a seg is the property that point lies on a nondegenerate segment.
      SegND.IsInt -- Given (a : P) (seg_nd : SegND P), IsInt a ray is the property that point a lies in the interior of a nondegenerate segment.
      SegND.carrier -- Given a (seg_nd : SegND P), seg_nd.carrier is the set of points on a seg_nd.
      SegND.interior -- Given a (seg_nd : SegND P), seg_nd.interior is the set of points in the interior of a seg_nd.


  (coercion compatibility)`in Ray_ex.lean, need to rewrite comment`
    Ray.source_lies_on -- Given a (ray : Ray P), the source ray.source ∈ ray.carrier.
    Seg.source_lies_on -- Given a (seg : Seg P), the source seg.source ∈ seg.carrier.
    Seg.target_lies_on -- Given a (seg : Seg P), the target seg.target ∈ seg.carrier.
    Ray.source_not_lies_int -- Given a (ray : Ray P), the source seg.source ∉ ray.interior.
    Seg.source_not_lies_int -- Given a (seg : Seg P), the source seg.source ∉ seg.interior.
    Seg.target_not_lies_int -- Given a (seg : Seg P), the source seg.target ∉ seg.interior.

    Seg.lies_on_of_lies_int -- Given a (seg : Seg P), its interior is a subset of its carrier, i.e. seg.interior ⊂ seg.carrier.
    Ray.lies_on_of_lies_int -- Given a (ray : Ray P), its interior is a subset of its carrier, i.e. ray.interior ⊂ ray.carrier.
    SegND.lies_on_toRay_of_lies_on -- Given a nondegenerate segment (seg_nd : SegND P), its carrier is a subset of the carrier of the associated ray, i.e. seg_nd.1.carrier ⊂ seg_nd.toRay.carrier.
    SegND.lies_int_toray_of_lies_int -- Given a nondegenerate segment (seg_nd : SegND P), its interior is a subset of the interior of the associated ray, i.e. seg_nd.interior ⊂ seg_nd.toRay.interior.

    `More to add here, or other place. e.g. the source and target of a seg LiesOn a ray → every other point lies on it `

    SegND.toDir_eq_toray_toDir : Given a nondegenerate segment (seg_nd : SegND P), we have seg_nd.toDir = seg_nd.toRay.toDir
    SegND.toProj_eq_toray_toProj : Given a nondegenerate segment (seg_nd : SegND P), we have seg_nd.toProj = seg_nd.toRay.toProj

    Ray.is_in_inter_iff_add_pos_Dir -- Given a (ray : Ray P), a point (p : P) lies in the interior of ray iff  ∃ t : ℝ, 0 < t ∧ VEC ray.source p = t • ray.toDir.toVec .

    `More to add here, related to points and mk method e.g. relation A B (SEG A B).toVec = VEC A B`

  (reverse)
    (defn) Ray.reverse : Ray P -- Given a (ray : Ray P), ray.reverse is a ray obtained by reversing the direction of ray, i.e. its source is ray.source, and its toDir is - ray.toDir.
    (defn) Seg.reverse : Seg P -- Given a (seg : Seg P), seg.reverse is a segment whose source is seg.target and whose target is seg.source.
    (defn) SegND.reverse : SegND P -- Given a (seg_nd : SegND P), seg_nd.reverse is a segment whose source is seg_nd.target and whose target is seg_nd.source.
    SegND.rev_toseg_eq_toseg_rev -- Given a (seg_nd : SegND P), seg_nd.reverse.1 = seg_nd.1.reverse.
    Ray.rev_rev_eq_self -- Given a (ray : Ray P), reversing it twice gives back to itself, i.e. ray.rev.rev = ray.
    Seg.rev_rev_eq_self -- Given a (seg : Seg P), reversing it twice gives back to itself, i.e. seg.rev.rev = seg.
    SegND.rev_rev_eq_self -- Given a (seg_nd : SegND P), reversing it twice gives back to itself, i.e. seg_nd.rev.rev = seg_nd.
    Seg.lies_on_rev_iff_lie_son -- Given a (p : P) (seg : Seg P), p lies on seg if and only if p lies on seg.reverse.
    eq_source_iff_lies_on_ray_lies_on_ray_rev -- Given a (ray : Ray P), the intersection of the carrier of ray and the carrier of the reverse of ray is exactly the source of ray, i.e. (A : P) : A = ray.source ↔ A ∈ ray.carrier ∧ A ∈ ray.reverse.carrier
    not_lies_on_of_lies_int_rev -- Given a (ray : Ray P), the intersection of the carrier of ray and the interior of the reverse of ray is empty.
    not_lies_int_of_lies_on_rev -- Given a (ray : Ray P), the intersection of the interior of ray and the carrier of the reverse of ray is empty.
    lies_on_iff_lies_on_toray_and_rev_toray -- Given a nondegenerate segment (segnd : SegND P), a point (A : P) lies on segnd if and only if A lies on the ray associated to the segment as well as the ray associated to the reverse of the segment, i.e. A ∈ segnd.toray ∧ A ∈ segnd.reverse.toray.
    Ray.toDir_of_reverse_eq_neg_toDir --
    Ray.toProj_of_reverse_eq_toProj --
    Seg.toVec_of_reverse_eq_neg_toVec -- Given a (seg : Seg P), seg.reverse.toVec = - seg.toVec
    SegND.toVecND_of_reverse_eq_neg_toVecND -- Given a (seg_nd : SegND P), seg_nd.reverse.toVecND = - seg_nd.toVecND
    SegND.toDir_of_reverse_eq_neg_toDir -- Given a (seg_nd : SegND P), seg_nd.reverse.toDir = - seg_nd.toDir
    SegND.toProj_of_reverse_eq_neg_toProj -- Given a (seg_nd : SegND P), seg_nd.reverse.toProj = seg_nd.toProj

  (extension)
    (defn) SegND.extension : Ray P -- Given a (segnd : SegND P), extend the directed segment AB to the ray starting at B, in the direction of VEC A B, defined as the ray with starting point segnd.2.target, and direction segnd.toDir.
    extn_eq_rev_toRay_rev -- Given a (segnd : SegND P), extending a segment is the same as first reverse the segment, and to ray, and then reverse the direction of ray, i.e. segnd.extension = segnd.reverse.toRay.reverse.
    eq_target_of_lies_on_lies_on_extn -- Given a (segnd : SegND P), the only point that lies on both segnd and segnd.extension is segnd.1.target, i.e. (A : P) : (A ∈ segnd.carrier) ∧ (A ∈ segnd.extension) ↔ A = segnd.target.
    target_lies_int_seg_source_pt_of_pt_lies_int_extn -- Given a nondegenerate segment (segnd : SegND P), for any point (A : P) in the interior of extension line of segnd, i.e. A ∈ segnd.extension.interior, segnd.target lies in the segment SEG segnd.source A.

  (length)
    (defn) Seg.length : ℝ -- The length of a segment (seg : Seg P).  (for segnd : SegND P, use segnd.1.length)
    seg_length_nonneg -- The length of a segment (seg : Seg P) is nonnegative
    length_pos_iff_seg_nd -- A segment (seg : Seg P) has positive length iff it is nondegenerate, i.e. seg.length > 0 ↔ seg.IsND.
    length_ne_zero_iff_nd -- A segment (seg : Seg P) has nonzero length iff it is nondegenerate, i.e. seg.length ≠ 0 ↔ seg.IsND.
    length_eq_length_add_length -- The length of segment is the sum of its two parts, i.e. given a segment (seg : Seg P) and a point (A : P) on seg, then seg.length = (SEG seg.source A).length + (SEG A seg.target).length.
    length_rev_seg_eq_length_seg -- `@simp` `Maybe not at simp` `currently in Ray_ex` Given a segment (seg : Seg P), the length of the reversed segment is equal to the length of the segment, i.e. seg.reverse.length = seg.length

  (midpoint)
    (defn) Seg.midpiont : P -- For a segment (seg : Seg P), return the midpoint of a segment (by (seg.target -ᵥ seg.source) /2 +ᵥ seg.source)
    Seg.midpt_lies_on -- midpoint of a segment lies in its carrier
    SegND.midpt_lies_int -- if a segment is nondegenerate, the midpoint lies in its interior
    midpt_iff_same_toVec_source_and_target -- a point is the midpoint of a segment iff (SEG l.source p).toVec = (SEG p l.target).toVec
    

    dist_target_eq_dist_source_of_midpt -- the midpoint of a segment has equal distance to the source and the target
    is_midpoint_iff_in_seg_and_dist_target_eq_dist_source -- a point is the midpoint of a segment if and only if it lies on the segment and it has same distance to the source and target


  (Archimedean property)`existence`
    SegND.exist_pt_beyond_pt --
    Ray.exist_pt_in_interior -- for any ray, there exists a point in its interior
    length_pos_iff_exist_inter_pt -- length of a segment is positive iff there exists an interior point (the necessity condition uses the additivity of length function, and the existence is given by the midpoint)

-/

/-!
Colinarity.lean -- Define the relative positions of points on rays

  Definitions :
    (defn) colinear_of_nd : Prop -- Given three distinct points (A B C : P), return whether the three points are colinear, i.e. whether (VEC A B).toProj = (VEC A C).toProj
    (defn) colinear : Prop -- Given three points (A B C : P), return whether they are colinear; if at least two of them are equal, then they are considered automatically colinear.
  
  Theorems :
    colinear_of_vec_eq_smul_vec -- Given three points (A B C : P), if VEC A C = t ⬝ VEC A B for some t ∈ ℝ, then A B C are colinear
    colinear_of_vec_eq_smul_vec' -- same as colinear_of_vec_eq_smul_vec, excepted stated in the form of existence of t
    colinear_iff_eq_smul_vec_of_ne -- Given three points (A B C : P) with (B ≠ A), then A B C are colinear if and only if VEC A C = r ⬝ VEC A B for some r ∈ ℝ
    


-/

/-!
Line.lean -- Define lines

  Setoid : 
    same_extn_line -- the equivalent relation of admitting the same underlying line on rays

  Classes : 
    class of Line -- define Line as the quotient of Ray with respect to relation same_extn_line

  Make :
    LIN = Line.mk_pt_pt -- 
    Line.mk_pt_proj --
    Line.mk_pt_dir --
    Line.mk_pt_vec_nd --

  Coersion:

    Line.toProj --
    Ray.toLine  --
    SegND.toLine --
    Carrier:
      Line.carrier --
      Line.IsOn -- `Don't really need this`
      linear -- every 3 pts on line colinear;
      maximal -- pt that colinear with 2 different pts on line falls on the line
      nontriv -- a line contains at least 2 pts
      Ray.lies_on_toLine_iff_lies_on_or_lies_on_rev --
      Ray.lies_on_toLine_iff_lies_int_or_lies_int_rev_or_eq_source

  (compatibility) `Line_ex`
    pt_pt : theorems directly related to Line.mk_pt_pt
      line_of_pt_pt_eq_rev --
      fst_pt_lies_on_line_of_pt_pt --
      snd_pt_lies_on_line_of_pt_pt --
      eq_line_of_pt_pt_of_ne --
      eq_of_pt_pt_lies_on_of_ne -- 2 ne pts lies on 2 lines implies 2 lines are the same
    coercion : theorems related to coercions 
      SegND.toLine_eq_toray_toLine --
      line_of_pt_pt_eq_ray_toLine --
      line_of_pt_pt_eq_seg_nd_toLine --
      Ray.source_lies_on_toLine --
      SegND.source_lies_on_toLine --
      SegND.target_lies_on_toLine --
      Ray.toLine_eq_rev_toLine --
      SegND.toLine_eq_rev_toLine --
      toLine_eq_extn_toLine --
      lies_on_extn_or_rev_extn_iff_lies_on_toLine_of_not_lies_on --
      lies_on_iff_lies_on_iff_line_eq_line --
      Ray.lies_on_toLine_of_lie_on --
      SegND.lies_on_toLine_of_lie_on --
      line_toProj_eq_seg_nd_toProj_of_lies_on --
      Ray.toProj_eq_toLine_toProj --
      SegND.toProj_eq_toLine_toProj --
      lies_on_iff_eq_toProj_of_lies_on --
    colinear : theorems related to colinear
      lies_on_line_of_pt_pt_iff_colinear --
      lies_on_iff_colinear_of_ne_lies_on_lies_on --
      colinear_iff_exist_line_lies_on --

    (archemidean) `Line_ex`
    exists_ne_pt_pt_lies_on_of_line --
    lies_on_of_SegND_toProj_eq_toProj --
    lies_on_iff_eq_toProj_of_lies_on --
    Line.exist_pt_beyond_pt --
  
-/