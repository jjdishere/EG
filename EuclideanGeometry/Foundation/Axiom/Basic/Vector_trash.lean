import EuclideanGeometry.Foundation.Axiom.Basic.Vector

namespace EuclidGeom

theorem det_eq_zero_of_toProj_eq (u v : Vec_nd) (toprojeq : Vec_nd.toProj u = v.toProj) : det u v = 0 := sorry

theorem dir_toVec_nd_toProj_eq_dir_toProj (u : Dir) : u.toVec_nd.toProj = u.toProj := sorry

end EuclidGeom
