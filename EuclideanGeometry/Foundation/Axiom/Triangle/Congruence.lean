import EuclideanGeometry.Foundation.Axiom.Triangle.Basic

namespace EuclidGeom
/- definition of congruence of triangles-/

/- congruences of triangles, separate definitions for reversing orientation or not, (requiring all sides and angles being the same)-/

variable {P : Type _} [EuclideanPlane P]

def IsCongr (tr₁ tr₂: Triangle P) : Prop := by
  by_cases tr₁.is_nd ∧ tr₂.is_nd
  · let tr_nd₁ : Triangle_nd P := ⟨tr₁, h.1⟩
    let tr_nd₂ : Triangle_nd P := ⟨tr₂, h.2⟩
    exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length ∧ tr_nd₁.angle₁ = tr_nd₂.angle₁ ∧ tr_nd₁.angle₂ = tr_nd₂.angle₂ ∧ tr_nd₁.angle₃ = tr_nd₂.angle₃
  · exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length

scoped infix : 50 "IsCongrTo" => IsCongr

scoped infix : 50 "≃" => IsCongr --do we need?

namespace IsCongr

section triangle

variable (tr₁ tr₂: Triangle P) (h : tr₁ IsCongrTo tr₂)

theorem is_nd: tr₁.is_nd = tr₂.is_nd := by
  rw [IsCongr] at h
  by_cases nd : (tr₁.is_nd ∧ tr₂.is_nd)
  · rcases nd with ⟨nd₁,nd₂⟩
    have i₁ := eq_true nd₁
    have i₂ :=eq_true nd₂
    rw[i₁,i₂]
  · simp only [nd, dite_false] at h 
    rcases h with ⟨s₁,s₂,s₃⟩
    have d₁₂: (¬ tr₁.is_nd) → (¬ tr₂.is_nd) := by 
     intro i
     unfold Triangle.is_nd at i
     push_neg at i
     unfold Triangle.is_nd 
     push_neg 
     unfold colinear at i
     by_cases m : (tr₁.point₃ = tr₁.point₂ ∨ tr₁.point₁ = tr₁.point₃ ∨ tr₁.point₂ = tr₁.point₁)
     · rcases m with (m₁|(m₂|m₃))
       · unfold Seg.length Seg.toVec Seg.source Seg.target at s₁--情况1
         have i₁ : (Triangle.edge₁ tr₁).1=tr₁.2 := by unfold Seg.source;rfl
         have i₂ : (Triangle.edge₁ tr₁).2=tr₁.3 := by unfold Seg.target;rfl
         rw[← i₁,← i₂] at m₁
         have i₄ : VEC (Triangle.edge₁ tr₁).1 (Triangle.edge₁ tr₁).2=0 := by rw[m₁];apply vec_same_eq_zero
         have i₅ : ‖VEC (Triangle.edge₁ tr₁).1 (Triangle.edge₁ tr₁).2‖=0 := by rw[i₄];norm_num
         have i₆ : ‖VEC (Triangle.edge₁ tr₂).1 (Triangle.edge₁ tr₂).2‖=0 := by unfold Seg.source Seg.target;rw[← s₁];exact i₅
         have i₇ : (Triangle.edge₁ tr₂).1=(Triangle.edge₁ tr₂).2 := by unfold Vec.mk_pt_pt at i₆;norm_num at i₆;simp only[i₆]
         by_contra h₀
         unfold colinear at h₀
         have j₂:(Triangle.edge₁ tr₂).1=Triangle.point₂ := by unfold Seg.source Triangle.edge₁;dsimp
         have j₃:(Triangle.edge₁ tr₂).2=Triangle.point₃ := by unfold Seg.target Triangle.edge₁;dsimp
         rw[j₂,j₃] at i₇
         have delta: tr₂.point₃ = tr₂.point₂ ∨ tr₂.point₁ = tr₂.point₃ ∨ tr₂.point₂ = tr₂.point₁ := by apply Or.inl;rw[i₇]
         apply false_of_true_eq_false
         simp[delta] at h₀
       · unfold Seg.length Seg.toVec Seg.source Seg.target at s₂--情况2
         have i₁ : (Triangle.edge₂ tr₁).1=tr₁.3 := by unfold Seg.source;rfl
         have i₂ : (Triangle.edge₂ tr₁).2=tr₁.1 := by unfold Seg.target;rfl
         rw[← i₁,← i₂] at m₂
         have i₄ : VEC (Triangle.edge₂ tr₁).1 (Triangle.edge₂ tr₁).2=0  := by rw[m₂];apply vec_same_eq_zero
         have i₅ : ‖VEC (Triangle.edge₂ tr₁).1 (Triangle.edge₂ tr₁).2‖=0 := by rw[i₄];norm_num
         have i₆ : ‖VEC (Triangle.edge₂ tr₂).1 (Triangle.edge₂ tr₂).2‖=0 := by unfold Seg.source Seg.target;rw[← s₂];exact i₅
         have i₇ : (Triangle.edge₂ tr₂).1=(Triangle.edge₂ tr₂).2 := by unfold Vec.mk_pt_pt at i₆;norm_num at i₆;simp only[i₆]
         by_contra h₀
         unfold colinear at h₀
         have j₂:(Triangle.edge₂ tr₂).1=Triangle.point₃ := by unfold Seg.source Triangle.edge₂;dsimp
         have j₃:(Triangle.edge₂ tr₂).2=Triangle.point₁ := by unfold Seg.target Triangle.edge₂;dsimp
         rw[j₂,j₃] at i₇
         have delta: tr₂.point₃ = tr₂.point₂ ∨ tr₂.point₁ = tr₂.point₃ ∨ tr₂.point₂ = tr₂.point₁ := by apply Or.inr;apply Or.inl;rw[i₇]
         apply false_of_true_eq_false
         simp[delta] at h₀
       · unfold Seg.length Seg.toVec Seg.source Seg.target at s₃--情况3
         have i₁ : (Triangle.edge₃ tr₁).1=tr₁.1 := by unfold Seg.source;rfl
         have i₂ : (Triangle.edge₃ tr₁).2=tr₁.2 := by unfold Seg.target;rfl
         rw[← i₁,← i₂] at m₃
         have i₄ : VEC (Triangle.edge₃ tr₁).1 (Triangle.edge₃ tr₁).2=0 := by rw[m₃];apply vec_same_eq_zero
         have i₅ : ‖VEC (Triangle.edge₃ tr₁).1 (Triangle.edge₃ tr₁).2‖=0 := by rw[i₄];norm_num
         have i₆ : ‖VEC (Triangle.edge₃ tr₂).1 (Triangle.edge₃ tr₂).2‖=0 := by unfold Seg.source Seg.target;rw[← s₃];exact i₅
         have i₇ : (Triangle.edge₃ tr₂).1=(Triangle.edge₃ tr₂).2 := by unfold Vec.mk_pt_pt at i₆;norm_num at i₆;simp only[i₆]
         by_contra h₀
         unfold colinear at h₀
         have j₂:(Triangle.edge₃ tr₂).1=Triangle.point₁ := by unfold Seg.source Triangle.edge₃;dsimp
         have j₃:(Triangle.edge₃ tr₂).2=Triangle.point₂ := by unfold Seg.target Triangle.edge₃;dsimp
         rw[j₂,j₃] at i₇
         have delta: tr₂.point₃ = tr₂.point₂ ∨ tr₂.point₁ = tr₂.point₃ ∨ tr₂.point₂ = tr₂.point₁ := by apply Or.inr;apply Or.inr;rw[i₇]
         apply false_of_true_eq_false
         simp[delta] at h₀
     · simp[m] at i
       unfold colinear_of_nd at i 
       push_neg at m
       rcases m with ⟨ne₂₃,ne₁₃,ne₁₂⟩
       have ne₃₁ := ne_comm.mp ne₁₃
       have cons_mul := smul_of_eq_toProj ⟨VEC tr₁.point₁ tr₁.point₂, (ne_iff_vec_ne_zero tr₁.point₁ tr₁.point₂).1 ne₁₂⟩ ⟨VEC tr₁.point₁ tr₁.point₃, (ne_iff_vec_ne_zero tr₁.point₁ tr₁.point₃).1 ne₃₁⟩ i
       simp at cons_mul
       rcases cons_mul with ⟨t,eq⟩
       have eq' : VEC tr₁.point₂ tr₁.point₃ = (1 - t) • VEC tr₁.point₂ tr₁.point₁ := by
        rw [← vec_sub_vec tr₁.point₁ tr₁.point₂ tr₁.point₃, eq , ← neg_vec tr₁.point₁ tr₁.point₂,smul_neg, sub_smul, neg_sub, one_smul]
        rfl
       have leq : ‖(VEC tr₁.point₁ tr₁.point₃)‖ = ‖t‖* ‖(VEC tr₁.point₁ tr₁.point₂)‖ := by 
        rw[eq]
        rw[<-norm_smul t (VEC tr₁.point₁ tr₁.point₂)]
        simp
       have leq' : ‖(VEC tr₁.point₂ tr₁.point₃)‖ = ‖1-t‖* ‖(VEC tr₁.point₁ tr₁.point₂)‖ := by sorry
       unfold Seg.length at s₁ s₂ s₃
       unfold Seg.toVec at s₁ s₂ s₃
       have : tr₁.point₁ = (Triangle.edge₂ tr₁).2 := by rfl
       rw[<-this] at s₂
       have : tr₁.point₁ = (Triangle.edge₃ tr₁).1 := by rfl
       rw[<-this] at s₃
       have : tr₁.point₂ = (Triangle.edge₁ tr₁).1 := by rfl
       rw[<-this] at s₁
       have : tr₁.point₂ = (Triangle.edge₃ tr₁).2 := by rfl
       rw[<-this] at s₃
       have : tr₁.point₃ = (Triangle.edge₂ tr₁).1 := by rfl
       rw[<-this] at s₂
       have : tr₁.point₃ = (Triangle.edge₁ tr₁).2 := by rfl
       rw[<-this] at s₁
       rw[s₁,s₃] at leq'
       rw[s₃] at leq
       have : ‖VEC tr₁.point₁ tr₁.point₃‖ = ‖VEC tr₁.point₃ tr₁.point₁‖ := by sorry
       rw[this,s₂] at leq 
       
    have d₂₁: (¬ tr₂.is_nd) → (¬ tr₁.is_nd) := by 
     intro i
     unfold Triangle.is_nd at i
     push_neg at i
     unfold Triangle.is_nd 
     push_neg 
     unfold colinear at i
     have i' :=eq_true i
     rw[dite_eq_left_iff] at i'
     simp at i'
     by_cases m : (Triangle.point₃ = Triangle.point₂ ∨ Triangle.point₁ = Triangle.point₃ ∨ Triangle.point₂ = Triangle.point₁)
     · rcases m with (m₁|(m₂|m₃))
       · unfold Seg.length Seg.toVec Seg.source Seg.target at s₁--情况1
         have i₁ : (Triangle.edge₁ tr₂).1=tr₂.2 := by unfold Seg.source;rfl
         have i₂ : (Triangle.edge₁ tr₂).2=tr₂.3 := by unfold Seg.target;rfl
         rw[← i₁,← i₂] at m₁
         have i₄ : VEC (Triangle.edge₁ tr₂).1 (Triangle.edge₁ tr₂).2=0 := by rw[m₁];apply vec_same_eq_zero
         have i₅ : ‖VEC (Triangle.edge₁ tr₂).1 (Triangle.edge₁ tr₂).2‖=0 := by rw[i₄];norm_num
         have i₆ : ‖VEC (Triangle.edge₁ tr₁).1 (Triangle.edge₁ tr₁).2‖=0 := by unfold Seg.source Seg.target;rw[s₁];exact i₅
         have i₇ : (Triangle.edge₁ tr₁).1=(Triangle.edge₁ tr₁).2 := by unfold Vec.mk_pt_pt at i₆;norm_num at i₆;simp only[i₆]
         by_contra h₀
         unfold colinear at h₀
         have h₀' :=eq_false h₀
         have h₀'':=dite_eq_iff'.mp h₀'
         rcases h₀'' with ⟨h1,h2⟩
         have j₂: tr₁.2=(Triangle.edge₁ tr₁).1 := by unfold Seg.source Triangle.edge₁;dsimp
         have j₃:(Triangle.edge₁ tr₁).2=tr₁.3 := by unfold Seg.target Triangle.edge₁;dsimp
         rw[← j₂,j₃] at i₇
         apply false_of_true_eq_false
         apply h1
         constructor
         rw[i₇]
       · unfold Seg.length Seg.toVec Seg.source Seg.target at s₂--情况2
         have i₁ : (Triangle.edge₂ tr₂).1=tr₂.3 := by unfold Seg.source;rfl
         have i₂ : (Triangle.edge₂ tr₂).2=tr₂.1 := by unfold Seg.target;rfl
         rw[← i₁,← i₂] at m₂
         have i₄ : VEC (Triangle.edge₂ tr₂).1 (Triangle.edge₂ tr₂).2=0  := by rw[m₂];apply vec_same_eq_zero
         have i₅ : ‖VEC (Triangle.edge₂ tr₂).1 (Triangle.edge₂ tr₂).2‖=0 := by rw[i₄];norm_num
         have i₆ : ‖VEC (Triangle.edge₂ tr₁).1 (Triangle.edge₂ tr₁).2‖=0 := by unfold Seg.source Seg.target;rw[s₂];exact i₅
         have i₇ : (Triangle.edge₂ tr₁).1=(Triangle.edge₂ tr₁).2 := by unfold Vec.mk_pt_pt at i₆;norm_num at i₆;simp only[i₆]
         by_contra h₀
         unfold colinear at h₀
         have h₀' :=eq_false h₀
         have h₀'':=dite_eq_iff'.mp h₀'
         rcases h₀'' with ⟨h1,h2⟩
         have j₂:(Triangle.edge₂ tr₁).1=tr₁.3 := by unfold Seg.source Triangle.edge₂;dsimp
         have j₃:(Triangle.edge₂ tr₁).2=tr₁.1 := by unfold Seg.target Triangle.edge₂;dsimp
         rw[j₂,j₃] at i₇
         apply false_of_true_eq_false
         apply h1
         apply Or.inr
         apply Or.inl 
         rw[i₇]
       · unfold Seg.length Seg.toVec Seg.source Seg.target at s₃--情况3
         have i₁ : (Triangle.edge₃ tr₂).1=tr₂.1 := by unfold Seg.source;rfl
         have i₂ : (Triangle.edge₃ tr₂).2=tr₂.2 := by unfold Seg.target;rfl
         rw[← i₁,← i₂] at m₃
         have i₄ : VEC (Triangle.edge₃ tr₂).1 (Triangle.edge₃ tr₂).2=0 := by rw[m₃];apply vec_same_eq_zero
         have i₅ : ‖VEC (Triangle.edge₃ tr₂).1 (Triangle.edge₃ tr₂).2‖=0 := by rw[i₄];norm_num
         have i₆ : ‖VEC (Triangle.edge₃ tr₁).1 (Triangle.edge₃ tr₁).2‖=0 := by unfold Seg.source Seg.target;rw[s₃];exact i₅
         have i₇ : (Triangle.edge₃ tr₁).1=(Triangle.edge₃ tr₁).2 := by unfold Vec.mk_pt_pt at i₆;norm_num at i₆;simp only[i₆]
         by_contra h₀
         unfold colinear at h₀
         have h₀' :=eq_false h₀
         have h₀'':=dite_eq_iff'.mp h₀'
         rcases h₀'' with ⟨h1,h2⟩
         have j₂:(Triangle.edge₃ tr₁).1=tr₁.1 := by unfold Seg.source Triangle.edge₃;dsimp
         have j₃:(Triangle.edge₃ tr₁).2=tr₁.2 := by unfold Seg.target Triangle.edge₃;dsimp
         rw[j₂,j₃] at i₇
         apply false_of_true_eq_false
         apply h1
         apply Or.inr
         apply Or.inr
         rw[i₇]
     · have mm :=eq_true (i' m)
       unfold colinear_of_nd at mm

    by_cases m: tr₁.is_nd
    · simp at nd
      have m' :=d₂₁ (nd m)
      exfalso
      exact m' m
    · have m' := d₁₂ m
      have m₁:=eq_false m
      have m₂:=eq_false m'
      rw[m₁,m₂]
      
theorem edge₁ : tr₁.edge₁.length = tr₂.edge₁.length := by
  rw[IsCongr] at h
  have h' :=eq_true h
  by_cases nd:(tr₁.is_nd ∧ tr₂.is_nd)
  · simp[nd] at h'
    rcases h' with ⟨s₁,_⟩
    exact s₁
  · simp[nd] at h'
    rcases h' with ⟨t₁,_⟩
    exact t₁

theorem edge₂ : tr₁.edge₂.length = tr₂.edge₂.length := by
  rw[IsCongr] at h
  have h' :=eq_true h
  by_cases nd:(tr₁.is_nd ∧ tr₂.is_nd)
  · simp[nd] at h'
    rcases h' with ⟨_,⟨s₂,_⟩⟩
    exact s₂
  · simp[nd] at h' 
    rcases h' with ⟨_,⟨t₂,_⟩⟩
    exact t₂
  
theorem edge₃ : tr₁.edge₃.length = tr₂.edge₃.length := by
  rw[IsCongr] at h
  have h' :=eq_true h
  by_cases nd:(tr₁.is_nd ∧ tr₂.is_nd)
  · simp[nd] at h'
    rcases h' with ⟨_,⟨_,⟨s₃,_⟩⟩⟩
    exact s₃
  · simp[nd] at h' 
    rcases h' with ⟨_,⟨_,t₃⟩⟩
    exact t₃
  
end triangle

section triangle_nd

variable (tr_nd₁ tr_nd₂: Triangle_nd P) (h:tr_nd₁.1 IsCongrTo tr_nd₂.1)

theorem angle₁ : tr_nd₁.angle₁ = tr_nd₂.angle₁ := by
  rw[IsCongr] at h
  have i : Triangle.is_nd tr_nd₁.1 ∧ Triangle.is_nd tr_nd₂.1 := by constructor;exact tr_nd₁.2;exact tr_nd₂.2
  simp[i] at h
  rcases h with ⟨_,⟨_,⟨_,⟨h₄,_⟩⟩⟩⟩
  exact h₄
  
theorem angle₂ : tr_nd₁.angle₂ = tr_nd₂.angle₂ := by
  rw[IsCongr] at h
  have i : Triangle.is_nd tr_nd₁.1 ∧ Triangle.is_nd tr_nd₂.1 := by constructor;exact tr_nd₁.2;exact tr_nd₂.2
  simp[i] at h
  rcases h with ⟨_,⟨_,⟨_,⟨_,⟨h₅,_⟩⟩⟩⟩⟩
  exact h₅

theorem angle₃ : tr_nd₁.angle₃ = tr_nd₂.angle₃ := by
  rw[IsCongr] at h
  have i : Triangle.is_nd tr_nd₁.1 ∧ Triangle.is_nd tr_nd₂.1 := by constructor;exact tr_nd₁.2;exact tr_nd₂.2
  simp[i] at h
  rcases h with ⟨_,⟨_,⟨_,⟨_,⟨_,h₆⟩⟩⟩⟩⟩
  exact h₆

theorem is_cclock : tr_nd₁.is_cclock = tr_nd₂.is_cclock := sorry

end triangle_nd

end IsCongr

namespace IsCongr

variable (tr tr₁ tr₂ tr₃: Triangle P)

protected theorem refl : tr IsCongrTo tr := by 
  rw[IsCongr]
  by_cases h': Triangle.is_nd tr 
  · have h'' : Triangle.is_nd tr ∧ Triangle.is_nd tr := by constructor;exact h';exact h'
    rw[dif_pos h'']
    repeat
     constructor
     rfl
    rfl
  · have h'' : ¬ (Triangle.is_nd tr ∧ Triangle.is_nd tr) := by push_neg;intro ;exact h'
    rw[dif_neg h'']
    repeat
     constructor
     rfl
    rfl
  

protected theorem symm (h : tr₁ IsCongrTo tr₂) : tr₂ IsCongrTo tr₁ := by sorry

protected theorem trans (h₁ : tr₁ IsCongrTo tr₂) (h₂ : tr₂ IsCongrTo tr₃) : tr₁ IsCongrTo tr₃ := by sorry

instance : IsEquiv (Triangle P) IsCongr where
  refl := IsCongr.refl
  symm := IsCongr.symm
  trans := IsCongr.trans

end IsCongr

/- Anti-congruence -/
def IsACongr (tr₁ tr₂: Triangle P) : Prop := by
  by_cases tr₁.is_nd ∧ tr₂.is_nd
  · let tr_nd₁ : Triangle_nd P := ⟨tr₁, h.1⟩
    let tr_nd₂ : Triangle_nd P := ⟨tr₂, h.2⟩
    exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length ∧ tr_nd₁.angle₁ = - tr_nd₂.angle₁ ∧ tr_nd₁.angle₂ = - tr_nd₂.angle₂ ∧ tr_nd₁.angle₃ = - tr_nd₂.angle₃
  · exact tr₁.edge₁.length = tr₂.edge₁.length ∧ tr₁.edge₂.length = tr₂.edge₂.length ∧ tr₁.edge₃.length = tr₂.edge₃.length

scoped infix : 50 "IsACongrTo" => IsACongr

scoped infix : 50 "≃ₐ" => IsACongr --do we need?

namespace IsACongr

section triangle

variable (tr₁ tr₂: Triangle P) (h : tr₁ IsACongrTo tr₂)

theorem is_nd: tr₁.is_nd ↔ tr₂.is_nd := by sorry

theorem edge₁ : tr₁.edge₁.length = tr₂.edge₁.length := by
  rw[IsACongr] at h
  have h' :=eq_true h
  by_cases nd:(tr₁.is_nd ∧ tr₂.is_nd)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h' 
    rcases h' with ⟨s₁,_⟩
    exact s₁
  · simp only [nd, dite_false, eq_iff_iff, iff_true] at h' 
    rcases h' with ⟨t₁,_⟩
    exact t₁

theorem edge₂ : tr₁.edge₂.length = tr₂.edge₂.length := by
  rw[IsACongr] at h
  have h' :=eq_true h
  by_cases nd:(tr₁.is_nd ∧ tr₂.is_nd)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h' 
    rcases h' with ⟨_,⟨s₂,_⟩⟩
    exact s₂
  · simp only [nd, dite_false, eq_iff_iff, iff_true] at h'  
    rcases h' with ⟨_,⟨t₂,_⟩⟩
    exact t₂

theorem edge₃ : tr₁.edge₃.length = tr₂.edge₃.length := by
  rw[IsACongr] at h
  have h' :=eq_true h
  by_cases nd:(tr₁.is_nd ∧ tr₂.is_nd)
  · simp only [nd, and_self, dite_true, eq_iff_iff, iff_true] at h' 
    rcases h' with ⟨_,⟨_,⟨s₃,_⟩⟩⟩
    exact s₃
  · simp only [nd, dite_false, eq_iff_iff, iff_true] at h'  
    rcases h' with ⟨_,⟨_,t₃⟩⟩
    exact t₃
  

end triangle

section triangle_nd

variable (tr_nd₁ tr_nd₂: Triangle_nd P) (h : tr_nd₁.1 IsACongrTo tr_nd₂.1)

theorem angle₁ : tr_nd₁.angle₁ = - tr_nd₂.angle₁ := by
  rw[IsACongr] at h
  have i : Triangle.is_nd tr_nd₁.1 ∧ Triangle.is_nd tr_nd₂.1 := by constructor;exact tr_nd₁.2;exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h 
  rcases h with ⟨_,⟨_,⟨_,⟨h₄,_⟩⟩⟩⟩
  exact h₄

theorem angle₂ : tr_nd₁.angle₂ = - tr_nd₂.angle₂ := by
  rw[IsACongr] at h
  have i : Triangle.is_nd tr_nd₁.1 ∧ Triangle.is_nd tr_nd₂.1 := by constructor;exact tr_nd₁.2;exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h 
  rcases h with ⟨_,⟨_,⟨_,⟨_,⟨h₅,_⟩⟩⟩⟩⟩
  exact h₅

theorem angle₃ : tr_nd₁.angle₃ = - tr_nd₂.angle₃ := by
  rw[IsACongr] at h
  have i : Triangle.is_nd tr_nd₁.1 ∧ Triangle.is_nd tr_nd₂.1 := by constructor;exact tr_nd₁.2;exact tr_nd₂.2
  simp only [i, and_self, Subtype.coe_eta, dite_eq_ite, ite_true] at h 
  rcases h with ⟨_,⟨_,⟨_,⟨_,⟨_,h₆⟩⟩⟩⟩⟩
  exact h₆

theorem is_cclock : tr_nd₁.is_cclock = ¬ tr_nd₂.is_cclock := sorry

end triangle_nd

end IsACongr

namespace IsACongr

variable (tr tr₁ tr₂ tr₃: Triangle P)

theorem triv_of_acongr_self (h : tr IsACongrTo tr) : ¬ tr.is_nd := by
  intro m
  have m' : Triangle.is_nd tr ∧ Triangle.is_nd tr := by constructor;exact m;exact m
  rw[IsACongr] at h
  simp only [m', and_self, true_and, dite_true] at h  
  rcases h with ⟨h₁,_⟩
  rw[eq_neg_iff_zero] at h₁

protected theorem symm (h : tr₁ IsACongrTo tr₂) : tr₂ IsACongrTo tr₁ := sorry

theorem congr_of_trans_acongr (h₁ : tr₁ IsACongrTo tr₂) (h₂ : tr₂ IsACongrTo tr₃) : tr₁ IsCongrTo tr₃ := sorry

instance : IsSymm (Triangle P) IsACongr where
  symm := IsACongr.symm

end IsACongr


section criteria
/- 
criteria of congruence of triangles. each SAS ASA AAS SSS involves congr and anti congr. SSS is special.
Need a tactic `Congrence` to consider filp and permutation. -/

variable {tr_nd₁ tr_nd₂ : Triangle_nd P}

/- SAS -/
theorem congr_of_SAS (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (a₁ : tr_nd₁.angle₁ = tr_nd₂.angle₁) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length): tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

theorem acongr_of_SAS (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (a₁ : tr_nd₁.angle₁ = - tr_nd₂.angle₁) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length): tr_nd₁.1 IsACongrTo tr_nd₂.1 := sorry

/- ASA -/
theorem congr_of_ASA (a₂ : tr_nd₁.angle₂ = tr_nd₂.angle₂) (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (a₃ : tr_nd₁.angle₃ = tr_nd₂.angle₃): tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

theorem acongr_of_ASA (a₂ : tr_nd₁.angle₂ = - tr_nd₂.angle₂) (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (a₃ : tr_nd₁.angle₃ = - tr_nd₂.angle₃): tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

/- AAS -/
theorem congr_of_AAS (a₁ : tr_nd₁.angle₁ = tr_nd₂.angle₁) (a₂ : tr_nd₁.angle₂ = tr_nd₂.angle₂) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) : tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

theorem acongr_of_AAS (a₁ : tr_nd₁.angle₁ = - tr_nd₂.angle₁) (a₂ : tr_nd₁.angle₂ = - tr_nd₂.angle₂) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) : tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

/- SSS -/ 
/- cannot decide orientation -/
theorem congr_of_SSS_of_eq_orientation (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) (c : tr_nd₁.is_cclock = tr_nd₂.is_cclock) : tr_nd₁.1 IsCongrTo tr_nd₂.1 := sorry

theorem acongr_of_SSS_of_ne_orientation (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) (c : tr_nd₁.is_cclock = ¬ tr_nd₂.is_cclock) : tr_nd₁.1 IsACongrTo tr_nd₂.1 := sorry

theorem congr_or_acongr_of_SSS (e₁ : tr_nd₁.1.edge₁.length = tr_nd₂.1.edge₁.length) (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length): tr_nd₁.1 IsCongrTo tr_nd₂.1 ∨ tr_nd₁.1 IsACongrTo tr_nd₂.1  := sorry

end criteria


end EuclidGeom