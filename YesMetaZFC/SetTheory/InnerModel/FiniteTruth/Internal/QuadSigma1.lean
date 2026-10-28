import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.QuadCertificate

/-! # 原四字段指令数码的实际 Σ₁ 图 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def quadCode_s : S1_binary 1 where
  matrix := { body := quadCheck_m (.bound 3) (.bound 2) (.bound 1) .newest, delta0 := quadCheck_delta_l .. }

theorem quadCode_matrix_sat_l (hKP : M.Models KP) (ρ : Env M 1) (c z w : M.Domain) :
    Formula.satisfies (((ρ.push c).push z).push w) quadCode_s.matrix.body ↔ QuadCheck_d (ρ.bound 0) c z w :=
  quadCheck_sat_l hKP (((ρ.push c).push z).push w) (.bound 3) (.bound 2) (.bound 1) .newest

theorem quadCode_sat_l (hZF : M.Models ZF) (ρ : Env M 1) (c z : M.Domain) (hω : M.IsOmega (ρ.bound 0)) :
    quadCode_s.schema.denote ρ c z ↔ NaturalQuad_d (ρ.bound 0) c ∧ QuadNumber_d (kp_pair_l (ZF.modelsKP hZF)) c z := by
  rw [S1_binary.sat_l]
  simp only [quadCode_matrix_sat_l (ZF.modelsKP hZF)]
  exact ⟨fun ⟨_,cert⟩ => quadCheck_sound_l hZF cert,fun ⟨input,code⟩ => quadCheck_exists_l hZF hω input code⟩

theorem quadCode_unique_l (hZF : M.Models ZF) (ρ : Env M 1) {c z w : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (hz : quadCode_s.schema.denote ρ c z) (hw : quadCode_s.schema.denote ρ c w) : z = w :=
  quadNumber_unique_l (kp_pair_l (ZF.modelsKP hZF)) hZF ((quadCode_sat_l hZF ρ c z hω).mp hz).2
    ((quadCode_sat_l hZF ρ c w hω).mp hw).2

theorem quadCode_injective_l (hZF : M.Models ZF) (ρ : Env M 1) {c d z : M.Domain}
    (hω : M.IsOmega (ρ.bound 0)) (hc : quadCode_s.schema.denote ρ c z) (hd : quadCode_s.schema.denote ρ d z) : c = d :=
  quadNumber_injective_l (kp_pair_l (ZF.modelsKP hZF)) hZF ((quadCode_sat_l hZF ρ c z hω).mp hc).2
    ((quadCode_sat_l hZF ρ d z hω).mp hd).2

theorem bnode_naturalQuad_l (hZF : M.Models ZF) {T ω n r c : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (hr : M.mem r ω) (node : Bnode_d T ω n r c) : NaturalQuad_d ω c := by
  have one (tag : Nat) {A B D : M.Domain} (aω : M.MemberSubset A ω)
      (bω : M.MemberSubset B ω) (dω : M.MemberSubset D ω) (h : Bcase_d T tag c A B D) : NaturalQuad_d ω c := by
    obtain ⟨i,_,j,_,k,_,⟨t,_,v,_,ht,⟨p,hp,hv⟩,hc⟩,hi,hj,hk⟩ := h
    exact ⟨t,v,i,p,j,k,num_mem_l hZF.1 hω ht,aω i hi,bω j hj,dω k hk,hc,hv,hp⟩
  have nω := hω.transitive hZF n hn
  have rω := hω.transitive hZF r hr
  rcases node with node | node | node | node
  · exact one 0 nω nω (fun _ h => h) node
  · exact one 1 nω nω (fun _ h => h) node
  · exact one 2 rω rω (fun _ h => h) node
  · exact one 3 nω nω rω node

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
