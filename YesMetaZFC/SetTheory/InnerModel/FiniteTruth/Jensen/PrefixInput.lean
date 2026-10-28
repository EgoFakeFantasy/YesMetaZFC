import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.PrefixInputSigma1
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ParameterAssignment

/-! # 固定内部参数前缀的完整同层证书 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem jh_prefixParameters_l (hZF : M.Models ZF) {α C ω P x l X z : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hPC : M.mem P C) (hxC : M.mem x C) (hl : M.mem l ω) (zero : Num_d 0 z) (pref : Fn0_d l X P) :
    ∃ Y s k f g params, M.mem Y C ∧ M.TransitiveSet Y ∧ M.mem f C ∧ M.mem g C ∧ M.mem params C ∧
      PrefixParameters_d ω P x l s k Y z f g params := by
  let hKP := ZF.modelsKP hZF
  have rud := jh_value_closed_l (ZF.models_kpi_l hZF) hα h
  obtain ⟨B,hBC,hb,prefB,hxB⟩ := jh_assignmentDomain_withValue_l hZF hα h hPC hxC (fn0_function_l hKP pref)
  obtain ⟨Y,hYC,hY⟩ := rud.union_l hKP hBC hωC
  have sub : M.MemberSubset B Y := fun v hv => (hY v).mpr (Or.inl hv)
  have hy : M.TransitiveSet Y := fun v hv t ht => (hY t).mpr (((hY v).mp hv).elim
    (fun hv => Or.inl (hb v hv t ht)) (fun hv => Or.inr (hω.transitive hZF v hv t ht)))
  have prefY := fn0_of_function_l hKP (function_codomain_mono_l (kp_pair_l hKP) sub prefB)
  have hzY := (hY z).mpr (Or.inr (num_mem_l hZF.1 hω zero))
  obtain ⟨s,k,f,g,params,cert⟩ := prefixParameters_exists_l hZF hω hl zero hzY (sub x hxB) prefY
  have hfC := jh_finite_function_mem_l hZF hα h hω hωC hYC cert.first.finite (fn0_function_l hKP cert.first.full)
  have hgC := jh_finite_function_mem_l hZF hα h hω hωC hYC cert.second.finite (fn0_function_l hKP cert.second.full)
  have hpC := jh_finite_function_mem_l hZF hα h hω hωC hYC cert.second.finite (fn0_function_l hKP cert.full)
  exact ⟨Y,s,k,f,g,params,hYC,hy,hfC,hgC,hpC,cert⟩

theorem jh_prefixInputCheck_l (hZF : M.Models ZF) {α C ω P input packet : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (hω : M.IsOmega ω) (hωC : M.mem ω C)
    (hPC : M.mem P C) (hinC : M.mem input C) (graph : PrefixInput_d ω P input packet) :
    M.mem packet C ∧ ∃ l s k X z f g params c x, M.mem l C ∧ M.mem s C ∧ M.mem k C ∧ M.mem X C ∧
      M.mem z C ∧ M.mem f C ∧ M.mem g C ∧ M.mem params C ∧ M.mem c C ∧ M.mem x C ∧
        PrefixInputCheck_d ω P input packet l s k X z f g params c x := by
  obtain ⟨l,s,k,X,z,f,g,params,c,x,hc,outer,inner,cert⟩ := graph
  have trans := jh_value_transitive_l (ZF.models_kpi_l hZF) h
  have coords := po_pair_bound_l trans hinC outer
  have hl := hω.transitive hZF s cert.first.finite l cert.first.capacity
  obtain ⟨Y,s',k',f',g',params',hYC,_,hfC,hgC,hpC,newCert⟩ :=
    jh_prefixParameters_l hZF hα h hω hωC hPC coords.2 hl cert.first.zero cert.first.parameters
  have eq := cert.unique_l hZF hω newCert
  subst params'
  have hpacketC := (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) .opair c params c
    coords.1 hpC coords.1 packet (rd_opair_value_l hZF.1 inner)
  exact ⟨hpacketC,l,s',k',Y,z,f',g',params,c,x,trans ω hωC l hl,
    trans ω hωC s' newCert.first.finite,trans ω hωC k' newCert.second.finite,hYC,
    trans ω hωC z (num_mem_l hZF.1 hω cert.first.zero),hfC,hgC,hpC,coords.1,coords.2,hc,outer,inner,newCert⟩

theorem jh_prefixInput_within_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 3) (input packet : M.Domain)
    (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hPC : M.mem (ρ.bound 2) C)
    (hinC : M.mem input C) :
    Within_d prefixInput_s ρ input packet C ↔ PrefixInput_d (ρ.bound 1) (ρ.bound 2) input packet := by
  constructor
  · intro hit
    exact (prefixInput_sat_l (ZF.modelsKP hZF) ρ input packet).mp (within_toSchema_l prefixInput_s ρ hit)
  · intro graph
    obtain ⟨_,l,s,k,X,z,f,g,params,c,x,hlC,hsC,hkC,hXC,hzC,hfC,hgC,hpC,hcC,hxC,cert⟩ :=
      jh_prefixInputCheck_l hZF hα h hω hωC hPC hinC graph
    have all : ∀ v, v ∈ [l,s,k,X,z,f,g,params,c,x] → M.mem v C := by
      intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨w,hwC,hw⟩ := rd_finiteTruth_cover_l (ZF.modelsKP hZF)
      (jh_value_closed_l (ZF.models_kpi_l hZF) hα h) hωC [l,s,k,X,z,f,g,params,c,x] all
    exact ⟨w,hwC,(prefixInput_matrix_sat_l (ZF.modelsKP hZF) ρ input packet w).mpr
      ⟨l,hw l (by simp),s,hw s (by simp),k,hw k (by simp),X,hw X (by simp),z,hw z (by simp),
        f,hw f (by simp),g,hw g (by simp),params,hw params (by simp),c,hw c (by simp),x,hw x (by simp),cert⟩⟩

theorem jh_prefixInput_output_l (hZF : M.Models ZF) {α C : M.Domain}
    (hα : M.IsOrdinal α) (h : Jh_value_d α C) (ρ : Env M 3) {input packet : M.Domain}
    (hω : M.IsOmega (ρ.bound 1)) (hωC : M.mem (ρ.bound 1) C) (hPC : M.mem (ρ.bound 2) C)
    (hinC : M.mem input C) (graph : prefixInput_s.schema.denote ρ input packet) : M.mem packet C :=
  (jh_prefixInputCheck_l hZF hα h hω hωC hPC hinC ((prefixInput_sat_l (ZF.modelsKP hZF) ρ input packet).mp graph)).1

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
