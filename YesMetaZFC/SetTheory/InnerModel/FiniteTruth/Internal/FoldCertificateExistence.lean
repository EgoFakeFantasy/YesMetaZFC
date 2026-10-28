import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FoldCertificate

/-! # 完整折叠证书的背景存在性 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}}

theorem foldCheck_exists_l (hZF : M.Models ZF) {ω F n c : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (input : Fn0_d n ω F)
    (fold : Oc_fold_d (kp_pair_l (ZF.modelsKP hZF)) F n c) :
    ∃ e s H V, FoldCheck_d ω F n c e s H V := by
  obtain ⟨e,s,H,run⟩ := foldRun_exists_l hZF hω hn input fold
  let ρ := foldRow_env_l ω F H s
  have total r (hr : M.mem r n) : ∃ w, foldRow_s.denote ρ r w := by
    obtain ⟨a,ha,b,hb,t,ht,d,hd,hra,hrb,hts,htd,pair⟩ := run.step r hr
    obtain ⟨w,wit⟩ := pairWitness_exists_l hZF hω hb ha pair
    exact ⟨w,(foldRow_schema_sat_l (ZF.modelsKP hZF) ω F H s r w).mpr
      ⟨a,ha,b,hb,t,ht,d,hd,hra,hrb,hts,htd,wit⟩⟩
  obtain ⟨V,cover⟩ := ZF.collection_exists_d hZF foldRow_s ρ n total
  exact ⟨e,s,H,V,run.finite,run.successor_finite,run.successor,run.input,run.history,
    run.zero,run.initial,run.final,fun r hr => (cover r hr).imp fun w hw =>
      ⟨hw.1,(foldRow_schema_sat_l (ZF.modelsKP hZF) ω F H s r w).mp hw.2⟩⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
