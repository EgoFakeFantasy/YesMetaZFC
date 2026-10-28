import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.FoldRun

/-! # 原规范折叠的完整自然数值历史存在性

从原递归序列直接取得全部前缀值与给定根；不另选不对应的宿主历史。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem natural_successorWithin_l (hZF : M.Models ZF) {ω n s r t : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (ht : M.mem t ω)
    (root : M.SuccessorOf s n) (hr : M.mem r n) (next : M.SuccessorOf t r) : M.mem t s := by
  rcases (hω.isOrdinal hZF).wellOrder.linear.compare t ht n hn with eq | htn | hnt
  · exact (hZF.1.eq_of_same_members t n eq) ▸ root.predecessor_mem
  · exact (root t).mpr (Or.inl htn)
  · rcases (next n).mp hnt with hnr | eq
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n ((hω.members_areOrdinals hZF n hn).transitive r hr n hnr)).elim
    · have eqnr := hZF.1.eq_of_same_members n r eq
      subst r
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n hr).elim

theorem foldRun_exists_l (hZF : M.Models ZF) {ω F n c : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (input : Fn0_d n ω F)
    (fold : Oc_fold_d (kp_pair_l (ZF.modelsKP hZF)) F n c) :
    ∃ e s H, FoldRun_d (kp_pair_l (ZF.modelsKP hZF)) ω F n c e s H := by
  let hKP := ZF.modelsKP hZF
  let I := kp_pair_l hKP
  have ff := fn0_function_l hKP input
  have no := hω.members_areOrdinals hZF n hn
  obtain ⟨s,hs,hsω⟩ := hω.1.2 n hn
  have so := hω.members_areOrdinals hZF s hsω
  obtain ⟨_,H,historyRec,_⟩ := oc_fold_exists_l I hZF ff.1 so
  have correct r (hr : M.mem r s) d (hrd : M.PairMember I r d H) : Oc_fold_d I F r d :=
    historyRec.recursionValue_of_pairMember hr hrd
  have pref : Oc_prefix_d I n F := ⟨ff.1,fun r hr => by
    obtain ⟨a,ha,hra⟩ := ff.2.2 r hr
    exact ⟨a,hω.members_areOrdinals hZF a ha,hra⟩⟩
  have sub r (hr : M.mem r s) : M.MemberSubset r n := by
    rcases (hs r).mp hr with hrn | eq
    · exact no.transitive r hrn
    · exact fun x hx => (eq x).mp hx
  have values r (hr : M.mem r s) d (hrd : M.PairMember I r d H) : M.mem d ω :=
    oc_fold_natural_l I hZF hω r (hω.transitive hZF s hsω r hr) F d (pref.mono_l I (sub r hr))
      (fun _ _ _ entry => ff.output_mem_of_pairMember entry) (correct r hr d hrd)
  have fh : M.IsSetFunctionFromTo I H s ω := by
    refine ⟨historyRec.1.2.1,historyRec.1.2.2,fun r hr => ?_⟩
    obtain ⟨d,hrd⟩ := (historyRec.1.2.2 r).mp hr
    exact ⟨d,values r hr d hrd,hrd⟩
  obtain ⟨e,he,heω⟩ := hω.1.1
  have heS := Structure.IsOrdinal.empty_mem_of_nonempty hKP so ⟨n,hs.predecessor_mem⟩ he
  obtain ⟨d,hed⟩ := (historyRec.1.2.2 e).mp heS
  have de : d = e := hZF.1.eq_of_same_members d e (fun x =>
    iff_of_false (oc_fold_zero_l I he (correct e heS d hed) x) (he x))
  have initial : Rd_entry_d e e H := de ▸ hed
  obtain ⟨d,hnd⟩ := (historyRec.1.2.2 n).mp hs.predecessor_mem
  have dc := oc_fold_unique_l I hZF ff.1 (correct n hs.predecessor_mem d hnd) fold
  refine ⟨e,s,H,hn,hsω,hs,input,fn0_of_function_l hKP fh,he,initial,dc ▸ hnd,?_⟩
  intro r hr
  have hrω := hω.transitive hZF n hn r hr
  obtain ⟨t,ht,htω⟩ := hω.1.2 r hrω
  have htS := natural_successorWithin_l hZF hω hn htω hs hr ht
  have hrS := (hs r).mpr (Or.inl hr)
  obtain ⟨a,ha,hra⟩ := ff.2.2 r hr
  obtain ⟨b,hb,hrb⟩ := fh.2.2 r hrS
  obtain ⟨d,hd,htd⟩ := fh.2.2 t htS
  obtain ⟨b',before,pair⟩ := oc_fold_succ_l I hZF ff.1 ht (hω.members_areOrdinals hZF a ha) hra (correct t htS d htd)
  have eq := oc_fold_unique_l I hZF ff.1 before (correct r hrS b hrb)
  exact ⟨a,ha,b,hb,t,htS,d,hd,hra,hrb,ht,htd,eq ▸ pair⟩

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
