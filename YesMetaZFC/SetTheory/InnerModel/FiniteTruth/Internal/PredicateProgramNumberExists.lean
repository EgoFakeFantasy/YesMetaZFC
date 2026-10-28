import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.CanonicalPredicateObjectTheorems
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.ProgramNumber
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal.QuadSigma1

/-! # 五类原内部程序复用同一个通用自然数编号

只扩展存在性与合法性证书，不创建平行 NumberedRows 或 ProgramNumber 关系。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem pnode_number_exists_l (hZF : M.Models ZF) {T ω n r c : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (hr : M.mem r ω) (node : Pnode_d T ω n r c) :
    ∃ z, M.mem z ω ∧ QuadNumber_d (kp_pair_l (ZF.modelsKP hZF)) c z := by
  rcases node with old | query
  · exact bnode_number_exists_l hZF hω hn hr old
  · obtain ⟨i,_,j,_,k,_,⟨t,_,v,_,ht,⟨p,hp,hv⟩,code⟩,hi,hj,hk⟩ := query
    exact quadNumber_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω code hv hp
      (num_mem_l hZF.1 hω ht) (hω.transitive hZF n hn i hi) hj hk

theorem pnode_naturalQuad_l (hZF : M.Models ZF) {T ω n r c : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (hr : M.mem r ω) (node : Pnode_d T ω n r c) :
    NaturalQuad_d ω c := by
  rcases node with old | query
  · exact bnode_naturalQuad_l hZF hω hn hr old
  · obtain ⟨i,_,j,_,k,_,⟨t,_,v,_,ht,⟨p,hp,hv⟩,code⟩,hi,hj,hk⟩ := query
    exact ⟨t,v,i,p,j,k,num_mem_l hZF.1 hω ht,hω.transitive hZF n hn i hi,hj,hk,code,hv,hp⟩

theorem pnumberedRows_exists_l (hZF : M.Models ZF) {T ω n L F : M.Domain}
    (hω : M.IsOmega ω) (valid : PBoundedFormula_d T ω n L F) :
    ∃ G, NumberedRows_d (kp_pair_l (ZF.modelsKP hZF)) ω L F G := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hf := fn0_function_l (ZF.modelsKP hZF) valid.graph
  have total i (hi : M.mem i L) c (hic : M.PairMember I i c F) :
      ∃ z, M.mem z ω ∧ QuadNumber_d I c z :=
    pnode_number_exists_l hZF hω valid.variables (hω.transitive hZF L valid.finite i hi)
      (valid.at_l hic).2.2
  let ρ : Env M 1 := ⟨fun _ => F,fun _ => F⟩
  let φ : BinarySchema 1 := { body := .existsE (.conj
    (Formula.orderedPairMem kpair_convention_l (.bound 2) .newest (.bound 3))
    (quadNumber_m (𝒞 := kpair_convention_l) .newest (.bound 1))) }
  have sat i z : φ.denote ρ i z ↔ ∃ c, M.PairMember I i c F ∧ QuadNumber_d I c z := by
    simp only [BinarySchema.denote,φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I,quadNumber_sat_l I hZF.1]
    rfl
  obtain ⟨G,hg,he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := L) (target := ω) (by
    intro i hi
    obtain ⟨c,_,hic⟩ := hf.2.2 i hi
    obtain ⟨z,_,hz⟩ := total i hi c hic
    exact ⟨z,(sat i z).mpr ⟨c,hic,hz⟩⟩) (by
      intro i _ z w hz hw
      obtain ⟨c,hc,hz⟩ := (sat i z).mp hz
      obtain ⟨d,hd,hw⟩ := (sat i w).mp hw
      have eq := hf.1.2 i c d hc hd; subst d
      exact quadNumber_unique_l I hZF hz hw) (by
        intro i z hi hz
        obtain ⟨c,hc,hz⟩ := (sat i z).mp hz
        obtain ⟨w,hw,hc'⟩ := total i hi c hc
        exact (quadNumber_unique_l I hZF hz hc').symm ▸ hw)
  exact ⟨G,hg,fun i z => (he i z).trans (and_congr_right fun _ => sat i z)⟩


theorem pprogramNumber_exists_l (hZF : M.Models ZF) {T ω n L F r : M.Domain}
    (hω : M.IsOmega ω) (valid : PBoundedFormula_d T ω n L F) (hr : M.mem r L) :
    ∃ e, M.mem e ω ∧ ProgramNumber_d (kp_pair_l (ZF.modelsKP hZF)) ω n L F r e := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨G,rows⟩ := pnumberedRows_exists_l hZF hω valid
  have ordinalRows : M.IsOrdinalValuedSequence I G L :=
    ⟨⟨valid.ordinal,rows.1.1,rows.1.2.1⟩,fun _ _ z hz => hω.members_areOrdinals hZF z (rows.1.output_mem_of_pairMember hz)⟩
  obtain ⟨c,seq⟩ := oc_seq_exists_l I hZF valid.finite ordinalRows
  have hc := oc_seq_natural_l I hZF hω rows.1 seq
  obtain ⟨d,pair⟩ := oc_pair_exists_l I hZF (hω.members_areOrdinals hZF n valid.variables) (hω.members_areOrdinals hZF c hc)
  have hd := oc_pair_natural_l I hZF hω valid.variables hc pair
  obtain ⟨e,last⟩ := oc_pair_exists_l I hZF (hω.members_areOrdinals hZF d hd) (valid.ordinal.mem hr)
  have hf := fn0_function_l (ZF.modelsKP hZF) valid.graph
  exact ⟨e,oc_pair_natural_l I hZF hω hd (hω.transitive hZF L valid.finite r hr) last,
    valid.variables,valid.finite,hr,⟨valid.ordinal,hf.1,hf.2.1⟩,G,c,d,rows,seq,pair,last⟩


end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
