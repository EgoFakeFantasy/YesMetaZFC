import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.IndexedSigma1SourceQuery
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 任意固定原保护槽 Σ₁ 源的同索引原对象推导 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u

private def indexedSigma1SourceBody {p} (φ : S1_binary (p+1)) : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 2)) <| .imp (jh_value_m (.bound 2) (.bound 1)) <|
    .imp (Formula.isOmega .newest) <| .imp (.mem .newest (.bound 1)) <|
    .existsE <| .existsE <| .existsE <| .existsE <|
      .conj (pc_num_m 0 (.bound 1)) <| .conj (.mem (.bound 1) (.bound 5)) <|
      .conj (.mem (.bound 3) (.bound 4)) <| .conj (.mem (.bound 3) (.bound 5)) <|
      .conj (pc_num_m (p+2) (.bound 2)) <| .conj (.mem (.bound 2) (.bound 5)) <|
      .conj (.mem .newest (.bound 4)) <| .conj (.mem .newest (.bound 5)) <|
      .conj (oc_pair_m (𝒞 := kpair_convention_l) (.bound 3) (.bound 2) .newest) <|
      .conj (.existsE <| .existsE <| .existsE <| .existsE <| .existsE <|
        .conj (pboundedFormula_m (.bound 4) (.bound 9) (.bound 3) (.bound 2) (.bound 1))
          (.conj (programNumber_m (𝒞 := kpair_convention_l) (.bound 9) (.bound 3) (.bound 2) (.bound 1) .newest (.bound 8))
            (.mem (.bound 7) (.bound 3)))) <|
      .conj (indexedSigma1Query_m φ (.bound 4) .newest (.bound 2) (.bound 5) (.bound 1))
        (niceSourceInputRealization_m (sigma1SourceSlot_l p) (.bound 4) .newest (.bound 2) (.bound 5) (.bound 1))

theorem indexedSigma1SourceBody_closed_l {p} (φ : S1_binary (p+1)) : (indexedSigma1SourceBody φ).FreeClosed := by
  simp -implicitDefEqProofs [indexedSigma1SourceBody,indexedSigma1Query_closed_l,niceSourceInputRealization_closed_l,
    Definitional.Formula.FreeClosed]

def indexedSigma1SourceSentence {p} (φ : S1_binary (p+1)) : Sentence :=
  .ofFormula (indexedSigma1SourceBody φ) (indexedSigma1SourceBody_closed_l φ)

theorem indexedSigma1Source_models {p} (φ : S1_binary (p+1))
    (useCert : PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) φ.matrix.body)
    (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) : M.SatisfiesSentence (indexedSigma1SourceSentence φ) := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (indexedSigma1SourceBody φ)
  simp only [indexedSigma1SourceBody,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,pc_num_sat_l hZF.1,pboundedFormula_sat_l (ZF.modelsKP hZF),
    oc_pair_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    programNumber_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,indexedSigma1Query_sat_l hZF.1,niceSourceInputRealization_sat_l hZF.1]
  intro α C ω hα hC hω hωC
  obtain ⟨e,k,empty,c,result⟩ := jh_indexedSigma1_sourceCompile_l hZF φ useCert hα hC hω hωC
  let base := result.body.normalized
  refine ⟨e,k,empty,c,base.zero,base.empty_mem,base.number_natural,base.number_mem,base.count,base.count_mem,
    result.body.index_natural,result.body.index_mem,result.body.pair,base.program,?_,?_⟩
  · intro x params input values outer boundedCorr
    let η : Env M (p+1) := ⟨values,free⟩
    have corr : SourceParameter_d (fun j => if j = sigma1SourceSlot_l p then empty else (η.push x).bound j) params :=
      boundedSourceParameter_forget_l boundedCorr
    refine ⟨fun y selected => result.sound_l hZF hω η corr outer selected,
      fun y selected => result.within_sound_l hZF hα hC hω hωC η corr outer selected,?_⟩
    intro amenable hinC parameterDomain source
    obtain ⟨X,fn⟩ := parameterDomain
    exact result.local_total_l hZF hα hC hω hωC η amenable hinC fn corr outer source
  · intro values inC
    let η : Env M (p+2) := ⟨values,free⟩
    obtain ⟨X,params,input,hXC,hx,hpC,hinC,fn,corr,outer⟩ := result.body.realizes_l hZF hα hC η inC
    have standard := result.body.input_standard_l hZF hω (jh_value_transitive_l (ZF.models_kpi_l hZF) hC) hXC fn outer
    refine ⟨X,params,input,hXC,hx,hpC,hinC,fn,boundedSourceParameter_of_l hZF.1 base.count corr,outer,standard,?_⟩
    intro b Y hb boundedCorr
    exact (base.parameter_unique X Y params b η fn hb corr (boundedSourceParameter_forget_l boundedCorr)).symm

theorem indexedSigma1Source_derives {p} (φ : S1_binary (p+1))
    (useCert : PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) φ.matrix.body) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (indexedSigma1SourceSentence φ) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => indexedSigma1Source_models φ useCert M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
