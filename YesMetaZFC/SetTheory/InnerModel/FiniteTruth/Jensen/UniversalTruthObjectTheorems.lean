import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.UniversalTruthCoverage
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ParameterCoverNonmembership
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 通用编码表存在、包含及全参数覆盖非成员性的原 ZF 推导 -/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u

private def universalTruthExistsBody : Formula 1 3 :=
  .existsE <| .conj (universalTruthTable_m (.bound 1) (.bound 2) (.bound 3) .newest) <|
    .forallE <| .imp (universalTruthTable_m (.bound 2) (.bound 3) (.bound 4) .newest)
      (Formula.extensionalEq .newest (.bound 1))

def universalTruthExistsSentence : Sentence := Sentence.forallClosure universalTruthExistsBody
  (by simp -implicitDefEqProofs [universalTruthExistsBody,Definitional.Formula.FreeClosed])

theorem universalTruthExists_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence universalTruthExistsSentence := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 3 universalTruthExistsBody)
  apply (Formula.satisfies_forallClosure_iff free universalTruthExistsBody).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 3) universalTruthExistsBody
  simp only [universalTruthExistsBody,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    universalTruthTable_sat_l hZF.1,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,Term.eval_bound]
  let ρ : Env M 2 := ⟨Fin.cases (b 0) (fun _ => b 1),free⟩
  obtain ⟨T,table⟩ := universalTruthTable_exists_l hZF ρ (b 2)
  exact ⟨T,table,fun V other => universalTruthTable_unique_l hZF.1 other table⟩

theorem universalTruthExists_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF universalTruthExistsSentence :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => universalTruthExists_models M hM)

private def universalTruthSubsetBody : Formula 1 5 :=
  .imp (KP.ord0_m (.bound 0)) <| .imp (jh_value_m (.bound 0) (.bound 1)) <|
    .imp (Formula.isOmega (.bound 3)) <| .imp (.mem (.bound 3) (.bound 1)) <|
      .imp (universalTruthTable_m (.bound 2) (.bound 3) (.bound 1) (.bound 4))
        (Formula.subset (.bound 4) (.bound 1))

def universalTruthSubsetSentence : Sentence := Sentence.forallClosure universalTruthSubsetBody
  (by simp -implicitDefEqProofs [universalTruthSubsetBody,Definitional.Formula.FreeClosed])

theorem universalTruthSubset_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence universalTruthSubsetSentence := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 5 universalTruthSubsetBody)
  apply (Formula.satisfies_forallClosure_iff free universalTruthSubsetBody).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 5) universalTruthSubsetBody
  simp only [universalTruthSubsetBody,Formula.satisfies_imp_iff,KP.ord0_sat_l (ZF.modelsKP hZF),
    jh_value_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    universalTruthTable_sat_l hZF.1,Formula.satisfies_subset_iff,Term.eval_bound]
  intro hα hC hω hωC table
  let ρ : Env M 2 := ⟨Fin.cases (b 2) (fun _ => b 3),free⟩
  exact jh_universalTruthTable_subset_l hZF hα hC ρ hω hωC table

theorem universalTruthSubset_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF universalTruthSubsetSentence :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => universalTruthSubset_models M hM)

private def universalTruthProperBody : Formula 1 4 :=
  .imp (KP.ord0_m (.bound 0)) <| .imp (jh_value_m (.bound 0) (.bound 1)) <|
    .imp (Formula.isOmega (.bound 3)) <| .imp (.mem (.bound 3) (.bound 1)) <|
      .imp (amenableSet_m (.bound 1) (.bound 2)) <| .existsE <|
        .conj (universalTruthTable_m (.bound 3) (.bound 4) (.bound 2) .newest) <|
          .conj (Formula.subset .newest (.bound 2)) <|
            .conj (.neg (.mem .newest (.bound 2))) <|
              .conj (parameterCover_m (.bound 2) .newest) <|
                .forallE <| .imp (universalTruthTable_m (.bound 4) (.bound 5) (.bound 3) .newest)
                  (Formula.extensionalEq .newest (.bound 1))

def universalTruthProperSentence : Sentence := Sentence.forallClosure universalTruthProperBody
  (by simp -implicitDefEqProofs [universalTruthProperBody,Definitional.Formula.FreeClosed])

theorem universalTruthProper_models (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence universalTruthProperSentence := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0) (Formula.forallClosure 4 universalTruthProperBody)
  apply (Formula.satisfies_forallClosure_iff free universalTruthProperBody).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 4) universalTruthProperBody
  simp only [universalTruthProperBody,Formula.satisfies_imp_iff,KP.ord0_sat_l (ZF.modelsKP hZF),
    jh_value_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,amenableSet_sat_l,
    Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,universalTruthTable_sat_l hZF.1,
    Formula.satisfies_subset_iff,Formula.satisfies_neg_iff,parameterCover_sat_l hZF.1,
    Formula.satisfies_forall_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,Term.eval_bound]
  intro hα hC hω hωC amenable
  let ρ : Env M 2 := ⟨Fin.cases (b 2) (fun _ => b 3),free⟩
  obtain ⟨T,table⟩ := universalTruthTable_exists_l hZF ρ (b 1)
  have sub := jh_universalTruthTable_subset_l hZF hα hC ρ hω hωC table
  obtain ⟨c,_,_,row⟩ := jh_universalTruthTable_coverage_l hZF hα hC ρ hω hωC amenable table
  have cover : ParameterCover_d (b 1) T := by
    intro x hx
    obtain ⟨input,params,i,hit,pair,entry⟩ := row x hx
    exact ⟨input,params,c,i,hit,pair,entry⟩
  exact ⟨T,table,sub,jh_parameterCover_not_mem_l hZF hα hC cover,cover,
    fun V other => universalTruthTable_unique_l hZF.1 other table⟩

theorem universalTruthProper_derives :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF universalTruthProperSentence :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality (fun M hM => universalTruthProper_models M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
