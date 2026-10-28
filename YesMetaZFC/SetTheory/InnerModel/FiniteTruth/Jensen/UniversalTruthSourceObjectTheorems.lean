import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.UniversalTruthSourceQuery
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.UniversalTruthSource
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 同一通用表对全部原源环境的原 ZF 模式

原源索引、完整参数长度与空值先于所有源值、所有给定通用表及所有输入选择。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
universe u

private def universalTruthSourceBody {p} (φ : S1_binary (p+1)) : Formula 1 3 :=
  .imp (KP.ord0_m (.bound 0)) <| .imp (jh_value_m (.bound 0) (.bound 1)) <|
    .imp (Formula.isOmega (.bound 2)) <| .imp (.mem (.bound 2) (.bound 1)) <|
      .existsE <| .existsE <| .existsE <|
        .conj (pc_num_m (p+2) (.bound 2)) <| .conj (.mem (.bound 2) (.bound 4)) <|
          .conj (pc_num_m 0 (.bound 1)) <| .conj (.mem (.bound 1) (.bound 4)) <|
            .conj (.mem .newest (.bound 5)) <| .conj (.mem .newest (.bound 4)) <|
              universalTruthSourceQuery_m φ (.bound 4) (.bound 5) .newest (.bound 2) (.bound 1)

theorem universalTruthSourceBody_closed_l {p} (φ : S1_binary (p+1)) :
    (universalTruthSourceBody φ).FreeClosed := by
  simp -implicitDefEqProofs [universalTruthSourceBody,Definitional.Formula.FreeClosed]

def universalTruthSourceSentence {p} (φ : S1_binary (p+1)) : Sentence :=
  Sentence.forallClosure (universalTruthSourceBody φ) (universalTruthSourceBody_closed_l φ)

theorem universalTruthSource_models {p} (φ : S1_binary (p+1))
    (useCert : PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) φ.matrix.body)
    (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (universalTruthSourceSentence φ) := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0)
    (Formula.forallClosure 3 (universalTruthSourceBody φ))
  apply (Formula.satisfies_forallClosure_iff free (universalTruthSourceBody φ)).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 3) (universalTruthSourceBody φ)
  simp only [universalTruthSourceBody,Formula.satisfies_imp_iff,KP.ord0_sat_l (ZF.modelsKP hZF),
    jh_value_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,pc_num_sat_l hZF.1,
    universalTruthSourceQuery_sat_l hZF.1,Term.eval_bound]
  intro hα hC hω hωC
  obtain ⟨e,k,empty,c,result⟩ := jh_indexedSigma1_sourceCompile_l hZF φ useCert hα hC hω hωC
  let base := result.body.normalized
  refine ⟨k,empty,c,base.count,base.count_mem,base.zero,base.empty_mem,
    result.body.index_natural,result.body.index_mem,?_⟩
  intro values amenable ordinary T table x hxC
  let ρ : Env M (p+1) := ⟨values,free⟩
  exact result.universal_table_realizes_l hZF hα hC hω hωC ρ amenable ordinary table hxC

theorem universalTruthSource_derives {p} (φ : S1_binary (p+1))
    (useCert : PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) φ.matrix.body) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (universalTruthSourceSentence φ) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => universalTruthSource_models φ useCert M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
