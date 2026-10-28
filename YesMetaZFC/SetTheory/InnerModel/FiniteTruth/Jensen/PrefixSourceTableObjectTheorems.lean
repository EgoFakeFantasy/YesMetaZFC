import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.PrefixSourceTable
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 同一标准索引、任意普通参数的受限真值表原 ZF 推导模式

索引先于所有源参数选择。真值集合在背景宇宙构造，不宣称属于目标 J 层。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
universe u

private def prefixSourceTableBody {p} (φ : S1_binary (p+1)) : Formula 1 4 :=
  .imp (KP.ord0_m (.bound 0)) <| .imp (jh_value_m (.bound 0) (.bound 1)) <|
    .imp (Formula.isOmega (.bound 2)) <| .imp (.mem (.bound 2) (.bound 1)) <|
      .imp (Formula.subset (.bound 3) (.bound 1)) <| .existsE <|
        .conj (.mem .newest (.bound 3)) <| .conj (.mem .newest (.bound 2)) <|
          forallBlock_m (p+1) <|
            .imp (amenableSet_m (oldTerm_m (.bound 2)) (sourceTerm_m 5 0)) <|
              .imp (finConj_m p (fun i => .mem (sourceTerm_m 5 i.succ) (oldTerm_m (.bound 2)))) <|
                prefixSourceRealization_m φ (sourceTerm_m 5)
                  (oldTerm_m (.bound 2)) (oldTerm_m (.bound 3))
                  (oldTerm_m (.bound 4)) (oldTerm_m .newest)

theorem prefixSourceTableBody_closed_l {p} (φ : S1_binary (p+1)) :
    (prefixSourceTableBody φ).FreeClosed := by
  simp -implicitDefEqProofs [prefixSourceTableBody,sourceTerm_m,Definitional.Formula.FreeClosed]

def prefixSourceTableSentence {p} (φ : S1_binary (p+1)) : Sentence :=
  Sentence.forallClosure (prefixSourceTableBody φ) (prefixSourceTableBody_closed_l φ)

theorem prefixSourceTable_models {p} (φ : S1_binary (p+1))
    (useCert : PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) φ.matrix.body)
    (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (prefixSourceTableSentence φ) := by
  intro free
  change Formula.satisfies (⟨Fin.elim0,free⟩ : Env M 0)
    (Formula.forallClosure 4 (prefixSourceTableBody φ))
  apply (Formula.satisfies_forallClosure_iff free (prefixSourceTableBody φ)).mpr
  intro b
  change Formula.satisfies (⟨b,free⟩ : Env M 4) (prefixSourceTableBody φ)
  simp only [prefixSourceTableBody,Formula.satisfies_imp_iff,KP.ord0_sat_l (ZF.modelsKP hZF),
    jh_value_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    forallBlock_sat_l,amenableSet_sat_l,finConj_sat_l,prefixSourceRealization_sat_l hZF.1,
    oldTerm_eval_l,sourceTerm_eval_l,Term.eval_bound]
  intro hα hC hω hωC hUC
  obtain ⟨e,k,empty,c,result⟩ := jh_indexedSigma1_sourceCompile_l hZF φ useCert hα hC hω hωC
  refine ⟨c,result.body.index_natural,result.body.index_mem,?_⟩
  intro values amenable ordinary
  let ρ : Env M (p+1) := ⟨values,free⟩
  exact result.prefix_table_realize_l hZF hα hC hω hωC hUC ρ amenable ordinary

theorem prefixSourceTable_derives {p} (φ : S1_binary (p+1))
    (useCert : PredicateDelta0 (⟨3,by omega⟩ : Fin (p+4)) φ.matrix.body) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (prefixSourceTableSentence φ) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => prefixSourceTable_models φ useCert M hM)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
