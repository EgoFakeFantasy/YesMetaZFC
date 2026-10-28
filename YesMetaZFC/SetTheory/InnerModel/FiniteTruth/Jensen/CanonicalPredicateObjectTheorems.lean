import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.CompiledPredicateQuery
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen.ProtectedAssignmentQuery
import YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Foundation.ProjectCompleteness

/-! # 完整 Δ₀ 编译、实际赋值与共享代码的原对象推导

句子自行生成数码框架和程序代码；传递求值域上的源变量由实际函数图实现。
同一代码的正负规格与全部域内源值的实际同层赋值实现都在原对象句子中。
本包不附加旧四类程序的数码合法性；标签 4 的统一数码接口仍须另证。
-/
namespace YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
open YesMetaZFC
open YesMetaZFC.SetTheory
open YesMetaZFC.SetTheory.Definitional.Project
open YesMetaZFC.SetTheory.InnerModel
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Internal
open YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBlock
universe u

private def deltaOld_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin 4) : Term (4+(deltaSourceWidth_l p reserve)) :=
  oldTerm_m (.bound i : Term 4)
private def deltaSlot_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin (deltaSourceWidth_l p reserve)) : Term (4+(deltaSourceWidth_l p reserve)) :=
  sourceTerm_m 4 i
private def deltaSource_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin d) : Term (4+(deltaSourceWidth_l p reserve)) :=
  sourceTerm_m 4 ⟨i.val,by unfold deltaSourceWidth_l; omega⟩
private def deltaResult_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin 4) : Term ((4+(deltaSourceWidth_l p reserve))+4) := .bound ⟨i.val,by unfold deltaSourceWidth_l; omega⟩
private def deltaQuerySlot_m {d} (p : Cp_test d) (reserve : Nat) (i : Fin 6) : Term ((4+(deltaSourceWidth_l p reserve))+6) := .bound ⟨i.val,by unfold deltaSourceWidth_l; omega⟩

private def canonicalPredicateResult_m {d} (a : Fin d) (reserve : Nat) (p : Cp_test d) (φ : Formula 1 d) : Formula 1 (4+(deltaSourceWidth_l p reserve)) :=
  .existsE <| .existsE <| .existsE <| .existsE <|
    .conj (.mem (deltaResult_m p reserve 3) (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken) <|
      .conj (Formula.isTransitive (deltaResult_m p reserve 3)) <|
        .conj (.mem (deltaResult_m p reserve 2) (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken) <|
          .conj (.mem (deltaResult_m p reserve 1) (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken) <|
            .conj (.mem (deltaResult_m p reserve 0) (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken) <|
              .conj (pboundedFormula_m (deltaResult_m p reserve 3) (deltaOld_m p reserve 1).weaken.weaken.weaken.weaken
                (deltaOld_m p reserve 0).weaken.weaken.weaken.weaken (deltaResult_m p reserve 1) (deltaResult_m p reserve 2)) <|
                .conj (.mem (deltaResult_m p reserve 0) (deltaResult_m p reserve 1)) <|
                  .conj (.forallE <| .forallE <|
                    .imp (Formula.isTransitive (deltaQuerySlot_m p reserve 1)) <|
                    .conj (compiledPredicateQuery_m a true φ (fun i => (deltaSource_m p reserve i).weaken.weaken.weaken.weaken.weaken.weaken)
                      (deltaQuerySlot_m p reserve 5) (deltaOld_m p reserve 1).weaken.weaken.weaken.weaken.weaken.weaken
                      (deltaOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken.weaken (deltaQuerySlot_m p reserve 1)
                      (deltaQuerySlot_m p reserve 4) (deltaQuerySlot_m p reserve 3) (deltaQuerySlot_m p reserve 2) (deltaQuerySlot_m p reserve 0))
                      (compiledPredicateQuery_m a false φ (fun i => (deltaSource_m p reserve i).weaken.weaken.weaken.weaken.weaken.weaken)
                        (deltaQuerySlot_m p reserve 5) (deltaOld_m p reserve 1).weaken.weaken.weaken.weaken.weaken.weaken
                        (deltaOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken.weaken (deltaQuerySlot_m p reserve 1)
                        (deltaQuerySlot_m p reserve 4) (deltaQuerySlot_m p reserve 3) (deltaQuerySlot_m p reserve 2) (deltaQuerySlot_m p reserve 0))) <|
                    .forallE <| .forallE <|
                      .imp (.mem (deltaQuerySlot_m p reserve 1) (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken.weaken) <|
                        .imp (Formula.isTransitive (deltaQuerySlot_m p reserve 1)) <|
                        .imp (.mem (deltaQuerySlot_m p reserve 0) (deltaQuerySlot_m p reserve 1)) <|
                          .existsE <| .conj (.mem .newest (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken.weaken.weaken) <|
                            .conj (Formula.isFunctionSpace kpair_convention_l .newest
                              (deltaOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken.weaken.weaken (deltaQuerySlot_m p reserve 1).weaken)
                              (protectedAssignmentQuery_m a (fun i => (deltaSource_m p reserve i).weaken.weaken.weaken.weaken.weaken.weaken.weaken)
                                (deltaOld_m p reserve 2).weaken.weaken.weaken.weaken.weaken.weaken.weaken .newest
                                (deltaOld_m p reserve 0).weaken.weaken.weaken.weaken.weaken.weaken.weaken (deltaQuerySlot_m p reserve 1).weaken)

private def canonicalPredicateBody {d} (a : Fin d) (reserve : Nat) (p : Cp_test d) (φ : Formula 1 d) : Formula 1 0 :=
  .forallE <| .forallE <| .forallE <|
    .imp (KP.ord0_m (.bound 2)) <| .imp (jh_value_m (.bound 2) (.bound 1)) <|
      .imp (Formula.isOmega .newest) <| .imp (.mem .newest (.bound 1)) <|
        .existsE <| existsBlock_m (deltaSourceWidth_l p reserve) <|
          .conj (.mem (deltaOld_m p reserve 0) (deltaOld_m p reserve 2)) <|
            .conj (registerFrame_m (deltaSourceWidth_l p reserve) (deltaOld_m p reserve 0) (deltaSlot_m p reserve)) <|
              .conj (finConj_m (deltaSourceWidth_l p reserve) (fun i => .mem (deltaSlot_m p reserve i) (deltaOld_m p reserve 2)))
                (canonicalPredicateResult_m a reserve p φ)

theorem canonicalPredicateBody_closed_l {d} (a : Fin d) (reserve : Nat) (p : Cp_test d) (φ : Formula 1 d) (hc : φ.FreeClosed) :
    (canonicalPredicateBody a reserve p φ).FreeClosed := by
  simp -implicitDefEqProofs [canonicalPredicateBody,canonicalPredicateResult_m,deltaOld_m,deltaSlot_m,deltaSource_m,
    deltaResult_m,deltaQuerySlot_m,registerFrame_closed_l,compiledPredicateQuery_closed_l,protectedAssignmentQuery_closed_l,
    sourceTerm_m,Definitional.Formula.FreeClosed,hc]

def canonicalPredicateSentence {d} (a : Fin d) (reserve : Nat) (p : Cp_test d) (φ : Formula 1 d) (hc : φ.FreeClosed) : Sentence :=
  .ofFormula (canonicalPredicateBody a reserve p φ) (canonicalPredicateBody_closed_l a reserve p φ hc)

theorem canonicalPredicateCompilation_models {d} (a : Fin d) (reserve : Nat) (φ : Formula 1 d) (p : Cp_test d)
    (hp : PredicateDelta0 a φ) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p)
    (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) :
    M.SatisfiesSentence (canonicalPredicateSentence a reserve p φ hc) := by
  intro envFree
  change Formula.satisfies (⟨Fin.elim0,envFree⟩ : Env M 0) (canonicalPredicateBody a reserve p φ)
  simp only [canonicalPredicateBody,canonicalPredicateResult_m,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    KP.ord0_sat_l (ZF.modelsKP hZF),jh_value_sat_l,Formula.satisfies_isOmega_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,existsBlock_sat_l,Formula.satisfies_conj_iff,Formula.satisfies_isTransitive_iff,
    registerFrame_sat_l hZF.1,finConj_sat_l,pboundedFormula_sat_l (ZF.modelsKP hZF),
    compiledPredicateQuery_sat_l (ZF.modelsKP hZF),protectedAssignmentQuery_sat_l hZF.1,
    Formula.satisfies_isFunctionSpace_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest,deltaOld_m,deltaSlot_m,deltaSource_m,
    deltaResult_m,deltaQuerySlot_m,oldTerm_eval_l,sourceTerm_eval_l]
  intro α C ω hα hC hω hωC
  obtain ⟨n,slots,U,G,K,r,result⟩ := jh_canonicalPredicate_compile_l hZF a reserve φ p hp hc parsed hα hC hω hωC
  refine ⟨n,slots,result.arity_mem,result.frame,result.slots_mem,U,G,K,r,result.container_mem,result.container_transitive,
    result.program_mem,result.length_mem,result.root_mem,result.valid,result.root_bound,?_,?_⟩
  · intro X f hx
    constructor
    · intro σ fn corr
      exact (result.correct X f (⟨σ,envFree⟩ : Env M d) hx fn corr).1
    · intro σ fn corr
      exact ((result.correct X f (⟨σ,envFree⟩ : Env M d) hx fn corr).2).trans
        (Formula.satisfies_neg_iff (⟨σ,envFree⟩ : Env M d) φ).symm
  · intro X default hXC hx inhabited
    obtain ⟨E,hEC,full,all⟩ := result.realizes X default hXC hx inhabited
    refine ⟨E,hEC,full,fun σ values => ?_⟩
    obtain ⟨f,hfE,hfC,fn,corr,_⟩ := all (⟨σ,envFree⟩ : Env M d) values
    exact ⟨f,hfE,hfC,fn,corr⟩

theorem canonicalPredicateCompilation_derives {d} (a : Fin d) (reserve : Nat) (φ : Formula 1 d) (p : Cp_test d)
    (hp : PredicateDelta0 a φ) (hc : φ.FreeClosed) (parsed : cp_parse_l φ = some p) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (canonicalPredicateSentence a reserve p φ hc) :=
  YesMetaZFC.SetTheory.InnerModel.FiniteTruth.ProjectBridge.derives_of_models ZF.Axiom.extensionality
    (fun M hM => canonicalPredicateCompilation_models a reserve φ p hp hc parsed M hM)

/-- 原解析器确定的全谓词有界模板编译句子，不从 Prop 选择语法数据。 -/
def predicateCompilationSentence {d} (a : Fin d) (reserve : Nat) (φ : Formula 1 d)
    (hp : PredicateDelta0 a φ) (hc : φ.FreeClosed) : Sentence :=
  canonicalPredicateSentence a reserve (parsedSourceTest_l φ hp.delta0_l hc) φ hc

/-- 每个原 PredicateDelta0 闭合模板的共享代码、两极性与普通值实现均在原 ZF 核中可推导。 -/
theorem predicateCompilation_derives {d} (a : Fin d) (reserve : Nat) (φ : Formula 1 d)
    (hp : PredicateDelta0 a φ) (hc : φ.FreeClosed) :
    YesMetaZFC.SetTheory.Definitional.Project.Derives ZF (predicateCompilationSentence a reserve φ hp hc) :=
  canonicalPredicateCompilation_derives a reserve φ (parsedSourceTest_l φ hp.delta0_l hc) hp hc
    (parsedSourceTest_some_l φ hp.delta0_l hc)

end YesMetaZFC.SetTheory.InnerModel.FiniteTruth.Jensen
